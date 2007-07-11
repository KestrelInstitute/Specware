Script qualifying
spec
  import Simplify, Rewriter, Interpreter

  op Isomorphism.makeIsoMorphism: Spec * QualifiedId * QualifiedId \_rightarrow Spec

  op [a] dummy: a

  type Context = RewriteRules.Context
  
  type Location =
    | Def QualifiedId

  type RuleSpec =
    | Unfold   QualifiedId
    | Fold     QualifiedId
    | LeftToRight QualifiedId
    | RightToLeft QualifiedId
    | AllDefs

  type Script =
    | At (List Location \_times Script)
    | Steps List Script
    | Simplify (List RuleSpec)
    | Apply (List RuleSpec)
    | SimpStandard
    | PartialEval
    | IsoMorphism(QualifiedId \_times QualifiedId \_times List RuleSpec)

 op mkAt(qid: QualifiedId, steps: List Script): Script = At([Def qid], mkSteps steps)
 op mkSteps(steps: List Script): Script = if length steps = 1 then hd steps else Steps steps
 op mkSimplify(steps: List RuleSpec): Script = Simplify(steps)
 op mkApply(rules: List RuleSpec): Script = Apply rules
 op mkSimpStandard(): Script = SimpStandard
 op mkPartialEval (): Script = PartialEval

 %% For convenience calling from lisp
 op mkFold(qid: QualifiedId): RuleSpec = Fold qid
 op mkUnfold(qid: QualifiedId): RuleSpec = Unfold qid
 op mkLeftToRight(qid: QualifiedId): RuleSpec = LeftToRight qid
 op mkRightToLeft(qid: QualifiedId): RuleSpec = RightToLeft qid
 op mkAllDefs(qid: QualifiedId): RuleSpec = AllDefs

 op ruleConstructor(id: String): QualifiedId -> RuleSpec =
   case id of
     | "fold" \_rightarrow mkFold
     | "f" \_rightarrow mkFold
     | "unfold" \_rightarrow mkUnfold
     | "uf" \_rightarrow mkUnfold
     | "lr" \_rightarrow mkLeftToRight
     | "lefttoright" \_rightarrow mkLeftToRight
     | "left-to-right" \_rightarrow mkLeftToRight
     | "rl" \_rightarrow mkRightToLeft
     | "righttoleft" \_rightarrow mkRightToLeft
     | "right-to-left" \_rightarrow mkRightToLeft
     | "alldefs" \_rightarrow mkAllDefs

 op printScript(scr: Script): () =
   toScreen(anyToString scr)

 %% From /Languages/SpecCalculus/Semantics/Evaluate/Prove.sw
 op claimNameMatch: QualifiedId \_times QualifiedId -> Boolean
 def claimNameMatch(cn, pn) =
   let Qualified(cq, cid) = cn in
   let Qualified(pq, pid) = pn in
   if cq = UnQualified
     then pid = cid
   else cq = pq & cid = pid

  op makeRule (context: Context, spc: Spec, rule: RuleSpec): List RewriteRule =
    case rule of
      | Unfold(qid as Qualified(q,nm)) \_rightarrow
        flatten (map (fn info ->
                        flatten (map (fn (Qualified(q,nm)) \_rightarrow defRule(context, q, nm, info))
                                   info.names))
                   (findAllOps(spc,qid)))
      | Fold(qid) \_rightarrow
        map (\_lambda rl \_rightarrow rl \_guillemotleft {lhs = rl.rhs, rhs = rl.lhs})
          (makeRule(context, spc, Unfold(qid)))
      | LeftToRight(qid) \_rightarrow
        foldr (\_lambda (p,r) \_rightarrow
               if claimNameMatch(qid,p.2)
                 then (axiomRules context p) ++ r
                 else r)
          [] (allProperties spc)
      | RightToLeft(qid) \_rightarrow
        map (\_lambda rl \_rightarrow rl \_guillemotleft {lhs = rl.rhs, rhs = rl.lhs})
          (makeRule(context, spc, LeftToRight(qid)))
      | AllDefs \_rightarrow
        foldriAQualifierMap
          (\_lambda (q,id,opinfo,val) ->
             (defRule (context,q,id,opinfo)) ++ val)
          [] spc.ops
        
  op rewriteDebug?: Boolean = false

  op rewriteDepth: Nat = 5
  op rewrite(term: MS.Term, context: Context, rules: List RewriteRule, maxDepth: Nat): MS.Term =
     let _ = if rewriteDebug? then
               (writeLine("Rewriting:\n"^printTerm term);
                app printRule rules)
               else ()
     in
     %let rules = map (etaExpand context) rules in   % Not sure if necessary
     %let rules = prioritizeRules rules in
     let rules = {unconditional=rules,
                  conditional=[]}
     in
     let def doTerm (count, trm) =
           %let _ = writeLine("doTerm "^toString count) in
           let lazy = rewriteRecursive (context,[],rules,trm,maxDepth) in
           case lazy of
             | Nil -> trm
             | Cons([],tl) -> trm
             | Cons((rule,trm,subst)::_,tl) ->
               if count > 0 then 
                 doTerm (count - 1, trm)
               else
                 trm
     in
     let result = % if maxDepth = 1 then hd(rewriteOnce(context,[],rules,term))
                  % else
                  doTerm(rewriteDepth, term)
     in
     let _ = if rewriteDebug? then writeLine("Result:\n"^printTerm result) else () in
     result

  op makeRules (context: Context, spc: Spec, rules: List RuleSpec): List RewriteRule =
    foldr (\_lambda (rl,rules) \_rightarrow makeRule(context, spc, rl) ++ rules) [] rules

  op maxRewrites: Nat = 25

  op interpretTerm(spc: Spec, script: Script, term: MS.Term): MS.Term =
    case script of
      | Steps steps \_rightarrow
        foldl (\_lambda (s,t) \_rightarrow
               interpretTerm(spc,s,t))
          term steps
      | SimpStandard \_rightarrow simplify spc term
      | PartialEval \_rightarrow
        evalFullyReducibleSubTerms (term, spc)
      | Simplify(rules) \_rightarrow
        let context = makeContext spc in
        let rules = makeRules (context, spc, rules) in
        rewrite(term,context,rules,maxRewrites)
      | Apply(rules) \_rightarrow
        let context = makeContext spc in
        let rules = makeRules (context, spc, rules) in
        rewrite(term,context,rules,1)

  op setOpInfo(spc: Spec, qid: QualifiedId, opinfo: OpInfo): Spec =
    let Qualified(q,id) = qid in
    spc << {ops = insertAQualifierMap(spc.ops,q,id,opinfo)}

  op getOpDef(spc: Spec, qid: QualifiedId): Option MS.Term =
    case findTheOp(spc,qid) of
      | None \_rightarrow None
      | Some opinfo \_rightarrow
        let (tvs, srt, tm) = unpackTerm opinfo.dfn in
        Some tm

  op interpretSpec(spc: Spec, script: Script): Spec =
    case script of
      | Steps steps \_rightarrow
        foldl (\_lambda (stp,sp) \_rightarrow
               interpretSpec(spc,stp))
          spc steps
      | At(locs, scr) \_rightarrow
        foldl (fn (Def qid, spc) \_rightarrow
               case findTheOp(spc,qid) of
                 | None \_rightarrow (warn("Can't find op "^anyToString qid);
                            spc)
                 | Some opinfo \_rightarrow
                   let (tvs, srt, tm) = unpackTerm opinfo.dfn in
                   let newtm = interpretTerm(spc, scr, tm) in
                   let newdfn = maybePiTerm(tvs, SortedTerm (newtm, srt, termAnn opinfo.dfn)) in
                   setOpInfo(spc,qid,opinfo << {dfn = newdfn}))
          spc locs
      | IsoMorphism(iso,inv_iso,_) \_rightarrow
        makeIsoMorphism(spc, iso, inv_iso)

  op interpret(spc: Spec, script: Script): Spec =
    interpretSpec(spc, script)
  

(*
    let rules = mergeDemodRules [rewriteRules ruleModeSpec, rewriteRules modeSpec] in
    % let rules = rewriteRules ruleModeSpec in
    let
      def doTerm count trm =
        let lazy = rewriteRecursivePre ((context ruleModeSpec) withSpec (specOf ruleModeSpec),[],rules,trm) in
        case lazy of
          | Nil -> trm
          | Cons([],tl) -> trm
          | Cons((rule,trm,subst)::_,tl) ->
              if (count > 0) then 
                doTerm (count - 1) trm
              else
                trm

      def doOp info =
        let ref = Op.refOf info in
        if member? (variables modeSpec, ref) then
          case opInfoDefs info of
            | [] -> info  % fail "empty term schemes"
            | [dfn] ->
	      let (tvs, srt, tm) = unpackTerm dfn in
              let tm = doTerm 20 tm in
	      info << {dfn = maybePiTerm (tvs, SortedTerm (tm, srt, termAnn dfn))}
            | _ -> fail "multiple term schemes"
        else
          info

      def doClaim claim =
        let ref = refOf claim in
        if member? (invariants modeSpec, ref) then
          case claim of
            | (Axiom,name,typeVars,term) -> (Axiom,name,typeVars,doTerm 20 term) 
            | claim -> claim
        else
          claim in
    let spc = specOf modeSpec in
    let newSpec:Spec.Spec = {
        sorts = spc.sorts,
        ops = mapAQualifierMap doOp spc.ops,
        properties = map doClaim spc.properties,
        importInfo = spc.importInfo
      } in
    return (modeSpec withSpec newSpec)

*)


endspec
