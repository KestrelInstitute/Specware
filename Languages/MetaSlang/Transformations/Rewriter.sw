(* Rewrite rule control *)

MetaSlangRewriter qualifying spec 
 import /Library/Legacy/DataStructures/LazyList
 import DeModRewriteRules, Simplify, Interpreter
 
 type Context = HigherOrderMatching.Context

 type TermPredicate = MSTerm * MSTerm -> Bool

 op traceRewriting : Nat 
 def traceRewriting = 0

 def mkVar = HigherOrderMatching.mkVar     

%%
%% Application of set of rewrite rules
%%

(*
	applyRewrites: 
	Application of rewrites to subterm.
%	matchEquality: 
%	Directly try to match left and right hand side of
%	an equality using the matcher.
*)

 op applyRewrites : 
    Context * List RewriteRule * SubstC 
       -> List Var * MSTerm 
	   -> LazyList (MSTerm * (SubstC * RewriteRule * List Var * List RewriteRule))

 op applyRewrite(context: Context, rule: RewriteRule, subst: SubstC, term: MSTerm): List SubstC = 
   let lhs = rule.lhs in
   filter (fn subst -> completeMatch(lhs,subst))
     (matchPairsTop(context,subst,stackFromList [(lhs,term,None)])) % !! Fix None

 def applyRewrites(context,rules,subst) (boundVars,term) = 
     let context = setBound(context,boundVars) in
     mapEach 
       (fn (first,rule,rest) -> 
          let substs = applyRewrite(context,rule,subst,term) in
          if empty? substs
	    then emptyList
          else
            let rule1 = freshRule (context,rule) in
            let rules = rest ++ first ++ [rule1] in
            fromList
	      (map (fn s -> (dereferenceAll s (renameBoundVars(rule.rhs,boundVars)),
                             (s,rule,boundVars,rules)))
                 substs)) 
       rules

 op orderRules(rls: List RewriteRule): List RewriteRule =
   if true   % length rls < 2
     then rls
   else
   let (simpleRules, condRules) =
       %% foldl is arbitrary
       foldl (fn ((simpleRules, condRules), rl) ->
                if some? rl.condition
                  then (simpleRules, Cons(rl, condRules))
                  else (Cons(rl, simpleRules), condRules))
         ([],[]) rls
   in
    simpleRules ++ condRules

 op optimizeSuccessList(results: List(MSTerm * (SubstC * RewriteRule * List Var * Demod RewriteRule)))
      : List(MSTerm * (SubstC * RewriteRule * List Var * Demod RewriteRule)) =
   %% Prefer unconditional match if result is the same -- happens with subtypes and type parameters
%    let opt_num = if length results > 1 then
%                   let (t1,(s1,rule1,_,_))::_ = results in
%                   (foldl (fn ((opt_num,t2,s2,rule2), (t1,(s1,rule1,_,_))) ->
%                            if equalTerm?(t1,t2) && s2.3 ~= [] && s1.3 = []
%                              then (opt_num + 1, t1, s1, rule1)
%                              else (opt_num, t1, s1, rule1))
%                     (0, t1, s1, rule1) (tl results)).1
%                  else 0 in
%    let _ = if length results > 1 then writeLine("Succ: "^toString(length results)^" results. Opt: "^toString opt_num) else () in
   let new_results =
       if length results < 2 then results
         else
         let (t1,(s1,rule1,_,_))::_ = results in
         (foldl (fn ((new_results,tr,sr,ruler), ri as (ti,(si,rulei,_,_))) ->
                   if equalTerm?(ti,tr)
                     then
                       if equalList?(sr.3,si.3,equalTerm?)
                         then (new_results,tr,sr,ruler)
                         else if sr.3 ~= [] && si.3 = []
                         then   % let _ = writeLine("Optimize "^rule1.name) in
%                            let _ = if length new_results > 1 then (writeLine(printTerm ti);
%                                                                    List.app (fn t -> writeLine("  "^printTerm t)) (si.3);
%                                                                    writeLine(printTerm (hd results).1);
%                                                                    List.app (fn t -> writeLine("  "^printTerm t)) ((hd results).2.1.3)) else () in
                           (butLast new_results ++ [ri], ti, si, rulei)
                         else (new_results ++ [ri], ti, si, rulei)
                     else (new_results ++ [ri], ti, si, rulei))
            ([head results], t1, s1, rule1) (tail results)).1
   in
   %let _ = if length new_results < length results then writeLine(toString (length new_results)) else () in
   if length new_results < length results
     then optimizeSuccessList new_results
     else new_results

 op useStandardSimplify?: Bool = true
 op debugApplyRewrites?:  Bool = false

 op applyDemodRewrites(context: Context, subst: SubstC, standardSimplify?: Bool)
                      (boundVars: List Var, term: MSTerm, demod: Demod RewriteRule)
                      : LazyList(MSTerm * (SubstC * RewriteRule * List Var * Demod RewriteRule))  = 
%     let _ = writeLine("Rewriting:\n"^printTerm term) in
%     let _ = writeLine("with rules:") in
%     let _ = app printRule (listRules demod) in
   let context = setBound(context,boundVars)  in
   let spc     = context.spc                  in
   let rules = orderRules(Demod.getRules(demod,term)) in
   (mapFlat 
      (fn rule ->
          let _ = if debugApplyRewrites? then
                   (%writeLine("boundVars: "^anyToString boundVars);
                    printRule rule;
                    if some? rule.trans_fn
                      then writeLine("Applying to "^printTerm term)
                    else writeLine("Matching "^printTerm rule.lhs^" against\n"^printTerm term))
                   else ()
          in
          case rule.trans_fn of
            | Some f ->
              (case f term of
               | Some new_term ->
                 (if debugApplyRewrites? then writeLine("Metarule succeeded:\n"^printTerm new_term)
                    else ();
                  unit(new_term, (subst, rule, boundVars, demod)))
               | None -> Nil)
            | None ->
          let substs = applyRewrite(context,rule,subst,term) in
          let _ = if debugApplyRewrites? then
                    if substs = [] then writeLine("Match failed.\n")
                      else (writeLine("Match succeeded."); app printSubst substs)
                  else ()
          in
          fromList
            (optimizeSuccessList
               (mapPartial (fn s ->
                              let rhs = renameBoundVars(rule.rhs,boundVars) in
                              %% Temporary fix to avoid identity transformations early
                              %% The dereferenceAll will be done later as well,
                              %% This is also necessary for foldSubPatterns
                              let result = dereferenceAll s rhs in
                              let result = renameBound result in
                              if equalTerm?(term, result)
                                then None
                              else Some(result,(s,rule,boundVars,demod)))
                  substs))) 
      rules)
   @@ (fn () -> if standardSimplify? && useStandardSimplify?
                  then standardSimplify spc (term,subst,boundVars,demod)
                  else Nil)

(*
 op substRule : RewriteRule = 
     { 
	name     = "Subst",
        rule_spec = 
	freeVars = [],
	tyVars = [],
	condition = None,
	lhs   = mkVar(1,TyVar("''a",noPos)),
	rhs   = mkVar(2,TyVar("''a",noPos)),
        trans_fn = None
     } 
*)

 op evalRule : RewriteRule = 
     { 
	name     = "Eval",
        rule_spec = Eval,
	freeVars = [],
	tyVars = [],
	condition = None,
	lhs   = mkVar(1,TyVar("''a",noPos)),
	rhs   = mkVar(2,TyVar("''a",noPos)),
        trans_fn = None
     } 

 op ssRule(s: String): RewriteRule =
   evalRule << {name = s}

 op evalRule?(rl: RewriteRule): Bool =
   rl.tyVars = [] && rl.lhs = evalRule.lhs && rl.rhs = evalRule.rhs

 op baseSpecTerm?(term: MSTerm): Bool =
   ~(existsSubTerm (fn t -> case t of
                              | Fun(Op(Qualified(qual,_),_),_,_) ->
                                qual nin? evalQualifiers
                              | _ -> false)
       term)

 op pushFunctionsIn?: Bool = true
 op evalGroundTerms?: Bool = true

 op standardSimplify (spc: Spec) (term: MSTerm, subst: SubstC, boundVars: List Var, demod: Demod RewriteRule)
    :  LazyList(MSTerm * (SubstC * RewriteRule * List Var * Demod RewriteRule)) =
   %let _ = (writeLine "ss:"; printSubst subst) in
   let (simp?, term) = if evalGroundTerms?
                         then
                           let new_term = reduceTerm (term, spc) in
                           if equalTermStruct?(new_term, term)
                             then (false, term)
                           else % let _ = writeLine(printTerm term ^"\n-->\n"^printTerm new_term^"\n") in
                             (true, new_term)
                       else (false, term)
   in
   if simp? then unit(term, (subst,evalRule,boundVars,demod))
   else
   case tryEvalOne spc term of
     | Some eTerm ->
       % let _ = writeLine("EvalOne:\n"^printTerm term^"\nTo:\n"^printTerm eTerm) in
       unit (eTerm, (subst,ssRule "Eval1",boundVars,demod))
     | None ->
   case term of
     %% case foo x of ... | foo y -> f y | ... --> f x
     | Apply(Lambda(rules, _), N, a) ->
       (case patternMatchRules(rules,N)
          of None -> Nil
           | Some (sub,M) -> unit (substitute(M,sub), (subst,ssRule "reduceCase",boundVars,demod)))
     %% {id1 = x.id1, ..., idn = x.idn} --> x
     | Record((id1,Apply(Fun(Project id2,_,_), tm, _)) :: r_flds, _)
         | id1 = id2
             &&
             (let tm_ty = inferType(spc, tm) in
              let term_ty = inferType(spc, term) in
                (equivType? spc (tm_ty, term_ty)
                   || equivType? spc (stripSubtypes (spc, tm_ty), term_ty))
              && forall? (fn (i1,t1) ->
                            case t1 of
                              | Apply(Fun(Project i2,_,_), t, _) ->
                                i1 = i2 && equalTerm?(t, tm)
                              | _ -> false)
                  r_flds)
         -> unit (tm, (subst,ssRule "RecordId",boundVars,demod))
     | Apply(Fun(Embedded id1,_,_), Apply(Fun(Embed(id2,_),_,_),_,_),_) ->
       unit (mkBool(id1 = id2), (subst,ssRule "reduceEmbed",boundVars,demod))
     | Apply(Fun(Equals,s,_), Record([(_,M1),(l2,M2)],_),_) ->
       (if equalTerm?(M1,M2)
          then unit(trueTerm, (subst,ssRule "Eval=",boundVars,demod))
        else
        case isFlexVar? M1 of
          | Some n | ~(hasFlexRef? M2)->
            unit(trueTerm, (updateSubst(subst,n,M2), ssRule "Subst", boundVars, demod))
          | _ -> Nil)
     | _ -> Nil
%   if ~pushFunctionsIn? then Nil
%    else
%    case term of
%      | Apply(f, IfThenElse(b,x,y,a2),a1) ->
%        unit (IfThenElse(b,Apply(f,x,a1),Apply(f,y,a1),a2), (subst,evalRule,demod))
%      | Apply(f, Let(bds,lt,a2),a1) -> 
%        unit (Let(bds,Apply(f,lt,a1),a2), (subst,evalRule,demod))
% %% Moved to rewriteTerm
% %      | Apply(f, Apply(Lambda(binds,a3),case_tm,a2),a1) ->
% %        unit (Apply(Lambda(map (fn (p,c,bod) -> (p,c,Apply(f,bod,a1))) binds, a3),
% %                    case_tm,a2),
% %              (subst,evalRule,demod))
%      | _ -> Nil

 %% Whether a function can be pushed inside Let, If, Case
 op pushable?(f: MSTerm): Bool =
   case f of
     | Fun(And, _, _) -> false
     | Fun _ -> true
     | Var _ -> true
     | Apply _ -> true
     | Lambda _ -> true
     | _ -> false

  op addPatternRestriction(context: Context, pat: MSPattern, rules: Demod RewriteRule)
    : Demod RewriteRule =
   case pat of
     | VarPat(v as (_,ty), _) ->
       (let ty = unfoldBase(context.spc,ty) in
          case ty of
            %% Redundant with subtype rules introduced in Script.sw
            | Subtype(_,p,_) ->
              (let pred = case p of
                           | Fun(Op(qid, _),_,_) ->
                             (case findTheOp(context.spc, qid) of
                                | Some info ->
                                  if definedOpInfo? info
                                    then firstOpDefInnerTerm info
                                  else p
                                | None -> p)
                           | _ -> p
               in
               let condn = simplifiedApply(pred, mkVar v, context.spc) in
               let condn = reduceSubTerms (condn,context.spc) in
               addDemodRules(assertRules(context, condn, "Subtype", Context, Either), rules))
            | _ -> rules)
     | RecordPat(fields, _ ) ->
       foldl (fn (rules, (_,p)) -> addPatternRestriction(context, p, rules)) rules fields
     | RestrictedPat(p,condn,_) ->
       addPatternRestriction(context, p,
                             addDemodRules(assertRules(context,condn,"Restriction",Context,Either), rules))
     | EmbedPat(_, Some p, _, _) -> addPatternRestriction(context, p, rules)
     | AliasPat(_, p, _)    -> addPatternRestriction(context, p, rules)
     | QuotientPat(p, _, _) -> addPatternRestriction(context, p, rules)
     | TypedPat(p, _, _)    -> addPatternRestriction(context, p, rules)
     | _ -> rules

 op useUnfoldLetStrategy?: Bool = true

 op substFromBinds(binds: List(MSPattern * MSTerm)): VarSubst =
   foldl (fn (sbst, (p, be)) ->
                 case (p, be) of
                   | (VarPat(v,_), _) -> (v, be) :: sbst
                   | (RecordPat(pat_prs, _), Record(tm_prs, _)) ->
                     substFromBinds(zip(map (project 2) pat_prs, map (project 2) tm_prs)) ++ sbst
                   | (EmbedPat(id1, Some p, _, _), Apply(Fun(Embed(id2, true), _, _), tm, _)) | id1 = id2 ->
                     substFromBinds([(p, tm)]) ++ sbst
                   | _ -> sbst)
     []
     binds
 
 op unFoldSimpleLet(binds: List(MSPattern * MSTerm), M: MSTerm)
    : MSTerm =
    let v_subst = substFromBinds binds in
    if binds = [] || v_subst = [] || ~useUnfoldLetStrategy?
      then M
      else substitute(M,v_subst)

 op reFoldLetVars(binds: List(MSPattern * MSTerm), M: MSTerm, b: Position)
    : MSTerm =
   let v_subst = substFromBinds binds in
   if binds = [] || v_subst = [] || ~useUnfoldLetStrategy?
      then Let(binds,M,b)
      else
        %% Variable capture unlikely because of substitute in unFoldSimpleLet
        let M1 = mapTerm (reverseSubst v_subst, id, id) M in
        if equalTerm?(M, M1)
          then M
        else
          let fvs = freeVars M1 in
          Let(filter (fn (p,_) ->
                        exists? (fn v -> inVars?(v,fvs)) (patVars p))
                binds,
              M1, b)

 op maybePushIfBack(tr_if: MSTerm, f: MSTerm, Ns: MSTerms, i: Nat): MSTerm =
   case tr_if of
     | IfThenElse(p, Apply(f1, q, _), Apply(f2, r, _), pos) ->
       let qn = termToList q in
       let rn = termToList r in
       if equalTerm?(f, f1)
          && equalTerm?(f, f2)
          && forall? (fn j -> i = j || (equalTerm?(Ns@j, qn@j)
                                        && equalTerm?(Ns@j, rn@j)))
               (tabulate(length Ns, id))
         then mkAppl(f, replaceNth(i, Ns, IfThenElse(p, qn@i, rn@i, pos)))
         else tr_if
     | _ -> tr_if

op maybePushLetBack(tr_let: MSTerm, f: MSTerm, Ns: MSTerms, i: Nat): MSTerm =
   case tr_let of
     | Let(bds, Apply(f1, q, a), pos) ->
       let qn = termToList q in
       if equalTerm?(f, f1)
          && forall? (fn j -> i = j || (equalTerm?(Ns@j, qn@j)))
               (tabulate(length Ns, id))
         then mkAppl(f, replaceNth(i, Ns, Let(bds, qn@i, pos)))
         else tr_let
     | _ -> tr_let

op maybePushCaseBack(tr_case: MSTerm, f: MSTerm, Ns: MSTerms, i: Nat): MSTerm =
   case tr_case of
     | Apply(Lambda(binds,b3), case_tm, b2) ->
       if forall? (fn (p,c,bod) ->
                     case bod of
                       | Apply(f1, q, a) ->
                         let qn = termToList q in
                         equalTerm?(f, f1)
                         && forall? (fn j -> i = j || (equalTerm?(Ns@j, qn@j)))
                              (tabulate(length Ns, id))
                       | _ -> false)
            binds
         then mkAppl(f, replaceNth(i, Ns,
                                   Apply(Lambda(map (fn (p,c,Apply(f1, q, a)) ->
                                                       let qn = termToList q in
                                                       (p,c,qn@i))
                                                  binds, b3),
                                         case_tm, b2)))
         else tr_case
     | _ -> tr_case

 op persistentFlexVarStartNum: Nat = 1000   % Greater than largest of variables in a rule
 op persistentFlexVar?(t: MSTerm): Bool =
   case isFlexVar? t of
     | Some n -> n >= persistentFlexVarStartNum
     | None -> false

 op renumberFlexVars(term: MSTerm, flexNumIncrement: Nat): MSTerm =
   mapTerm (fn t ->
            case t of
              | Apply(Fun(Op(Qualified (UnQualified,"%Flex"),x1),x2,x3),Fun(Nat n, x4,x5),x6)
                  | n < persistentFlexVarStartNum ->
                Apply(Fun(Op(Qualified (UnQualified,"%Flex"),x1),x2,x3),Fun(Nat (n + flexNumIncrement), x4,x5),
                      x6)               
              | _ -> t,
            id, id)
     term

 op removeLocalFlexVars(subst: SubstC, del_flexvarnums: List Nat): SubstC =
   let (typeSubst,termSubst,typeConds) = subst in
   let new_termsubst = NatMap.foldri (fn (i,v,result) ->
                                        if i >= persistentFlexVarStartNum && i nin? del_flexvarnums
                                          then NatMap.insert(result,i,v)
                                        else result)
                         NatMap.empty termSubst
   in
     (StringMap.empty,new_termsubst,[])

 op renameConditionFlexVars(rule: RewriteRule, term: MSTerm, subst: SubstC): RewriteRule * MSTerm * List Nat =
   case rule.condition of
     | None -> (rule, term, [])
     | Some condn ->
   let condn = dereferenceAll subst condn in
   let term  = dereferenceAll subst term in
   %let (typeSubst,termSubst,typeConds) = subst in
   let unBoundRefs = foldSubTerms (fn (t,result)  ->
                                    case isFlexVar? t of
                                      | Some n | n nin? result -> n::result
                                      | _ -> result)
                       [] condn
   in
   if unBoundRefs = []                    % No flex vars
     then (rule << {condition = Some(condn)}, term, [])
   else
   let maxFlexNum = foldl max 0 unBoundRefs in
   let flexNumIncrement = max(maxFlexNum, persistentFlexVarStartNum) in
   let rule1 = rule << {condition = Some(renumberFlexVars(condn, flexNumIncrement))} in
   let term1 = renumberFlexVars(term,   flexNumIncrement) in
   (rule1, term1, mapPartial (fn n -> if n < persistentFlexVarStartNum
                                       then Some(n + flexNumIncrement)
                                       else None)
                    unBoundRefs)

 (* Unnecessary as equality can be done as a built-in rule
     See spec builtInRewrites
 op matchEquality : 
    fa(rules) Context * rules * SubstC 
       -> List Var * Term * Term -> LazyList (SubstC * RewriteRule * rules)

 def equalityRule : RewriteRule = 
     { 
	name     = "=",
	freeVars = [(1,TyVar "''a")],
	tyVars = ["''a"],
	condition = None,
	lhs   = mkVar(1,TyVar "''a"),
	rhs   = mkVar(2,TyVar "''a")
     } 


% Disambiguate between HigerOrderMatchingMetaSlang and MetaSlang
 def mkVar = HigherOrderMatchingMetaSlang.mkVar     

 def matchEquality (context,rules,subst) (boundVars,M,N) = 
     let context = setBound(context,boundVars) in
     let substs = matchPairsTop(context,subst, stackFromList [(M,N)]) in
     fromList (List.map (fn s -> (s,equalityRule,rules)) substs)
 *)

%%
%% We will have to rename variables in used rewrite rules in order to 
%% use the triangular substitution to dereference terms (and not just apply
%% the obtained substitution directly)
%%  


(* An inner-most rewriting strategy

 Rewrite subterm using rewrite rules represented abstractly as a function
 returning a lazy list of terms and arbitrary other information.
 In its usage this information would consist of a substitution and  
 rewrite rule (with name and optional condition).
 
 Assumption: The rewriter does not attempt matching 
 directly upon meta variables. Directly true, 
 when term is always rigid.

*)

 type Rewriter a = List Var * MSTerm * Demod RewriteRule -> LazyList (MSTerm * a) 
 %type Matcher  a = List Var * Term * Term -> LazyList a
 type Strategy   = | Innermost | Outermost
 type RewriteInfo a = {strategy: Strategy, rewriter: Rewriter a, context: Context}

 op rewriteTerm    : [a] RewriteInfo a * List Var * MSTerm * Demod RewriteRule
                           -> LazyList (MSTerm * a)
 op rewriteSubTerm : [a] RewriteInfo a * List Var * MSTerm * Demod RewriteRule
                           -> LazyList (MSTerm * a)

 op [a] rewritePattern (solvers: RewriteInfo a, boundVars: List Var,
                        pat: MSPattern, rules: Demod RewriteRule)
          : LazyList(MSPattern * a) =
   case pat of
     | RestrictedPat(p,t,b) ->
       LazyList.map 
         (fn (t,a) -> (RestrictedPat(p,t,b),a)) 
         (rewriteTerm(solvers,boundVars ++ patternVars p,t,rules))
     | _ -> Nil

 def rewriteTerm (solvers as {strategy,rewriter,context},boundVars,term,rules) = 
     case strategy
       of Innermost -> 
          rewriteSubTerm(solvers,boundVars,term,rules) 
          @@
	  (fn () -> rewriter (boundVars,term,rules))
        | Outermost -> 
	  rewriter (boundVars,term,rules) 
	  @@
	  (fn () -> rewriteSubTerm(solvers,boundVars,term,rules))

 def rewriteSubTerm (solvers as {strategy,rewriter,context},boundVars,term,rules) = 
   case term of
     | Apply(M,N,b) ->
       let Ns = termToList N in
       (case findIndex (embed? IfThenElse) Ns  of
          | Some (i,if_tm) | pushFunctionsIn? && pushable? M ->
            (let IfThenElse(p,q,r,b1) = if_tm in
             let r_tm = IfThenElse(p,
                                   mkAppl(M,replaceNth(i, Ns, q)),
                                   mkAppl(M,replaceNth(i, Ns, r)), b)
             in
             let tr_tms = rewriteTerm(solvers,boundVars,r_tm,rules) in
             LazyList.map (fn (tr_tm, a) -> (maybePushIfBack(tr_tm, M, Ns, i), a))
               tr_tms)
          | _ ->
        case findIndex (embed? Let) Ns  of
          | Some (i,let_tm) | pushFunctionsIn? && pushable? M ->
            (let Let(bds,lt_body,a2) = let_tm in
             let r_tm = Let(bds, mkAppl(M,replaceNth(i, Ns, lt_body)),a2) in
             let tr_tms = rewriteTerm(solvers,boundVars,r_tm,rules) in
             LazyList.map (fn (tr_tm, a) -> (maybePushLetBack(tr_tm, M, Ns, i), a))
               tr_tms)
          | _ ->
        case findIndex caseExpr? Ns  of
          | Some (i,case_tm) | pushFunctionsIn? && pushable? M ->
            (let Apply(Lambda(binds,b3), case_tm, b2) = case_tm in
             let r_tm = Apply(Lambda(map (fn (p,c,bod) ->
                                            (p,c,mkAppl(M,replaceNth(i, Ns, bod))))
                                       binds, b3),
                              case_tm, b2)
             in
             let tr_tms = rewriteTerm(solvers,boundVars,r_tm,rules) in
             LazyList.map (fn (tr_tm, a) -> (maybePushCaseBack(tr_tm, M, Ns, i), a))
               tr_tms)
          | _ ->
        case M of
          | Lambda(lrules,b1) ->
            %% Separate case so we can use the context of the pattern matching
            LazyList.map (fn (N,a) -> (Apply(M,N,b),a)) 
              (rewriteTerm(solvers,boundVars,N,rules))
            @@ (fn () ->
                  mapEach(fn (first,(pat,cond,M),rest) -> 
                      rewritePattern(solvers,boundVars,pat,rules)
                      >>= (fn (pat,a) -> unit(Apply(Lambda (first ++ [(pat,cond,M)] ++ rest,b1), N, b), a)))
                    lrules
            @@ (fn () ->
                mapEach 
                  (fn (first,(pat,cond,M),rest) ->
                     let rules = addPatternRestriction(context,pat,rules) in
                     let (M, rules, sbst) =
                         case patternToTerm pat of
                           | None -> (M, rules, [])
                           | Some pat_tm ->
                         case N of
                           | Var(nv,_) ->
                             let sbst = [(nv, pat_tm)] in
                             (substitute (M, sbst), rules, sbst)
                           | _ ->
                             let equal_term = mkEquality(inferType(context.spc, N), N, pat_tm) in
                             (M, addDemodRules(assertRules(context, equal_term, "case", Context, Either), rules), [])
                     in
                     rewriteTerm(solvers,(boundVars ++ patternVars pat), M, rules)
                     >>= (fn (M,a) ->
                            let M = invertSubst(M,sbst) in
                            unit(Apply(Lambda (first ++ [(pat,cond,M)] ++ rest,b1), N, b), a)))
                  lrules))
          | Fun(Op(Qualified(_,"mapFrom"),_),_,_)
              | (case Ns of [_,Lambda([_], _)] -> true | _ -> false) ->
            let [set_term, f as Lambda([(p,c,bod)],b1)] = Ns in 
            LazyList.map (fn (set_term,a) -> (mkAppl(M,[set_term,f]),a)) 
              (rewriteTerm(solvers,boundVars,set_term,rules))
            @@ (fn () -> 
                  LazyList.map (fn (bod,a) -> (mkAppl(M,[set_term, Lambda([(p,c,bod)],b1)]), a))
                  (rewriteTerm(solvers,boundVars ++ patternVars p,bod,
                               let Some v_tm = patternToTerm p in
                               let memb_assert = mkAppl(mkInfixOp(mkUnQualifiedId("in?"),
                                                                  Infix(Left,100),
                                                                  mkArrow(mkProduct[termType v_tm,
                                                                                    termType set_term],
                                                                          boolType)),
                                                        [v_tm,set_term])
                               in
                               addDemodRules(assertRules(context, memb_assert,
                                                         "mapFrom function", Context, Either),
                                             rules))))
          | _ ->
        LazyList.map (fn (N,a) -> (Apply(M,N,b),a)) 
          (rewriteTerm(solvers,boundVars,N,rules))
        @@ (fn () -> 
              LazyList.map (fn (M,a) -> (Apply(M,N,b),a)) 
                (rewriteTerm(solvers,boundVars,M,rules))))
     | Record(fields,b) -> 
       mapEach 
        (fn (first,(label,M),rest) -> 
            rewriteTerm(solvers,boundVars,M,rules) >>= 
            (fn (M,a) -> unit(Record(first ++ [(label,M)] ++ rest,b),a)))
        fields
     | Lambda(lrules,b) ->
       mapEach(fn (first,(pat,cond,M),rest) -> 
                 rewritePattern(solvers,boundVars,pat,rules)
                 >>= (fn (pat,a) -> unit(Lambda (first ++ [(pat,cond,M)] ++ rest,b),a)))
         lrules
       @@ (fn () ->
           mapEach 
             (fn (first,(pat,cond,M),rest) -> 
                let patvars = patternVars pat in
                let rules = addPatternRestriction(context,pat,rules) in
                rewriteTerm(solvers, boundVars ++ patternVars pat, M, rules)
                >>= (fn (M,a) -> unit(Lambda (first ++ [(pat,cond,M)] ++ rest,b),a)))
             lrules)
     | Let(binds,M,b) ->
        mapEach (fn (first,(pat,N),rest) ->
                   rewriteTerm(solvers,boundVars,N,rules) >>=
                   (fn (N,a) -> unit(Let(first ++ [(pat,N)] ++ rest,M,b),a)))
          binds
        @@ (fn () ->
             let let_vars = flatten (map (fn (pat, _) -> patternVars pat) binds) in
             let p_M = unFoldSimpleLet(binds,M) in
             LazyList.map (fn (r_M,a) -> (reFoldLetVars(binds,r_M,b),a))
               (rewriteTerm(solvers,boundVars ++ let_vars,p_M,rules)) )
     | LetRec(binds,M,b) ->
       let letrec_vars = map(fn (v, _) -> v) binds in
       let boundVars = boundVars ++ letrec_vars in
       mapEach (fn (first,(v,N),rest) ->
                  rewriteTerm(solvers,boundVars,N,rules) >>=
                  (fn (N,a) -> unit(LetRec(first ++ [(v,N)] ++ rest,M,b),a)))
         binds
       @@ (fn () ->
             LazyList.map (fn (M,a) -> (LetRec(binds,M,b),a)) 
               (rewriteTerm(solvers,boundVars,M,rules)))

%           let let_vars = map(fn (v, _) -> v) bind in
%           LazyList.map (fn (M,a) -> (Bind(qf,vars,M,b),a))
%		(rewriteTerm(solvers,boundVars ++ let_vars,M,rules))
     | Bind(qf,vars,M,b) -> 
       LazyList.map (fn (M,a) -> (Bind(qf,vars,M,b),a))
            (rewriteTerm(solvers,boundVars ++ vars,M,rules))
     | The (var,M,b) -> 
       LazyList.map (fn (M,a) -> (The(var,M,b),a))
            (rewriteTerm(solvers,boundVars ++ [var],M,rules))
     | IfThenElse(M,N,P,b) -> 
       LazyList.map 
            (fn (M,a) -> (IfThenElse(M,N,P,b),a)) 
            (rewriteTerm(solvers,boundVars,M,rules)) @@
       (fn () -> 
       LazyList.map 
            (fn (N,a) -> (IfThenElse(M,N,P,b),a)) 
            (rewriteTerm(solvers,boundVars,N,
                         addDemodRules(assertRules(context,M,"if then", Context, Either), rules)))) @@
       (fn () -> 
       LazyList.map 
            (fn (P,a) -> (IfThenElse(M,N,P,b),a)) 
            (rewriteTerm(solvers,boundVars,P,
                         addDemodRules(assertRules(context,negate M,"if else", Context, Either), rules))))
     | Seq(tms, b) ->
       mapEach 
         (fn (first,M,rest) -> 
            rewriteTerm(solvers,boundVars,M,rules) >>= 
            (fn (M,a) -> unit(Seq(first ++ [M] ++ rest,b),a)))
         tms
     | TypedTerm(M,s,b) ->
       LazyList.map (fn (M,a) -> (TypedTerm(M,s,b),a))
            (rewriteTerm(solvers,boundVars,M,rules))
     | Pi(tvs,M,b) ->
       LazyList.map (fn (M,a) -> (Pi(tvs,M,b),a))
            (rewriteTerm(solvers,boundVars,M,rules))
   %  | And(tms,b) ->
     | _ -> Nil

(* Trace utilities *)

 op printTerm: Nat * MSTerm -> String
 def printTerm (indent,term) = 
     let indent   = PrettyPrint.blanks indent in
     let context  = initialize(asciiPrinter,false) in 
     let argument = ([],Top) in
     let termPP   = ppTerm context argument term in
     let termPP   = PrettyPrint.prettysNone [PrettyPrint.string indent,termPP] in
     PrettyPrint.toString(PrettyPrint.format(100,termPP))

 op traceTerm : Context * MSTerm * SubstC -> ()
 def traceTerm(context,term,(* subst *)_) = 
     if traceRewriting > 1 then 
     % if context.trace then 
	 (writeLine(printTerm(3 + ! context.traceIndent,term));
	  ()
	  ) 
     else ()

 op traceRule(context:Context,rule:RewriteRule): () = 
     % if context.trace then
     if traceRewriting > 0 then 
	let depth = show(! context.traceDepth) in
	(toScreen (PrettyPrint.blanks (! context.traceIndent));
	 writeLine("=  { "^depth^": "^ rule.name^" }"))
     else ()

 (* Check condition of conditional rewrite rule *)

%%
%% Check that all variables in a term are bound by the substitution.
%%

 def completeMatch(term,subst:SubstC) =
     let S = subst.2 in
     let 
	 def loop(term:MSTerm):Bool = 
	     case term
	       of Fun(top,srt,_) -> true
	        | Var((id,srt), _)  -> true
	        | Let(decls,bdy,_) -> 
	          forall? (fn (_,M) -> loop M) decls && loop bdy
	        | LetRec(decls,bdy,_) -> 
	          forall? (fn (_,M) -> loop M) decls && loop bdy
	        | Record(row, _) -> 
	          forall? (fn (_,M) -> loop M) row
	        | IfThenElse(t1,t2,t3,_) -> loop t1 && loop t2 && loop t3
	        | Lambda(match,_) -> 
	          forall?  (fn (_,_,M) -> loop M) match
                | The(var,trm,_) -> loop trm
                | Bind(bnd,vars,trm,_) -> loop trm
	        | Apply(t1,t2,_) -> 
	          (case isFlexVar?(term) 
		     of Some n -> NatMap.inDomain(S,n) 
		      | None -> loop t1 && loop t2)
	        | Seq(terms,_) -> forall? loop terms
     in
     loop term

 op backwardChainMaxDepth: Nat = 10

 type History = List (RewriteRule * MSTerm * SubstC)

 op historyRepetition: History -> Bool
 def historyRepetition = 
     fn (_,term1,_)::(_,term2,_)::_ -> equalTerm?(term1,term2)
      | _ -> false

 op rewriteRecursive : 
    Context * List Var * RewriteRules * MSTerm * Nat -> LazyList (History)

 op rewriteRecursivePre : 
    Context * List Var * Demod RewriteRule * MSTerm * Nat -> LazyList (History)


%%
%% Apply unconditional rewrite rules using inner-most strategy.
%% Apply conditional rewrite rules using outer-most strategy.
%%

 def rewriteRecursive(context,boundVars,rules,term,maxDepth) = 
%      let rules = {unconditional = addDemodRules(rules.unconditional,Demod.empty),
% 		  conditional   = addDemodRules(rules.conditional,Demod.empty)}
     let rules = addDemodRules(rules.unconditional ++ rules.conditional,Demod.empty)
     in rewriteRecursivePre(context,boundVars,rules,term,maxDepth)

 op conditionResultLimit: Nat = 4

 def rewriteRecursivePre(context,boundVars,rules0,term,maxDepth) = 
   let	
      def rewritesToTrue(rules,term,boundVars,subst,history,backChain): Option SubstC =
          if trueTerm? term then Some subst
          else
	  let results = rewriteRec(rules,subst,term,freeVars term,history,backChain+1) in
          case LazyList.find_n (fn (rl,t,c_subst)::_ -> trueTerm? t || falseTerm? t || evalRule? rl
                               | [] -> false)
                 results
                 conditionResultLimit
	    of None -> None
	     | Some((rl,t,c_subst)::_) ->
               %% Substitutions, history and conditional rewrites need work
	       if trueTerm? t then Some c_subst else None

      def solveCondition(rules,rule,(typeSubst,termSubst,typeConds),prev_term,boundVars,history,backChain)
          : Option SubstC = 
        let subst = (typeSubst,termSubst,[])
        in
        let conds = case rule.condition of
                      | None -> typeConds
                      | Some cond -> Cons(cond, typeConds)
        in
	if conds = []
          then
	     (traceRule(context,rule);
	      Some subst)
        else if termIn?(prev_term, conds)   % Avoid subproblem same as original
          then (%writeLine("Found recursive subgoal: "^printTerm prev_term);
                None)
        else
	if backChain < backwardChainMaxDepth && completeMatch(rule.lhs,subst) then 
            let cond = foldr Utilities.mkAnd trueTerm conds in
            let cond = dereferenceAll subst cond in % redundant?
            let subst = removeLocalFlexVars(subst,[]) in
            let traceIndent = ! context.traceIndent in
	    let res = if traceRewriting > 0 then
                        (context.traceIndent := traceIndent + 3;
                         toScreen ("=  "^PrettyPrint.blanks traceIndent^"{ "); 
                         writeLine (show(! context.traceDepth)^" : "^rule.name);
                         %              printSubst subst;
                         context.traceDepth := 0;
                         rewritesToTrue(rules,cond,boundVars,subst,history,backChain))
                      else 
                        (context.traceDepth := 0;
                         rewritesToTrue(rules,cond,boundVars,subst,history,backChain))
            in
	    if traceRewriting > 0 then
	      (context.traceIndent := traceIndent;
	       writeLine ("   "^PrettyPrint.blanks traceIndent ^"}");
               %(case res of Some s -> printSubst s | _ -> ());
	       res)
	    else
	       res
	else None

      def rewriteRec(rules0,subst,term0,boundVars,history,backChain) =
	let _ = traceTerm(context,term0,subst)     in
	let traceDepth = ! context.traceDepth + 1 in
        if traceDepth > (if backChain = 0 then maxDepth else max(maxDepth, backwardChainMaxDepth))
          then unit history
        else
	let def rewrite(strategy,rules) =
%                 let _ = writeLine("Rules:") in
%                 let _ = app printRule (listRules rules) in
		rewriteTerm 
		  ({strategy = strategy,
		    rewriter = applyDemodRewrites(context,subst,maxDepth > 1 || backChain > 0),
		    context = context},
		   boundVars,term0,rules)     
	in
	if historyRepetition(history)
	    then unit (tail history)
	else
	% let rews = (rewrite(Innermost,unconditional) >>= 
	let rews = (rewrite(Outermost,rules0) >>= 
		    (fn (term,(subst,rule,boundVars,rules1)) ->  
			unit (term,(subst,rule,boundVars,rules1))) 
% 		    @@
% 		    (fn () -> 
% 		     rewrite(Outermost,conditional) >>= 
% 		     (fn (term,(subst,rule,boundVars,rules)) ->  
% 			unit (term,(subst,rule,boundVars,
% 				    {conditional   = conditional,
% 				     unconditional = unconditional}))))
                    )
	in
	case rews
	  of Nil -> unit history
	   | _ ->
	rews >>=
	(fn (term,(subst,rule,boundVars,rules1)) -> 
	    (context.traceDepth := traceDepth;
             let (rule,term,new_flexvarnums) = renameConditionFlexVars(rule,term,subst) in
	     case solveCondition(rules1,rule,subst,term0,boundVars,history,backChain+1)
	       of Some subst -> 
		 (context.traceDepth := traceDepth;
		  let term = dereferenceAll subst term in
		  let term = renameBound term in
                  let history = Cons((rule,term,subst),history) in
                  let subst = removeLocalFlexVars(subst,new_flexvarnums) in
		  let rec_results
                     = rewriteRec(rules0,subst,term,boundVars, history, backChain)
                   in
                   if rec_results = Nil
                     then unit history
                     else rec_results)
	       | None -> Nil
                     ))
   in
      %let term = dereferenceAll emptySubstitution term in
      rewriteRec(rules0,emptySubstitution,term,boundVars,[],0)

 op rewriteOnce : 
    Context * List Var * RewriteRules * MSTerm -> List MSTerm

%%
%% Apply unconditional rewrite rules using outer-most strategy
%%
 def rewriteOnce(context,boundVars,rules,term) = 
     let unconditional = Demod.addRules(List.map (fn rl -> (rl.lhs,rl)) 
						rules.unconditional,Demod.empty) in
     (* unused...
     let conditional   = Demod.addRules(List.map (fn rl -> (rl.lhs,rl)) 
						rules.conditional,Demod.empty)  in
     *)

%    let {unconditional,conditional} = rules in
     let subst = emptySubstitution in
     let term = dereferenceAll emptySubstitution term in
     let rews = rewriteTerm
		 ({strategy = Innermost,
		   rewriter = applyDemodRewrites(context,emptySubstitution,false),
		   context = context},
		  boundVars,term,unconditional)
     in
     let rews = LazyList.toList rews in
     List.map (fn (newTerm,(subst,rule,boundVars,rules)) -> 
		  dereferenceAll subst newTerm) rews

	  
end-spec

(*
Discussion

* This allows to use rewriting as abstract execution. 
      What about compiled forms? A la type based partial evaluation forms, or
      unboxing analysis?

      Code generation should generate code of the form
      (defun f (x) 
        (let ((x-unboxed (unbox x)))
             (if (boxed? x)
                 (box (cons :|Apply| AST-for-symbol-f x-unboxed))
	      (unboxed (standard-code-for-f x-unboxed)))))
* Implement the boxification as a Spec to Spec transformation that allows
      to reuse one code generator.
        type Box a = | Boxed Term | UnBoxed a
        op  boxifySpec : Spec -> Spec
        op  boxifyTerm : Term -> Term
        op  boxifyType : Type -> Type
            
        boxifyDef(def f = fn x -> body) = 
            def f = fn Boxed x -> Boxed('Apply(f,x)) | UnBoxed x -> boxifyTerm body

        boxifyTerm(Apply(f,g)) = 
            case f
              of Boxed f -> Boxed('Apply(f,'g))
               | Unboxed f -> 
            case g
              of Unboxed g -> Apply(f,g)
               | Boxed g -> Boxed('Apply(f,g))

* Extend partial evaluation/boxing format with calls to rewrite engine, or
      interleave these steps.
*)
