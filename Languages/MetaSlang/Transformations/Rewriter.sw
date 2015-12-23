(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Rewrite rule control *)

MetaSlangRewriter qualifying spec 
 import /Library/Legacy/DataStructures/LazyList
 import ../AbstractSyntax/PathTerm
 import DeModRewriteRules, Simplify, Interpreter, MetaTransform, SubtypeElimination
 import ../Specs/Proof
 
 type Context = HigherOrderMatching.Context

 def mkVar = HigherOrderMatching.mkVar


%%
%% Application of set of rewrite rules
%%

 % This type represents the auxiliary info returned as a result of
 % applying a rewrite to an input term. It includes:
 %
 % * The term resulting from rewriting the input term;
 %
 % * The substitution resulting from matching the lhs of the rewrite
 %    rule against the input term;
 %
 % * The rewrite rule applied to the input term;
 %
 % * The path in the output term where the rule was applied; and
 %
 % * The set of rewrite rules being used.
 type RRResultInfo =  SubstC * RewriteRule * Path * MSVars * Demod RewriteRule

 % The result of rewriting, which is the output term plus RRResultInfo
 type RRResult = MSTerm * RRResultInfo

 % Flag for debugging
 op debugRRPaths : Bool = false

 op mapRRResultInfo (tr_fn: MSTerm -> MSTerm)
                    (((typeSubst, termSubst, tms), rule, path, boundVars, rules): RRResultInfo): RRResultInfo =
   let new_termSubst = NatMap.map tr_fn termSubst in
   let new_rule = rule << {lhs = tr_fn rule.lhs,
                           opt_proof = mapOption (mapProof "mapRRResultInfo" (tr_fn, id, id)) rule.opt_proof}
   in
   ((typeSubst, new_termSubst, tms), new_rule, path, boundVars, rules)

 % Get the path from a RRResultInfo
 op infoPath ((_, _, path, _, _): RRResultInfo) : Path = path

 % Return the difference between the path in a RRResultInfo and suffix
 op infoPathDifference ((_, _, path, _, _): RRResultInfo,
                        suffix: Path) : Option Path =
   pathDifference (path, suffix)

 % Return the reversal of infoPathDifference; useful for matching on
 % the "next steps" in a path
 op infoPathDifferenceRev (info: RRResultInfo, suffix: Path) : Option Path =
   case infoPathDifference (info, suffix) of
     | None -> None
     | Some p -> Some (reverse p)

 % Apply a function to the difference of the path in a RRResultInfo
 % and a suffix
 op mapInfoPathDifference (f: Path->Path, info: RRResultInfo,
                           suffix: Path, caller: String) : RRResultInfo =
   case infoPathDifference (info, suffix) of
     | None -> (warn (caller ^ ": unexpected path in rewrite result: "
                        ^ printPath (infoPath info)
                        ^ " with suffix path: "
                        ^ printPath suffix); info)
     | Some prefix ->
       let (subst, rule, path, boundVars, rules) = info in
       (subst, rule, (f prefix) ++ suffix, boundVars, rules)

 % Replace the difference between the path in a RRResultInfo and a
 % suffix
 op replaceInfoPathDifference (p: Path, info: RRResultInfo,
                               suffix: Path, caller: String) : RRResultInfo =
   mapInfoPathDifference ((fn _ -> p), info, suffix, caller)

 % Append p to the difference between the path in a RRResultInfo and a
 % suffix
 op appendToInfoPathDifference (p: Path, info: RRResultInfo,
                                suffix: Path, caller: String) : RRResultInfo =
   mapInfoPathDifference ((fn path ->
                             let _ =
                               if debugRRPaths then
                                 writeLine
                                 ("appendToInfoPathDifference: appending "
                                    ^ printPath p ^ " to " ^ printPath path
                                    ^ " in path " ^ printPath (infoPath info))
                               else ()
                             in
                             path++p),
                          info, suffix, caller)


(*
	applyRewrites: 
	Application of rewrites to subterm.
%	matchEquality: 
%	Directly try to match left and right hand side of
%	an equality using the matcher.
*)

 type ResultInfo0 = SubstC * RewriteRule * MSVars * List RewriteRule

 op applyRewrite(context: Context, rule: RewriteRule, subst: SubstC, term: MSTerm): List SubstC = 
   let lhs = rule.lhs in
   filter (fn subst -> completeMatch(lhs,subst))
     (matchPairsTop(context,subst,stackFromList [(lhs,term,None)])) % !! Fix None

 % FIXME: this function appears to never be used...
 op applyRewrites(context: Context, rules: List RewriteRule, subst: SubstC) (boundVars: MSVars, term: MSTerm)
     : LazyList (MSTerm * ResultInfo0) = 
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
            (map (fn s -> (dereferenceAllAsSubst s rule.rhs boundVars,
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

 op optimizeSuccessList(results: List RRResult) : List RRResult =
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
         let (t1,(s1,rule1,_,_,_))::_ = results in
         (foldl (fn ((new_results,tr,sr,ruler), ri as (ti,(si,rulei,_,_,_))) ->
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
   % let _ = if length new_results = length results then
   %          (writeLine "Opt Success:"; let (t1,(s1,_,_,_))::_ = results in (writeLine(printTerm t1); printSubst s1))
   %         else () in
   if length new_results < length results
     then optimizeSuccessList new_results
     else new_results

 % Search for a rewrite rule that applies to term, returning a lazy
 % list of possible results.
 op applyDemodRewrites(context: Context, standardSimplify?: Bool)
                      (boundVars: MSVars, term: MSTerm, path: Path, demod: Demod RewriteRule)
                      : LazyList RRResult  = 
%     let _ = writeLine("Rewriting:\n"^printTerm term) in
%     let _ = writeLine("with rules:") in
%     let _ = app printRule (listRules demod) in
   let context = setBound(context,boundVars)  in
   let spc     = context.spc                  in
   % First, use the term indexing in Demod to look up a list of
   % potential rules that could apply to term at path. (NOTE:
   % orderRules is currently the identity.)
   let rules = orderRules(Demod.getRules(demod,term)) in
   % Now iterate over all the possibilities, creating a LazyList of
   % the results that actually apply.
   (mapFlat 
      (fn rule ->
         % Print some debugging info
          let _ = if context.debugApplyRewrites? then
                   (%writeLine("boundVars: "^anyToString boundVars);
                    printRule rule;
                    if some? rule.trans_fn
                      then writeLine("Applying to "^printTerm term)
                    else writeLine("Matching "^printTerm rule.lhs^" against\n"^printTerm term))
                   else ()
          in
          % For meta-rules, which are signified by a non-empty
          % trans_fn, apply the trans_fn to get the result.
          case rule.trans_fn of
            | Some f ->
              (let result = apply(f, replaceSpecTermArgs(metaRuleATV rule.rule_spec, spc, term)) in
               case extractMSTerm result of
                 | Some new_term ->
                   (if context.debugApplyRewrites? then writeLine("Metarule succeeded:\n"^printTerm new_term)
                     else ();
                    let fake_rule =
                      % Build a new "fake" rule corresponding to the result
                      % of the meta-rule
                      {name      = rule.name,
                       rule_spec = rule.rule_spec,
                       opt_proof = extractProof result,
                       sym_proof = false,
                       lhs       = term,
                       rhs       = new_term,
                       condition = None,
                       freeVars  = [],	
                       tyVars    = [],
                       trans_fn   = rule.trans_fn}
                    in
                    unit(new_term, (emptySubstitution, fake_rule, path, boundVars, demod)))
                 | None -> Nil)
            | None ->
          % Otherwise, call applyRewrite to try to apply the rule,
          % returning the list of matches between the lhs and term
          let substs = applyRewrite(context,rule,emptySubstitution,term) in
          % More debugging
          let _ = if context.debugApplyRewrites? then
                    if substs = [] then writeLine("Match failed.\n")
                      else (writeLine("Match succeeded."); app printSubst substs)
                  else ()
          in
          fromList
            (optimizeSuccessList
               (mapPartial (fn (s as (typeSubst, termSubst, condns)) ->
                              % For each match s with the lhs of rule,
                              % substitute s into the rhs and return
                              % the result, making sure we don't apply
                              % an identity transformaion.
                              %
                              % FIXME: what do these comments mean?
                              %% Temporary fix to avoid identity transformations early
                              %% The dereferenceAll will be done later as well,
                              %% This is also necessary for foldSubPatterns
                              let result = dereferenceAllAsSubst s rule.rhs boundVars in
                              let s = case rule.condition of
                                        | None -> s
                                        | Some condn ->
                                          (typeSubst, termSubst,
                                           (dereferenceAllAsSubst s condn boundVars)
                                             :: condns)
                              in
                              if equalTerm?(term, result)
                                then None
                              else Some(result,(s,rule,path,boundVars,demod)))
                  substs))) 
      rules)
   @@ (fn () -> if standardSimplify? && context.useStandardSimplify?
                  then standardSimplify (context, spc) (term,path,boundVars,demod)
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

 op mkSimpRule (name:String, ty: MSType, lhs:MSTerm, rhs:MSTerm) : RewriteRule =
   {
    name     = name,
    rule_spec = Eval,
    opt_proof =
      Some (prove_equalWithTactic (AutoTactic [], lhs,rhs,ty)),
    sym_proof = false,
    freeVars = [],
    tyVars = [],
    condition = None,
    lhs   = lhs,
    rhs   = rhs,
    trans_fn = None
    }

 def mkEvalRule (ty,lhs,rhs) = mkSimpRule ("Eval",ty,lhs,rhs)
 op evalRule?(rl: RewriteRule): Bool = rl.rule_spec = Eval

 op baseSpecTerm?(term: MSTerm): Bool =
   ~(existsSubTerm (fn t -> case t of
                              | Fun(Op(Qualified(qual,_),_),_,_) ->
                                qual nin? evalQualifiers
                              | _ -> false)
       term)

 op pushFunctionsIn?: Bool = true
 op evalGroundTerms?: Bool = true

 op standardSimplify (context: Context,spc: Spec) (term: MSTerm, path:Path, boundVars: MSVars, demod: Demod RewriteRule)
    :  LazyList(RRResult) =
   %let _ = (writeLine "ss:"; printSubst subst) in
   let (simp?, new_term) =
     if evalGroundTerms?
       then
         let new_term = reduceTerm (term, spc) in
         if equalTermStruct?(new_term, term)
           then (false, term)
         else
           (true, new_term)
     else (false, term)
   in
   if simp? then
     unit(new_term, (emptySubstitution,mkEvalRule(inferType(spc, term),term,new_term),
                     path,boundVars,demod))
   else
   case tryEvalOne spc term of
     | Some eTerm ->
       % let _ = writeLine("EvalOne:\n"^printTerm term^"\nTo:\n"^printTerm eTerm) in
       unit (eTerm, (emptySubstitution,mkSimpRule ("Eval1", inferType (spc,term), term, eTerm),
                     path, boundVars, demod))
     | None ->
   case term of
     %% case foo x of ... | foo y -> f y | ... --> f x
     | Apply(Lambda(rules, _), N, a) ->
       (case patternMatchRules(rules,N)
          of None -> Nil
           | Some (sub,M) ->
             let out_term = substitute(M,sub) in
             % let _ = writeLine("EvalOne pat:\n"^printTerm term^"\nTo:\n"^printTerm out_term) in
             unit (out_term, (emptySubstitution,
                              mkSimpRule ("reduceCase",inferType(spc, term),term,out_term),
                              path, boundVars, demod)))
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
         -> unit (tm, (emptySubstitution,
                       mkSimpRule ("RecordId",inferType(spc, term),term,tm),
                       path,boundVars,demod))
     %% let p1 = (let p2 = e2 in e1) in e3 --> let p2 = e2 in let p1 = e2 in e3
     | Let([(p1, Let(bds2, e1, a2))], e3, a1) ->
       let out_term = Let(bds2, Let([(p1, e1)], e3, a1), a2) in
       unit (out_term,
             (emptySubstitution,
              mkSimpRule ("normalizeEmbeddedLets", inferType(spc, term), term, out_term),
              path, boundVars, demod))
     | Apply(Fun(Embedded id1,_,_), Apply(Fun(Embed(id2,_),_,_),_,_),_) ->
       let out_term = mkBool(id1 = id2) in
       unit (out_term, (emptySubstitution,mkSimpRule ("reduceEmbed", inferType(spc, term), term, out_term),
                        path,boundVars,demod))
     | Apply(Fun(Equals,s,_), Record([(_,M1),(l2,M2)],_),_) ->
       (if equalTermAlpha?(M1,M2)
          then unit(trueTerm, (emptySubstitution,
                               mkSimpRule ("Eval=", inferType(spc, term), term, trueTerm),
                               path,boundVars,demod))
        else
        case flexVarNum M1 of
          | Some n | ~(hasFlexRef? M2) || context.allowUnboundVars? ->
            unit(trueTerm,
                 (updateSubst(emptySubstitution,n,M2),
                  mkSimpRule ("Subst", inferType(spc, term), term, trueTerm),
                  path, boundVars, demod))
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
               addDemodRules(assertRules(context, condn, "Subtype", Context, Either, None, freeTyVarsInTerm condn),
                             rules))
            | _ -> rules)
     | RecordPat(fields, _ ) ->
       foldl (fn (rules, (_,p)) -> addPatternRestriction(context, p, rules)) rules fields
     | RestrictedPat(p,condn,_) ->
       addPatternRestriction(context, p,
                             addDemodRules(assertRules(context,condn,"Restriction",Context,Either,None,freeTyVarsInTerm condn),
                                           rules))
     | EmbedPat(_, Some p, _, _) -> addPatternRestriction(context, p, rules)
     | AliasPat(_, p, _)    -> addPatternRestriction(context, p, rules)
     | QuotientPat(p, _, _, _) -> addPatternRestriction(context, p, rules)
     | TypedPat(p, _, _)    -> addPatternRestriction(context, p, rules)
     | _ -> rules

 op useUnfoldLetStrategy?: Bool = true

 op substFromBinds(binds: List(MSPattern * MSTerm)): MSVarSubst =
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

 % Unfold a let-expression, by substituting the bindings into the body
 op unFoldSimpleLet(binds: List(MSPattern * MSTerm), M: MSTerm)
    : MSTerm =
    let v_subst = substFromBinds binds in
    if binds = [] || v_subst = [] || ~useUnfoldLetStrategy?
      then M
      else substitute(M,v_subst)

 % Let-expressions are rewritten by first unfolding them (i.e.,
 % performing beta-reduction), and then performing rewriting. If the
 % rewrite did not require the let to be unfolded, then it is
 % re-folded by this function.
 op reFoldLetVars(binds: List(MSPattern * MSTerm), let_path: Path,
                  res as (M, info): RRResult, b: Position)
    : RRResult =
   let v_subst = substFromBinds binds in
   if binds = [] || v_subst = [] || ~useUnfoldLetStrategy?
      then (Let(binds,M,b),
            appendToInfoPathDifference([length binds], info, let_path,
                                       "reFoldLetVars"))
      else
        %% Variable capture unlikely because of substitute in unFoldSimpleLet
        let rev_subst = reverseSubst v_subst in
        let M1 = mapTerm (rev_subst, id, id) M in
        if equalTerm?(M, M1)
          then res
        else
          let info = mapRRResultInfo (mapTerm (rev_subst, id, id)) info in
          let fvs = freeVars M1 in
          let new_binds =
            filter (fn (p,_) ->
                      exists? (fn v -> inVars?(v,fvs)) (patVars p))
              binds
          in
          % let _ = writeLine("reFoldLetVars:\n"^printTerm M^"  -->  \n"^printTerm(Let(new_binds, M1, b))) in
          (Let(new_binds, M1, b),
           appendToInfoPathDifference([length new_binds], info, let_path, "reFoldLetVars"))

% If a function was pushed inside an if-expression in its argument to
% apply a rewrite, test whether that pushing was necessary for the
% rewrite, and if not undo the pushing
op maybePushIfBack(res as (tr_if, info): RRResult, orig_path: Path,
                   f: MSTerm, Ns: MSTerms, i: Nat): Option RRResult =
  if equalTerm?(tr_if, mkAppl(f, Ns)) then None
  else
  Some(case tr_if of
         | IfThenElse(p, Apply(f1, q, _), Apply(f2, r, _), pos) ->
           let def unpush_if rr_in_else_branch f_Ns_num_opt new_prefix_rev =
             let qn = termToList q in
             let rn = termToList r in
             let new_f = if rr_in_else_branch then f2 else f1 in
             let new_Ns = if rr_in_else_branch then rn else qn in
             % README: don't need to do these tests, because if there had
             % been some further pushing in the then- or else- branches
             % they wouldn't be Applys!
             %
             % % test that only one term in f::Ns has changed; otherwise,
             % % there might have been some further pushing done on f1(q) or
             % % f2(r) that we need to keep
             % if length new_Ns = length Ns &&
             %   (forall?
             %      (fn j -> Some j = f_ns_num_opt
             %         || (f::Ns)@j = (new_f::new_Ns)@j)
             %      (tabulate(1+length Ns, id)))
             % then
               (mkAppl(new_f, replaceNth(i, new_Ns, IfThenElse (p, qn@i, rn@i, pos))),
                replaceInfoPathDifference(reverse new_prefix_rev, info, orig_path,
                                          "maybePushIfBack"))
             % else res
           in
           % README: fun_pathElem is the immediate subterm number of
           % Apply(f,Ns) that picks out f
           let fun_pathElem = 0 in
           let arg_pathElem = 1 in
           let path_to_unpushed_if =
             arg_pathElem :: (if length Ns = 1 then [] else [i])
           in
           (case infoPathDifferenceRev (info, orig_path) of
              % The rewrite happened at the top of the then- or else-branch,
              % or at the top of the whole expression, and so required f to be
              % pushed inside the if
              | Some [] -> res
              | Some [1] -> res
              | Some [2] -> res
              | Some (path as 0::_) ->
                % Rewrite happened in the condition of the if
                unpush_if false None (path_to_unpushed_if++path)
              | Some (1::elem::p_f) | elem = fun_pathElem ->
                % Rewrite happened in the function part of the then-branch;
                % try to unpush with the new, rewritten function
                unpush_if false (Some 0) (fun_pathElem::p_f)
              | Some (2::elem::p_f) | elem = fun_pathElem ->
                % Rewrite happened in the function part of the else-branch;
                % try to unpush with the new, rewritten function
                unpush_if true (Some 0) (fun_pathElem::p_f)
              | Some (1::elem::p_branch) | elem = arg_pathElem && length Ns = 1 ->
                % Rewrite happened in the then-branch and there are no other
                % args to f
                unpush_if false (Some 1) (path_to_unpushed_if++(1::p_branch))
              | Some (2::elem::p_branch) | elem = arg_pathElem && length Ns = 1 ->
                % Rewrite happened in the else-branch and there are no other
                % args to f
                unpush_if true (Some 1) (path_to_unpushed_if++(2::p_branch))
              | Some (1::elem::j::p_branch) | elem = arg_pathElem && j=i ->
                % Rewrite happened in the then-branch of the original
                % if-expression
                unpush_if false (Some (j+1)) (path_to_unpushed_if++(1::p_branch))
              | Some (2::elem::j::p_branch) | elem = arg_pathElem && j=i ->
                % Rewrite happened in the else-branch of the original
                % if-expression
                unpush_if true (Some (j+1)) (path_to_unpushed_if++(2::p_branch))
              | Some (1::elem::j::p_branch) | elem = arg_pathElem && j~=i ->
                % Rewrite happened in the then-branch in one of the arguments in
                % Ns that was not the original if-expression
                unpush_if false (Some (j+1)) [1,j]
              | Some (2::elem::j::p_branch) | elem = arg_pathElem && j~=i ->
                % Rewrite happened in the else-branch in one of the arguments in
                % Ns that was not the original if-expression
                unpush_if false (Some (j+1)) [1,j]
              | _ ->
                warn ("maybePushIfBack: unexpected path " ^ printPath (infoPath info)); res)
         | _ -> res)

% If a function was pushed inside a let-expression in its argument to
% apply a rewrite, test whether that pushing was necessary for the
% rewrite, and if not undo the pushing
op maybePushLetBack(res as (tr_let, info): RRResult, orig_path: Path,
                    f: MSTerm, Ns: MSTerms, i: Nat): RRResult =
  case tr_let of
    | Let(bds, Apply(new_f, q, a), pos) ->
      let def unpush_let f_Ns_num_opt new_prefix_rev =
        let new_Ns = termToList q in
        % README: don't need to do these tests, because if there had
        % been some further pushing in the body wouldn't be an Apply!
        %
        % test that only one term in f::Ns has changed; otherwise,
        % there might have been some further pushing done on f1(q)
        % that we need to keep
        % if (forall?
        %       (fn j -> Some j = f_ns_num_opt
        %          || (f::Ns)@j = (new_f::new_Ns)@j)
        %       (tabulate(1+length Ns, id)))
        % then
          (mkAppl(new_f, replaceNth(i, new_Ns, Let(bds, new_Ns@i, pos))),
           replaceInfoPathDifference(reverse new_prefix_rev, info, orig_path,
                                     "maybePushLetBack"))
        % else res
      in
      let num_bindings = length bds in
      % README: fun_pathElem is the immediate subterm number of
      % Apply(f,Ns) that picks out f
      let fun_pathElem = 0 in
      let arg_pathElem = 1 in
      let path_to_unpushed_let =
        arg_pathElem :: (if length Ns = 1 then [] else [i])
      in
      (case infoPathDifferenceRev (info, orig_path) of
         % The rewrite happened at the top of the let body or of the
         % whole expression, and so required f to be pushed into the let
         | Some [] -> res
         | Some [1] -> res
         | Some (path as b_num::_) | b_num < num_bindings ->
           % Rewrite happened in one of the bindings
           unpush_let None (path_to_unpushed_let++path)
         | Some (b_num::elem::p_f) | elem = fun_pathElem && b_num = num_bindings ->
           % Rewrite happened in the function
           unpush_let (Some 0) (elem::p_f)
         | Some (b_num::elem::p_arg) | elem = arg_pathElem && b_num = num_bindings && length Ns = 1 ->
           % Rewrite happened in the body of the only argument to f
           unpush_let (Some 0) (path_to_unpushed_let++p_arg)
         | Some (b_num::elem::j::p_arg) | elem = arg_pathElem && b_num = num_bindings && j = i ->
           % Rewrite happened in the original body of the let-expression
           unpush_let (Some (j+1)) (path_to_unpushed_let++(num_bindings::p_arg))
         | Some (b_num::elem::j::p_arg) | elem = arg_pathElem && b_num = num_bindings && j = i ->
           % Rewrite happened in some other of the original args to f
           unpush_let (Some (j+1)) [1,j]
         | _ ->
           warn ("maybePushLetBack: unexpected path " ^ printPath (infoPath info)); res)
     | _ -> res

% If a function was pushed inside a case-expression in its argument to
% apply a rewrite, test whether that pushing was necessary for the
% rewrite, and if not undo the pushing
op maybePushCaseBack(res as (tr_case, info): RRResult, orig_path: Path,
                     f: MSTerm, Ns: MSTerms, i: Nat): RRResult =
   % let _ = writeLine ("maybePushCaseBack: tr_case = (" ^ printTerm tr_case
   %                      ^ "), infoPath = " ^ printPath (infoPath info)
   %                      ^ ", orig_path = " ^ printPath orig_path
   %                      ^ ", f = (" ^ printTerm f ^ ")") in
  case tr_case of
    | Apply(Lambda(branches,pos3), case_tm, pos2) ->
      let def unpush_case branch_num_opt new_prefix_rev =
        let new_f_Ns_opt =
          case branch_num_opt of
            | Some n ->
              (case branches@n of
                 | (p, c, Apply (f1, q, pos1)) ->
                   % The rewrite happened in a strict subterm of branch n (the strict
                   % subterm part is determined with the path-matching magic below). If
                   % the branch is still an application, it must be the (optionally
                   % rewritten) function applied to the (optionally rewritten) args, so we
                   % extract these back out of the nth branch
                   Some (f1, termToList q)
                 | _ ->
                   % This case means that: a rewrite happened in branch n but branch n no
                   % longer looks like an application; this can only happen if we pushed f
                   % into some other if/let/case that we didn't unpush it back out of, so
                   % we can't unpush it out of the current case either
                   None)
            | _ ->
              % Rewriting happened somewhere other than a branch, so we keep f and Ns
              Some (f, Ns)
        in
        case new_f_Ns_opt of
          | None ->
            % The previous case determined not to unpush, so just return res
            res
          | Some (new_f, new_Ns) ->
            (mkAppl(new_f,
                    replaceNth(i, new_Ns,
                               Apply(Lambda(map (fn (p,c,Apply(f1, q, a)) ->
                                                   let qn = termToList q in
                                                   (p,c,qn@i))
                                              branches, pos3),
                                     case_tm, pos2))),
             replaceInfoPathDifference(reverse new_prefix_rev, info, orig_path,
                                       "maybePushCaseBack"))
      in
      % README: fun_pathElem is the immediate subterm number of
      % Apply(f,Ns) that picks out f
      let fun_pathElem = 0 in
      let arg_pathElem = 1 in
      % Similar to the above, but for Apply(Lambda(...),case_tm)
      let casefun_pathElem = 0 in
      let casearg_pathElem = 1 in
      % The reverse of the path to the case expression (of the form
      % Apply(Lambda(...)),scrut) after un-pushing it
      let path_to_unpushed_case =
        arg_pathElem :: (if length Ns = 1 then [] else [i])
      in
      let def branch_num case_pos = lambdaPosBranchNumber (branches, case_pos) in
      (case infoPathDifferenceRev (info, orig_path) of
         % The rewrite happened at the top of one of the branches, the lambda
         % itself, or of the whole expression, and so required f to be pushed
         | Some [] -> res
         | Some [elem] | elem = casefun_pathElem -> res
         | Some [elem,case_pos] | elem = casefun_pathElem && some? (branch_num case_pos) -> res

           % Rewrite happened in the scrutinee
         | Some (path as elem::_) | elem = casearg_pathElem ->
           unpush_case None (path_to_unpushed_case ++ path)

           % Rewrite happened in a pattern guard; NOTE: if this match fails, the
           % remaining cases can assume some? (lambdaPosBranchNumber case_pos)
         | Some (path as elem::case_pos::_)
         | elem = casefun_pathElem && branch_num case_pos = None ->
           unpush_case None (path_to_unpushed_case ++ path)

           % Rewrite happened in the function in a branch
         | Some (elem::case_pos::elem_f::p_f)
         | elem = casefun_pathElem && elem_f = fun_pathElem ->
           unpush_case (branch_num case_pos) (elem_f::p_f)

           % Rewrite happened in a branch of the original
           % case-expression, which was the only arg to f
         | Some (elem::case_pos::elem_arg::p_arg)
         | elem = casefun_pathElem && elem_arg = arg_pathElem && length Ns = 1 ->
           unpush_case (branch_num case_pos) (path_to_unpushed_case ++ (case_pos::p_arg))

           % Rewrite happened in a branch of original case-expression, with multiple args to f
         | Some (elem::case_pos::elem_arg::arg_num::p_arg)
         | elem = casefun_pathElem && elem_arg = arg_pathElem && arg_num = i ->
           unpush_case (branch_num case_pos) (path_to_unpushed_case ++ (case_pos::p_arg))

           % Rewrite happened in one of the non-case-expression original args to f
         | Some (elem::case_pos::elem_arg::arg_num::p_arg)
         | elem = casefun_pathElem && elem_arg = arg_pathElem && arg_num ~= i ->
           unpush_case (branch_num case_pos) (arg_pathElem::arg_num::p_arg)

         | _ ->
           warn ("maybePushCaseBack: unexpected path " ^ printPath (infoPath info)); res)
    | _ -> res


 % The maximum number, exclusive, allowed for a flex variable in a
 % rewrite rule
 op maxRuleFlexVar : Nat = 5000

 % Return a SubstC that "freshens up" all the flex variables in term,
 % so that they do not clash with any rules. We cheat by just adding
 % maxRuleFlexVar to the numbers of all flex vars in term.
 op fresheningSubstFor (context: Context, term : MSTerm) : SubstC =
   mkFresheningSubstC
     (foldSubTerms (fn (M,result) ->
                      case flexVarNum M of
                        | Some n | n < maxRuleFlexVar ->
                          (case findLeftmost (fn (m,_,_) -> m=n) result of
                             | Some (_, _, T) | equalType? (T, termType M) ->
                               result
                             | Some (_, _, T) ->
                               (warn ("fresheningSubstFor: occurrences of flex var with different types!");
                                result)
                             | None ->
                               let num = ! context.counter in
                               let num = max(maxRuleFlexVar, num) in
                               (context.counter := num + 1;
                                (n, num, termType M) :: result))
                        | _ -> result)
        [] term)

 op sanitizeFlexVars (context: Context, term : MSTerm): MSTerm =
   dereferenceAll (fresheningSubstFor(context, term)) term

 (* FIXME HERE: remove the following *)
 (*
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
 *)

 (* Unnecessary as equality can be done as a built-in rule
     See spec builtInRewrites
 op matchEquality : 
    fa(rules) Context * rules * SubstC 
       -> MSVars * Term * Term -> LazyList (SubstC * RewriteRule * rules)

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

 type Rewriter = MSVars * MSTerm * Path * Demod RewriteRule -> LazyList RRResult 
 %type Matcher  a = MSVars * Term * Term -> LazyList a
 type Strategy   = | Innermost | Outermost
 type RewriteInfo = {strategy: Strategy, rewriter: Rewriter, context: Context}

 op rewriteTerm    : RewriteInfo * MSVars * MSTerm * Path * Demod RewriteRule
                           -> LazyList RRResult
 op rewriteSubTerm : RewriteInfo * MSVars * MSTerm * Path * Demod RewriteRule
                           -> LazyList RRResult

 op rewritePattern (solvers: RewriteInfo, boundVars: MSVars,
                    pat: MSPattern, path: Path, rules: Demod RewriteRule,
                    prevCases: MSMatch, ign?: Bool)
          : LazyList(MSPattern * RRResultInfo) =
   case pat of
     | RestrictedPat(p,t,b) | ~ign? ->
       LazyList.map 
         (fn (t,a) -> (RestrictedPat(p,t,b),a)) 
         (rewriteTerm(solvers,boundVars ++ patternVars p,t,
                      (countMatchSubTerms prevCases)::path,rules))
     | _ -> Nil
 
 % Whether a function can be pushed inside Let, If, of Case
 op pushable?(f: MSTerm): Bool =
   case f of
     | Fun(And, _, _) -> false
     | Fun _ -> true
     | Var _ -> true
     | Apply _ -> true
     | Lambda _ -> true
     | _ -> false

 % Whether an argument is a Let, If, or Case
 % FIXME: should be updated to ask if any term in
 % termToList N is an if, let, or case expression
 op pushTerm?(tm: MSTerm) (top?: Bool): Bool =
   case tm of
     | IfThenElse _ -> true
     | Let _ -> true
     | Record(prs as ("1",_) :: _, _) | top? -> exists? (fn (_, tp_tm) -> pushTerm? tp_tm false) prs
     | _ -> caseExpr? tm

 % Outer wrapper for term rewriting, which handles two things: it sets
 % up the order of rewriting (i.e., innermost vs outermost), and it
 % also tries to perform some commuting conversions to make rewriting
 % easier. These commuting conversions take the form of commuting any
 % function application, whose argument is a let, if, or case
 % expression, so that the function application is moved inside the
 % let, if, or case expression. If this does not result in any
 % rewrites being applied, then the commuting conversion is then
 % undone.
 def rewriteTerm (solvers as {strategy,rewriter,context},boundVars,term,path,rules) =
   % let _ = writeLine("rewriteTerm with path "^printPath path^" and term ("^printTerm term^")") in
   % let _ = case context.topTerm of
   %           | Some(top_tm) | ~(equalTerm?(term, fromPathTerm(top_tm, path)))
   %                           && ~(embed? Record term) && ~(embed? Fun term) ->
   %             writeLine("Path error: "^anyToString path^"\n"^printTerm term^"\n"^printTerm(fromPathTerm(top_tm, path)))
   %           | _ -> ()
   % in
   case term of
     | Apply(M,N,b) | pushFunctionsIn? && pushTerm? N true && pushable? M ->
       let Ns = termToList N in
       (case findIndex (embed? IfThenElse) Ns  of
          | Some (i,if_tm) ->
            (let IfThenElse(p,q,r,b1) = if_tm in
             let r_tm = IfThenElse(p,
                                   mkAppl(M,replaceNth(i, Ns, q)),
                                   mkAppl(M,replaceNth(i, Ns, r)), b)
             in
             let tr_tms = rewriteTerm(solvers,boundVars,r_tm,path,rules) in
             LazyList.mapPartial (fn res -> maybePushIfBack(res, path, M, Ns, i))
               tr_tms)
          | _ ->
        case findIndex (embed? Let) Ns  of
          | Some (i,let_tm) ->
            (let fvs = foldl (fn (fvs, s_tm) -> if s_tm = let_tm then fvs else insertVars(freeVars s_tm, fvs))
                            [] Ns in
             let Let(bds, lt_body, a2) = renameBoundVars(let_tm, fvs) in
             let r_tm = Let(bds, mkAppl(M,replaceNth(i, Ns, lt_body)),a2) in
             let tr_tms = rewriteTerm(solvers,boundVars,r_tm,path,rules) in
             LazyList.map (fn res -> maybePushLetBack(res, path, M, Ns, i))
               tr_tms)
          | _ ->
        case findIndex caseExpr? Ns  of
          | Some (i,case_tm) ->
            (let fvs = foldl (fn (fvs, s_tm) -> if s_tm = case_tm then fvs else insertVars(freeVars s_tm, fvs))
                            [] Ns in
             let Apply(Lambda(binds,b3), case_tm, b2) = renameBoundVars(case_tm, fvs) in
             let r_tm = Apply(Lambda(map (fn (p,c,bod) ->
                                            (p,c,mkAppl(M,replaceNth(i, Ns, bod))))
                                       binds, b3),
                              case_tm, b2)
             in
             % let _ = writeLine("pushcase:\n"^printTerm r_tm) in
             let tr_tms = rewriteTerm(solvers,boundVars,r_tm,path,rules) in
             LazyList.map (fn res -> maybePushCaseBack(res, path, M, Ns, i))
               tr_tms)
          | None -> (writeLine("pushFunctionsIn? failed:\n"^printTerm term); Nil) )
     | _ ->
   case strategy
     of Innermost -> 
        rewriteSubTerm(solvers,boundVars,term,path,rules) 
        @@
        (fn () -> rewriter (boundVars,term,path,rules))
      | Outermost -> 
        rewriter (boundVars,term,path,rules) 
        @@
        (fn () -> rewriteSubTerm(solvers,boundVars,term,path,rules))

 def rewriteSubTerm (solvers as {strategy,rewriter,context},boundVars,term,path,rules) = 
   case term of
     | Apply(M,N,b) ->
       let Ns = termToList N in
       (case M of
          % This means we are rewriting an application of a lambda to an argument
          | Lambda(lrules,b1) ->
            % First case rewrites the argument, N
            LazyList.map (fn (N,a) -> (Apply(M,N,b),a)) 
              (rewriteTerm(solvers,boundVars,N,1::path,rules))
            % These cases rewrite the patterns
            @@ (fn () ->
                  mapEach(fn (first,(pat,cond,body),rest) -> 
                      rewritePattern(solvers,boundVars,pat,0::path,rules,first,false)
                      >>= (fn (pat,a) -> unit(Apply(Lambda (first ++ [(pat,cond,body)] ++ rest,b1), N, b), a)))
                    lrules
            % Rewrite each body with the additional assumption that the pattern
            % match with the argument has succeeded in that body
            @@ (fn () ->
                mapEach 
                  (fn (first,(pat,cond,body),rest) ->
                     let rules = addPatternRestriction(context,pat,rules) in
                     let (body, rules, sbst) =
                         case patternToTerm pat of
                           | None -> (body, rules, [])
                           | Some pat_tm ->
                         case N of
                           | Var(nv,_) ->
                             let sbst = [(nv, pat_tm)] in
                             (substitute (body, sbst), rules, sbst)
                           | _ ->
                             let equal_term = mkEquality(inferType(context.spc, N), N, pat_tm) in
                             (body, addDemodRules(assertRules(context, equal_term, "case", Context, Either, None,
                                                              freeTyVarsInTerm equal_term),
                                                  rules), [])
                     in
                     rewriteTerm(solvers,(boundVars ++ patternVars pat), body,
                                 (ithLambdaBodyPos(lrules,length first))::0::path, rules)
                     >>= (fn (body',a) ->
                            let M = invertSubst(body',sbst) in
                            unit(Apply(Lambda (first ++ [(pat,cond,body')] ++ rest,b1), N, b), a)))
                  lrules))
          | Fun(Op(Qualified(_,"mapFrom"),_),_,_)
              | (case Ns of [_,Lambda([_], _)] -> true | _ -> false) ->
            let [set_term, f as Lambda([(p,c,bod)],b1)] = Ns in 
            LazyList.map (fn (set_term,a) -> (mkAppl(M,[set_term,f]),a)) 
              (rewriteTerm(solvers,boundVars,set_term,0::1::path,rules))
            @@ (fn () -> 
                  LazyList.map (fn (bod,a) -> (mkAppl(M,[set_term, Lambda([(p,c,bod)],b1)]), a))
                  (rewriteTerm(solvers,boundVars ++ patternVars p,bod,
                               (ithLambdaBodyPos([(p,c,bod)],0))::1::1::path,
                               let Some v_tm = patternToTerm p in
                               let memb_assert = mkAppl(mkInfixOp(mkUnQualifiedId("in?"),
                                                                  Infix(Left,100),
                                                                  mkArrow(mkProduct[termType v_tm,
                                                                                    termType set_term],
                                                                          boolType)),
                                                        [v_tm,set_term])
                               in
                               addDemodRules(assertRules(context, memb_assert,
                                                         "mapFrom function", Context, Either, None, freeTyVarsInTerm memb_assert),
                                             rules))))
          | _ ->
        LazyList.map (fn (N,a) -> (Apply(M,N,b),a)) 
          (rewriteTerm(solvers, boundVars, N, 1::path, rules))
        @@ (fn () -> 
              LazyList.map (fn (M,a) -> (Apply(M,N,b),a)) 
                (rewriteTerm(solvers, boundVars, M, 0::path, rules))))
     | Record(fields,b) -> 
       mapEach 
        (fn (first,(label,M),rest) -> 
            rewriteTerm(solvers,boundVars,M,(length first)::path,rules) >>= 
            (fn (M,a) -> unit(Record(first ++ [(label,M)] ++ rest,b),a)))
        fields
     | Lambda(lrules,b) ->
       let last_rule = last lrules in

       % Rewrite each pattern
       mapEach(fn (first,rule as (pat,cond,body),rest) -> 
                 rewritePattern(solvers,boundVars,pat,path, rules, first, false)
                 >>= (fn (pat,a) -> unit(Lambda (first ++ [(pat,cond,body)] ++ rest,b),a)))
         lrules % A condition on the last case should be guaranteed by the type
       
       % Rewrite each body with the additional assumption that the pattern match
       % with the argument has succeeded in that body
       @@ (fn () ->
           mapEach 
             (fn (first,(pat,cond,body),rest) -> 
                let patvars = patternVars pat in
                let rules = addPatternRestriction(context,pat,rules) in
                rewriteTerm(solvers, boundVars ++ patternVars pat, body,
                            (ithLambdaBodyPos(lrules, length first))::path, rules)
                >>= (fn (body',a) -> unit(Lambda (first ++ [(pat,cond,body')] ++ rest,b),a)))
             lrules)
     | Let(binds,M,b) ->
        % First try to rewrite the body of let-expressions; note that the path
        % (length first)::path works because we assume no guards in the pattern
        mapEach (fn (first,(pat,N),rest) ->
                   rewriteTerm(solvers,boundVars,N,(length first)::path,rules) >>=
                   (fn (N,a) -> unit(Let(first ++ [(pat,N)] ++ rest,M,b),a)))
          binds
        % Otherwise, try to fold the bindings and see if that enables a rewrite
        @@ (fn () ->
             let let_vars = flatten (map (fn (pat, _) -> patternVars pat) binds) in
             let p_M = unFoldSimpleLet(binds,M) in
             LazyList.map (fn res -> reFoldLetVars(binds,path,res,b))
               (rewriteTerm(solvers,boundVars ++ let_vars,p_M,path,rules)) )
     | LetRec(binds,M,b) ->
       let letrec_vars = map(fn (v, _) -> v) binds in
       let boundVars = boundVars ++ letrec_vars in
       mapEach (fn (first,(v,N),rest) ->
                  rewriteTerm(solvers,boundVars,N,(length first)::path,rules) >>=
                  (fn (N,a) -> unit(LetRec(first ++ [(v,N)] ++ rest,M,b),a)))
         binds
       @@ (fn () ->
             LazyList.map (fn (M,a) -> (LetRec(binds,M,b),a)) 
               (rewriteTerm(solvers,boundVars,M,(length binds)::path,rules)))

%           let let_vars = map(fn (v, _) -> v) bind in
%           LazyList.map (fn (M,a) -> (Bind(qf,vars,M,b),a))
%		(rewriteTerm(solvers,boundVars ++ let_vars,M,rules))
     | Bind(qf,vars,M,b) -> 
       LazyList.map (fn (M,a) -> (Bind(qf,vars,M,b),a))
            (rewriteTerm(solvers,boundVars ++ vars,M,0::path,rules))
     | The (var,M,b) -> 
       LazyList.map (fn (M,a) -> (The(var,M,b),a))
            (rewriteTerm(solvers,boundVars ++ [var],M,0::path,rules))
     | IfThenElse(M,N,P,b) -> 
       LazyList.map 
            (fn (M,a) -> (IfThenElse(M,N,P,b),a)) 
            (rewriteTerm(solvers,boundVars,M,0::path,rules)) @@
       (fn () -> 
       LazyList.map 
            (fn (N,a) -> (IfThenElse(M,N,P,b),a)) 
            (rewriteTerm(solvers,boundVars,N, 1::path,
                         addDemodRules(assertRules(context,M,"if then", Context, Either, None, freeTyVarsInTerm M),
                                       rules)))) @@
       (fn () -> 
       LazyList.map 
            (fn (P,a) -> (IfThenElse(M,N,P,b),a)) 
            (rewriteTerm(solvers,boundVars,P, 2::path,
                         addDemodRules(assertRules(context,negate M,"if else", Context, Either, None, freeTyVarsInTerm M),
                                       rules))))
     | Seq(tms, b) ->
       mapEach 
         (fn (first,M,rest) -> 
            rewriteTerm(solvers,boundVars,M,(length first)::path,rules) >>= 
            (fn (M,a) -> unit(Seq(first ++ [M] ++ rest,b),a)))
         tms
     | TypedTerm(M,s,b) ->
       LazyList.map (fn (M,a) -> (TypedTerm(M,s,b),a))
            (rewriteTerm(solvers,boundVars,M,0::path,rules))
     | Pi(tvs,M,b) ->
       LazyList.map (fn (M,a) -> (Pi(tvs,M,b),a))
            (rewriteTerm(solvers,boundVars,M,0::path,rules))
   %  | And(tms,b) ->
     | _ -> Nil

(* Trace utilities *)

 op traceTerm : Context * MSTerm * MSTerm -> ()
 def traceTerm(context, term, prev_term) = 
     if context.traceRewriting > 1 then 
     % if context.trace then 
	 (let indent = 3 + ! context.traceIndent in
          if context.traceShowsLocalChanges? && ~(equalTerm?(term, prev_term))
            then (let changed_ptm = changedPathTerm(term, prev_term) in
                  let prev_sub_tm = fromPathTerm(prev_term, changed_ptm.2) in
                  let prev_tm_str = printTermIndent(indent, prev_sub_tm) in
                  let new_sub_tm = fromPathTerm changed_ptm in
                  let new_tm_str  = printTerm new_sub_tm in
                  if length prev_tm_str + length new_tm_str < 90
                    then writeLine(prev_tm_str^"  --->  "^new_tm_str)
                    else if length new_tm_str < 40
                    then writeLine(prev_tm_str^"\n --->  "^new_tm_str)
                    else writeLine(prev_tm_str^"\n --->\n"^printTermIndent(indent, new_sub_tm)))
            else writeLine(printTermIndent(indent, term))
	  ) 
     else ()

 op traceRule(context:Context,rule:RewriteRule): () = 
     % if context.trace then
     if context.traceRewriting > 0 then 
	let depth = show(! context.traceDepth) in
	(toScreen (PrettyPrint.blanks (! context.traceIndent));
	 writeLine("=  { "^depth^": "^ rule.name^" }"))
     else ()

 op [a] traceRuleRec(context:Context,rule:RewriteRule,f:() -> a) : a =
   let traceIndent = ! context.traceIndent in
   if context.traceRewriting > 0 then
     (context.traceIndent := traceIndent + 3;
      toScreen ("=  "^PrettyPrint.blanks traceIndent^"{ "); 
      writeLine (show(! context.traceDepth)^" : "^rule.name);
      %              printSubst subst;
      let res = f () in
      (context.traceIndent := traceIndent;
       writeLine ("   "^PrettyPrint.blanks traceIndent ^"}");
       %(case res of Some s -> printSubst s | _ -> ());
       res)
      )
   else 
     f ()


 (* Check condition of conditional rewrite rule *)

%%
%% Check that all variables in a term are bound by the substitution.
%%

 def completeMatch(term: MSTerm,subst:SubstC): Bool =
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
	          (case flexVarNum(term) 
		     of Some n -> NatMap.inDomain(S,n) 
		      | None -> loop t1 && loop t2)
	        | Seq(terms,_) -> forall? loop terms
     in
     loop term

 % A history of the steps used to rewrite a term, where the last term
 % (the result of all the rewriting) is first
 type History = List (RewriteRule * MSTerm * SubstC * Proof)

 op emptyHistory : History = []

 op historyRepetition: History -> Bool
 def historyRepetition = 
     fn | (_,term1,_,_)::(_,term2,_,_)::_ -> equalTerm?(term1,term2)
        | _ -> false

 % Transitively combine all the proofs in a history into one proof
 % that input_trm = output_trm
 op combineHistoryProofs (input_trm : MSTerm, T : MSType, hist : History) : Proof =
   case hist of
     | [] -> prove_equalRefl (T, input_trm)
     | [(_, _, _, pf)] -> pf
     | (_, _, _, pf_last)::hist' ->
       prove_equalTrans (combineHistoryProofs (input_trm, T, hist'), pf_last)

 op rewriteRecursive :
    Context * MSVars * RewriteRules * MSTerm ->
    Option (MSTerm * Proof)

 op rewriteWithRules_opt : Spec * RuleSpecs * MSTerm -> Option (MSTerm * Proof)
 op rewriteWithRules : Spec * RuleSpecs * MSTerm -> MSTerm * Proof

 op rewriteRecursivePre : 
    Context * MSVars * Demod RewriteRule * MSTerm -> LazyList (History)

 op minTraceDepth: Nat = 10


 %%
 %% The main entrypoint for rewriting
 %%

 % Forward reference for rewriteWithRules
 op Script.makeRules (context: Context, spc: Spec, rules: RuleSpecs, ctxt_rules: List RewriteRule): List RewriteRule

 % A slightly higher-level version of the rewriter, that uses
 % RuleSpecs and does not need a Context
 def rewriteWithRules_opt(spc: Spec, rules: RuleSpecs, term: MSTerm) : Option (MSTerm * Proof) =
   let context = makeContext spc in
   let context = setTopTerm (context, term) in
   let rules = makeRules (context, spc, rules, []) in
   rewriteRecursive (context, [], splitConditionalRules rules, term)

 def rewriteWithRules (spc: Spec, rules: RuleSpecs, term: MSTerm): MSTerm * Proof =
   case rewriteWithRules_opt (spc, rules, term) of
     | Some res -> res
     | None -> (term, prove_equalRefl (inferType (spc, term), term))

 % Rewrite the subterm of term at path
 def rewriteRecursive(context,boundVars,rules,term) = 
%      let rules = {unconditional = addDemodRules(rules.unconditional,Demod.empty),
% 		  conditional   = addDemodRules(rules.conditional,Demod.empty)}
   let rules = addDemodRules(rules.unconditional ++ rules.conditional,Demod.empty) in
   case rewriteRecursivePre(context,boundVars,rules,term) of
     | Nil -> None
     | Cons ([], _) -> None
     | Cons (history as (_,out_term,_,_)::_, _) ->
       Some (out_term, combineHistoryProofs (term, inferType (context.spc, term), history))

 def rewriteRecursivePre(context, boundVars0, rules0, term) =
   let
     def rewritesToTrue(rules, term, boundVars, backChain): Option (SubstC * Proof) =
       % let _ = writeLine("boundVarsC: "^anyToString boundVars) in
       if trueTerm? term then Some (emptySubstitution, prove_true)
       else
         let results = rewriteRec(rules, term, [], term, boundVars, emptyHistory, backChain+1) in
         case LazyList.find_n (fn | (rl, t, c_subst, pf)::_ -> trueTerm? t || falseTerm? t || evalRule? rl
                                  | [] -> false)
           results
           conditionResultLimit
         of
           None -> None
         | Some (hist as ((_, t, c_subst, _)::_)) ->
           if trueTerm? t then
             Some (c_subst,
                   prove_fromEqualTrue (term,
                                        combineHistoryProofs
                                          (term, inferType (context.spc,term), hist)))
           else None

     def solveCondition (cond, rules, boundVars, backChain) : Option (SubstC * Proof) = 
	if backChain < context.backwardChainMaxDepth then 
          let _ = context.traceDepth := 0 in % reset traceDepth for solving conditions
          rewritesToTrue(rules, cond, boundVars, backChain)
	else None

     def rewriteRec(rules0, term0, path0, prev_term, boundVars1, history, backChain) =
        % let _ = writeLine("boundVars1: "^anyToString boundVars1) in
	let _ = traceTerm(context, term0, prev_term) in
	let traceDepth = ! context.traceDepth + 1 in
        let maxTraceDepth = if backChain = 0
                              then context.maxDepth
                            else max(context.maxDepth,
                                     context.backwardChainMaxDepth) in
        if traceDepth > maxTraceDepth
          then unit history
        else
        let ts = termSize term0 in
        if traceDepth > minTraceDepth && termSize term0 > context.termSizeLimit
          then (warn("Rewriting terminated because term size of "^show ts^" exceeded limit of "^show context.termSizeLimit);
              unit history)
        else
        let def rewrite(strategy, rules) =
              % let _ = writeLine("Rules:") in
              % let _ = app printRule (listRules rules) in
              let context = setTopTerm (context, term0) in
              rewriteTerm 
                ({strategy = strategy,
                  rewriter = applyDemodRewrites(context, context.maxDepth > 1 || backChain > 0),
                  context = context},
                 boundVars1, term0, path0, rules)
        in
        if historyRepetition(history)
          then unit (tail history)
        else
      % let rews = (rewrite(Innermost, unconditional) >>= 
	let rews = (rewrite(Outermost, rules0) >>= 
		    (fn (term, (subst, rule, path, boundVarsRl, rules1)) ->  
			unit (term, (subst, rule, path, boundVarsRl, rules1))) 
% 		    @@
% 		    (fn () -> 
% 		     rewrite(Outermost, conditional) >>= 
% 		     (fn (term, (subst, rule, boundVars, rules)) ->  
% 			unit (term, (subst, rule, boundVars,
% 				    {conditional   = conditional,
% 				     unconditional = unconditional}))))
                    )
	in
	(rews >>= 
           (fn (term, (subst, rule, path, boundVarsRl, rules1)) ->
              % let _ = writeLine("boundVarsRl: "^anyToString boundVarsRl) in

              % At this point, a rewrite has been successfully applied to term0, the input term. We
              % now need to ensure that all of the preconditions of the rule which was applied hold;
              % this is done by solveCondition, which itself recursively applies rewriting.
              %
              % The conditions which must be solved include the precondition of the rule itself, as
              % well as any type unification conditions from higher-order matching, which include
              % any subtype predicates on the free variables of the rules.
              let (_, _, conds) = subst in
              let opt_subst_pf =
                if conds = [] then
                  (traceRule(context, rule); Some (subst, prove_true))
                else if termIn?(term0, conds) then
                  % Avoid subproblem same as original
                  (%writeLine("Found recursive subgoal: "^printTerm prev_term);
                     None)
                else
                  % At this point, subst has only been applied to the output term, term, so now we
                  % additionally apply it to the condition we are about to try to solve.  Note that
                  % boundVars are considered free in the condition, which must be true at the point
                  % in the input term where the rewrite occurred.
                  let cond = dereferenceAllAsSubst subst (mkConj conds) boundVarsRl in

                  % The condition could still have free flex variables, e.g., for a rule like
                  % transitivity, written as below, where we may have already rewritten x<z to true
                  % but we don't yet know y:
                  % fa (x,y,z) x<y && y<z => x<z = true
                  %
                  % We need to freshen up the free flex variables of cond before we try to rewrite
                  % it so that none of them clash with free flex variables in our rules
                  let fresh_subst = fresheningSubstFor (context, cond) in
                  % README: don't need dereferenceAllAsSubst here because fresh_subst just replaces
                  % flex vars with other flex vars, so substitution and grafting are the same
                  let cond = dereferenceAll fresh_subst cond in
                  case
                    traceRuleRec (context, rule,
                                  fn () ->
                                    solveCondition (cond, rules1,
                                                    boundVarsRl, backChain+1))
                    of
                    | None -> None
                    | Some (subst', pf) ->
                      % subst' is a substitution that is to be applied after fresh_subst, which
                      % itself is to be applied after the original subst we got from rewriting, so
                      % here we compose them all together.
                      Some (composeSubstCs subst'
                              (composeSubstCs fresh_subst subst),
                            pf)
              in
              case opt_subst_pf of
                | None -> Nil
                | Some (final_subst, cond_pf) ->
                  % Now we apply final_subst to the output term, term, and build a proof that
                  % original input term = term.  Note that we don't use dereferenceAllAsSubst
                  % because we want grafting, not substitution, i.e., we are rewriting subterms of
                  % term that might contain variables bound in term.
                  let term = dereferenceAll final_subst term in

                  % If there are any remaining flex vars we sanitize them to ops
                  let term = if context.allowUnboundVars? then sanitizeFlexVars (context, term) else term in

                  % To build the proof that the input term, term0, equals the output term, term, we
                  % first undo the rewrite that was applied to get term, to get
                  % term_without_rr. This is not necessarily equal to term0, since rewriteTerm
                  % optionally performs some commuting conversions that push function calls inside
                  % of ifs, lets, and cases. We prove term0=term_without_rr using an auto tactic and
                  % then prove term_without_rr=term using the proof given in the rule. The latter
                  % proof additionally requires: type substitution, for any free type variables;
                  % forall elimination, to substitute in the values of any free term variables in
                  % the rule; and implication elimination, to supply a proof of the condition of the
                  % rule.  Rather than trying to build all of these proofs explicitly, all of the
                  % "helper" proofs are built with an auto tactic augmented with the proof cond_pf
                  % of the conjunction of conds above. This includes the proof that
                  % term0=term_without_rr, as this equality might depend on some of the type
                  % conditions returned by higher-order matching.
                  let term_without_rr =
                    case validPathTermWithErr (term, path) of
                      | None ->
                        topTerm (replaceSubTerm
                                   (dereferenceAllAsSubst
                                      final_subst rule.lhs boundVarsRl,
                                    (term, path)))
                      | Some (valid_prefix, ok_tm, bad_step) ->
                        (warn
                           ("rewriteRec: invalid returned path "
                              ^ printPath path
                              ^ " in term (" ^ printTerm term
                              ^ ") with orig term ("
                              ^ printTerm term0
                              ^ ") and rule LHS ("
                              ^ printTerm (dereferenceAllAsSubst
                                             final_subst rule.lhs boundVarsRl)
                              ^ "); prefix " ^ printPath valid_prefix
                              ^ " yields subterm ("
                              ^ printTerm ok_tm
                              ^ ") which does not allow next step "
                              ^ show bad_step);
                         term0)
                  in
                  let auto_helpers =
                    if trueProof? cond_pf then [] else [cond_pf]
                  in
                  let pf1 =
                    if equalTerm? (term0, term_without_rr) then
                      prove_equalRefl (inferType (context.spc, term0), term0)
                    else
                      prove_equalWithTactic (WithTactic(auto_helpers,
                                                        fn ids ->
                                                          "(auto simp add: Let_def"
                                                         ^foldl (fn (s, si) -> s^" "^si)
                                                            "" ids^")"),
                                             term0,
                                             term_without_rr,
                                             inferType (context.spc, term0))
                  in
                  let pf2 =
                    case rule.opt_proof of
                      | None ->
                        % If there is no proof, use "auto" to prove the equality of the rewrite,
                        % throwing in cond_pf as well (why not?)
                        % let _ = printRule rule in
                        prove_equalWithTactic (WithTactic(auto_helpers,
                                                          fn ids ->
                                                            "(auto simp add:  Let_def"
                                                            ^foldl (fn (s, si) -> s^" "^si)
                                                            "" ids^")"),
                                               term_without_rr, term,
                                               inferType (context.spc, term))
                      | Some rule_pf ->
                        % If there is a proof for the rule, use it to prove that
                        % term_without_rr=term.
                        %
                        % Step 1: Instantiate any type variables
                        let rule_pf1 =
                          instantiateTyVarsInProof
                            (tyVarSubstFromSubstC final_subst, rule_pf)
                        in

                        % Step 2: Instantiate universally quantified variables using forall
                        % elimination
                        let var_terms_pfs =
                          map (fn (var_i, var_tp) ->
                                 % Go through each free variable of a
                                 % rule, find what term it has been
                                 % mapped to, and forall-eliminate the
                                 % proof against that term
                                 let var_term =
                                   dereferenceAll subst (mkVar (var_i, var_tp))
                                 in
                                 (var_term,
                                  prove_withTactic
                                    (AutoTactic [cond_pf],
                                     typePredTermNoSpec (var_tp, var_term))))
                          rule.freeVars
                        in
                        let rule_pf2 =
                          prove_forallElimMulti (rule_pf1, var_terms_pfs)
                        in

                        % Step 3: Cut (i.e., perform implication elimination) the proof against the
                        % proof of the condition, if any
                        let rule_pf3 =
                          case rule.condition of
                            | Some cond ->
                              prove_implElim (rule_pf2,
                                              prove_withTactic
                                                (AutoTactic [cond_pf], cond))
                            | None -> rule_pf2
                        in

                        % Step 4: Apply symmetry to a proof of rhs=lhs
                        % to get one of lhs=rhs if sym_proof is set
                        let rule_pf4 =
                          if rule.sym_proof then prove_equalSym rule_pf3
                          else rule_pf3
                        in

                        % Step 5: Expand the resulting proof that
                        % lhs=rhs from the subterms to the superterms
                        prove_equalSubTerm (term_without_rr, term,
                                            inferType (context.spc, term),
                                            path, rule_pf4)
                  in
                  let pf = prove_equalTrans (pf1, pf2) in
                  % let _ = writeLine ("rewriteRec succeeded: term ("
                  %                      ^ printTerm term0
                  %                      ^ ") rewritten to term ("
                  %                      ^ printTerm term ^ ")") in
                  let history = Cons ((rule, term, final_subst, pf),history) in
                  % increment the trace depth before the recursive call
                  let _ = context.traceDepth := traceDepth in
                  rewriteRec(rules0, term, path0, term0, boundVars1, history, backChain)))
        @@
        (fn () -> unit history)
   in
      %let term = dereferenceAll emptySubstitution term in
      rewriteRec(rules0, term, [], term, boundVars0, [], 0)

 op rewriteOnce : 
    Context * MSVars * RewriteRules * MSTerm * Path -> MSTerms

%%
%% Apply unconditional rewrite rules using outer-most strategy
%%
 def rewriteOnce(context, boundVars, rules, term, path) = 
     let unconditional = Demod.addRules(List.map (fn rl -> (rl.lhs, rl)) 
						rules.unconditional, Demod.empty) in
     (* unused...
     let conditional   = Demod.addRules(List.map (fn rl -> (rl.lhs, rl)) 
						rules.conditional, Demod.empty)  in
     *)

%    let {unconditional, conditional} = rules in
     let subst = emptySubstitution in
     let term = dereferenceAll emptySubstitution term in
     let rews = rewriteTerm
		 ({strategy = Innermost,
		   rewriter = applyDemodRewrites(context, false),
		   context = context},
		  boundVars, term, path, unconditional)
     in
     let rews = LazyList.toList rews in
     map (fn (newTerm, (subst, rule, path, boundVars, rules)) -> 
            dereferenceAll subst newTerm)
       rews

	  
end-spec
