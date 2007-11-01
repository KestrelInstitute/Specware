(* Rewrite rule control *)

MetaSlangRewriter qualifying spec 
 import /Library/Legacy/DataStructures/LazyList
 import DeModRewriteRules, Simplify, Interpreter
 
 type Context = HigherOrderMatching.Context

 type TermPredicate = MS.Term * MS.Term -> Boolean

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
       -> List Var * MS.Term 
	   -> LazyList (MS.Term * (SubstC * RewriteRule * List Var * List RewriteRule))

 op applyRewrite(context: Context, rule: RewriteRule, subst: SubstC, term: MS.Term): List SubstC = 
   let lhs = rule.lhs in
   filter (fn subst -> completeMatch(lhs,subst))
     (matchPairs(context,subst,stackFromList [(lhs,term)]))

 def applyRewrites(context,rules,subst) (boundVars,term) = 
     let context = setBound(context,boundVars) in
     mapEach 
       (fn (first,rule,rest) -> 
          let substs = applyRewrite(context,rule,subst,term) in
          if null substs
	    then emptyList
          else
            let rule1 = freshRule (context,rule) in
            let rules = rest ++ first ++ [rule1] in
            fromList
	      (map (fn s -> (dereferenceAll s (renameBoundVars(rule.rhs,boundVars)),
                             (s,rule,boundVars,rules)))
                 substs)) 
       rules

 op useStandardSimplify?: Boolean = true
 op debugApplyRewrites?: Boolean = false

 op applyDemodRewrites(context: Context, subst: SubstC, standardSimplify?: Boolean)
                      (boundVars: List Var, term: MS.Term, demod: Demod RewriteRule)
                      : LazyList(MS.Term * (SubstC * RewriteRule * List Var * Demod RewriteRule))  = 
%     let _ = writeLine("Rewriting:\n"^printTerm term) in
%     let _ = writeLine("with rules:") in
%     let _ = app printRule (listRules demod) in
   let context = setBound(context,boundVars)  in
   let spc     = context.spc                  in
   let rules = Demod.getRules(demod,term)     in
   (mapFlat 
      (fn rule ->
          let _ = if debugApplyRewrites? then
                   (writeLine("boundVars: "^anyToString boundVars);
                    printRule rule;
                    writeLine("Matching "^printTerm rule.lhs^" against\n"^printTerm term))
                   else ()
          in
          let substs = applyRewrite(context,rule,subst,term) in
          let _ = if debugApplyRewrites? then
                    if substs = [] then writeLine("Match failed.\n")
                      else (writeLine("Match succeeded."); printSubst (hd substs))
                  else ()
          in
          fromList
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
               substs)) 
      rules)
   @@ (fn () -> if standardSimplify? && useStandardSimplify?
                  then standardSimplify spc (term,subst,boundVars,demod)
                  else Nil)


 def evalRule : RewriteRule = 
     { 
	name     = "Eval",
	freeVars = [],
	tyVars = [],
	condition = None,
	lhs   = mkVar(1,TyVar("''a",noPos)),
	rhs   = mkVar(2,TyVar("''a",noPos))
     } 

 op ssRule(s: String): RewriteRule =
   evalRule << {name = s}

 op evalRule?(rl: RewriteRule): Boolean =
   rl.tyVars = [] && rl.lhs = evalRule.lhs && rl.rhs = evalRule.rhs

 op pushFunctionsIn?: Boolean = true
 op evalGroundTerms?: Boolean = true

 op standardSimplify (spc: Spec) (term: MS.Term, subst: SubstC, boundVars: List Var, demod: Demod RewriteRule)
    :  LazyList(MS.Term * (SubstC * RewriteRule * List Var * Demod RewriteRule)) =
   case tryEvalOne spc term of
     | Some eTerm ->
       % let _ = writeLine("EvalOne:\n"^printTerm term^"\nTo:\n"^printTerm eTerm) in
       unit (eTerm, (subst,ssRule "Eval1",boundVars,demod))
     | None ->
   let (simp?, term) = if evalGroundTerms? &&  ~(constantTerm? term) && freeVarsRec term = []
                         then
                           let v = eval(term,spc) in
                           if fullyReduced? v
                             then
                               let new_term = valueToTerm v in
                               if equalTerm?(new_term, term)
                                 then (false, term)
                                 else (true, new_term)
                           else (false, term)
                       else (false, term)
   in
   if simp? then unit(term, (subst,evalRule,boundVars,demod))
   else
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
                   || equivType? spc (stripSubsorts (spc, tm_ty), term_ty))
              && all (fn (i1,t1) ->
                       case t1 of
                         | Apply(Fun(Project i2,_,_), t, _) ->
                           i1 = i2 && equalTerm?(t, tm)
                         | _ -> false)
                  r_flds)
         -> unit (tm, (subst,ssRule "RecordId",boundVars,demod))
     | Apply(Fun(Embedded id1,_,_), Apply(Fun(Embed(id2,_),_,_),_,_),_) ->
       unit (mkBool(id1 = id2), (subst,ssRule "reduceEmbed",boundVars,demod))
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
 op pushable?(f: MS.Term): Boolean =
   case f of
     | Fun _ -> true
     | Var _ -> true
     | Apply _ -> true
     | Lambda _ -> true
     | _ -> false

  op addPatternRestriction(context: Context, pat: Pattern, rules: Demod RewriteRule)
    : Demod RewriteRule =
   case pat of
     | VarPat(v as (_,ty), _) ->
       (let ty = unfoldBase(context.spc,ty) in
          case ty of
            %% Redundant with subsort rules introduced in Script.sw
            | Subsort(_,p,_) ->
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
               addDemodRules(assertRules(context, condn, "Subtype", false),rules))
            | _ -> rules)
     | RecordPat(fields, _ ) ->
       foldl (fn ((_,p), rules) -> addPatternRestriction(context, p, rules)) rules fields
     | RestrictedPat(p,condn,_) ->
       addPatternRestriction(context, p,
                             addDemodRules(assertRules(context,condn,"Restriction",false), rules))
     | EmbedPat(_, Some p, _, _) -> addPatternRestriction(context, p, rules)
     | AliasPat(_, p, _)    -> addPatternRestriction(context, p, rules)
     | QuotientPat(p, _, _) -> addPatternRestriction(context, p, rules)
     | SortedPat(p, _, _)   -> addPatternRestriction(context, p, rules)
     | _ -> rules

 def negate term =
   case term of
     | Apply (Fun(Not,_,_), p,                        _) -> p
     | Apply (Fun(Or,_,_),  Record([(_,M),(_,N)], _), _) ->
       Utilities.mkAnd(negate M,negate N)
     | _ -> mkNot term

 op useUnfoldLetStrategy?: Boolean = true

 op substFromBinds(binds: List(Pattern * MS.Term)): VarSubst =
   mapPartial (fn (p, be) ->
                 case p of
                   | VarPat(v,_) -> Some (v,be)
                   | _ -> None)
     binds
 
 op unFoldSimpleLet(binds: List(Pattern * MS.Term), M: MS.Term)
    : MS.Term =
    let v_subst = substFromBinds binds in
    if binds = [] || v_subst = [] || ~useUnfoldLetStrategy?
      then M
      else substitute(M,v_subst)

 op reverseSubst (v_subst: VarSubst) (t: MS.Term): MS.Term =
   case v_subst of
     | [] -> t
     | (v,vt)::_ | equalTerm?(vt,t) && ~((embed? Fun) vt)-> mkVar v
     | _ :: r -> reverseSubst r t

 op invertSubst (tm: MS.Term, sbst: VarSubst): MS.Term =
   if sbst = [] then tm
     else mapTerm (reverseSubst sbst, id, id) tm

 op reFoldLetVars(binds: List(Pattern * MS.Term), M: MS.Term, b: Position)
    : MS.Term =
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
                        case p of
                          | VarPat(v,_) -> inVars?(v,fvs)
                          | _ -> true)
                binds,
              M1, b)

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
     let substs = matchPairs(context,subst, stackFromList [(M,N)]) in
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

 type Rewriter a = List Var * MS.Term * Demod RewriteRule -> LazyList (MS.Term * a) 
 %type Matcher  a = List Var * Term * Term -> LazyList a
 type Strategy   = | Innermost | Outermost
 type RewriteInfo a = {strategy: Strategy, rewriter: Rewriter a, context: Context}

 op rewriteTerm    : [a] RewriteInfo a * List Var * MS.Term * Demod RewriteRule
                           -> LazyList (MS.Term * a)
 op rewriteSubTerm : [a] RewriteInfo a * List Var * MS.Term * Demod RewriteRule
                           -> LazyList (MS.Term * a)

 op [a] rewritePattern (solvers: RewriteInfo a, boundVars: List Var,
                        pat: Pattern, rules: Demod RewriteRule)
          : LazyList(Pattern * a) =
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
     (case term of
% sjw: I don't know why these were ever separate cases
%         | Apply(Fun(Not,s,_),arg,b) ->  
% 	   LazyList.map 
% 		(fn (arg,a) -> (Apply(Fun(Not,s,b), arg, b),a)) 
% 		(rewriteTerm(solvers,boundVars,arg,rules))
%         | Apply(Fun(And,s,_),Record([(l1,M),(l2,N)], _),b) -> 
% 	   LazyList.map 
% 		(fn (N,a) -> (Apply(Fun(And,s,b),
% 				    Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,N,rules)) @@
% 	   (fn () -> 
% 	   LazyList.map 
% 		(fn (M,a) -> (Apply(Fun(And,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,M,rules))) 
%         | Apply(Fun(Or,s,_),Record([(l1,M),(l2,N)], _),b) -> 
% 	   LazyList.map 
% 		(fn (N,a) -> (Apply(Fun(Or,s,b),
% 				    Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,N,rules)) @@
% 	   (fn () -> 
% 	   LazyList.map 
% 		(fn (M,a) -> (Apply(Fun(Or,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,M,rules))) 
%         | Apply(Fun(Implies,s,_),Record([(l1,M),(l2,N)], _),b) -> 
% 	   LazyList.map 
% 		(fn (N,a) -> (Apply(Fun(Implies,s,b),
% 				    Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,N,rules)) @@
% 	   (fn () -> 
% 	   LazyList.map 
% 		(fn (M,a) -> (Apply(Fun(Implies,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,M,rules))) 
%         | Apply(Fun(Iff,s,_),Record([(l1,M),(l2,N)], _),b) -> 
% 	   LazyList.map 
% 		(fn (N,a) -> (Apply(Fun(Iff,s,b),
% 				    Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,N,rules)) @@
% 	   (fn () -> 
% 	   LazyList.map 
% 		(fn (M,a) -> (Apply(Fun(Iff,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,M,rules))) 
%         | Apply(Fun(Equals,s,_),Record([(l1,M),(l2,N)], _),b) -> 
% 	   LazyList.map 
% 		(fn (N,a) -> (Apply(Fun(Equals,s,b),
% 				    Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,N,rules)) @@
% 	   (fn () -> 
% 	   LazyList.map 
% 		(fn (M,a) -> (Apply(Fun(Equals,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,M,rules))) 
%         | Apply(Fun(NotEquals,s,_),Record([(l1,M),(l2,N)], _),b) -> 
% 	   LazyList.map 
% 		(fn (N,a) -> (Apply(Fun(NotEquals,s,b),
% 				    Record([(l1,M),(l2,N)],b),b),a)) 
% 		(rewriteTerm(solvers,boundVars,N,rules)) @@
% 	   (fn () -> 
% 	   LazyList.map 
%		(fn (M,a) -> (Apply(Fun(NotEquals,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
%		(rewriteTerm(solvers,boundVars,M,rules))) 

% Moved in Apply case
%          | Apply(f, c_tm as (Apply(Lambda(binds,b3), case_tm, b2)), b1)
%               | pushFunctionsIn?
%                   && (case f of
%                         | Fun _ -> true
%                         | Var _ -> true
%                         | Apply _ -> true
%                         | Lambda _ -> true
%                         | _ -> false)
%                 ->
%            let new_c_tm = Apply(Lambda(map (fn (p,c,bod) ->
%                                                     (p,c,Apply(f,bod,b1)))
%                                                binds, b3),
%                                       case_tm,b2)
%            in
%              rewriteTerm(solvers,boundVars,new_c_tm,rules)
%              @@ (fn () ->
%                    LazyList.map (fn (f,a) -> (Apply(f,c_tm,b2),a)) 
%                      (rewriteTerm(solvers,boundVars,f,rules)))
	 | Apply(M,N,b) ->
           let Ns = termToList N in
           (case findIndex (embed? IfThenElse) Ns  of
              | Some (i,if_tm) | pushFunctionsIn? && pushable? M ->
                (let IfThenElse(p,q,r,b1) = if_tm in
                 let r_tm = IfThenElse(p,
                                       mkAppl(M,replaceNth(i, Ns, q)),
                                       mkAppl(M,replaceNth(i, Ns, r)), b)
                 in rewriteTerm(solvers,boundVars,r_tm,rules))
              | _ ->
            case findIndex (embed? Let) Ns  of
              | Some (i,let_tm) | pushFunctionsIn? && pushable? M ->
                (let Let(bds,lt_body,a2) = let_tm in
                 let r_tm = Let(bds, mkAppl(M,replaceNth(i, Ns, lt_body)),a2) in
                 rewriteTerm(solvers,boundVars,r_tm,rules))
              | _ ->
            case findIndex caseExpr? Ns  of
              | Some (i,case_tm) | pushFunctionsIn? && pushable? M ->
                (let Apply(Lambda(binds,b3), case_tm, b2) = case_tm in
                 let r_tm = Apply(Lambda(map (fn (p,c,bod) ->
                                                (p,c,mkAppl(M,replaceNth(i, Ns, bod))))
                                           binds, b3),
                                  case_tm, b2)
                 in rewriteTerm(solvers,boundVars,r_tm,rules))
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
                                 (M, addDemodRules(assertRules(context, equal_term, "case", false), rules), [])
                         in
                         rewriteTerm(solvers,(boundVars ++ patternVars pat), M, rules)
                         >>= (fn (M,a) ->
                                let M = invertSubst(M,sbst) in
                                unit(Apply(Lambda (first ++ [(pat,cond,M)] ++ rest,b1), N, b), a)))
                      lrules))
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
			     addDemodRules(assertRules(context,M,"if then",false),rules)))) @@
	   (fn () -> 
	   LazyList.map 
		(fn (P,a) -> (IfThenElse(M,N,P,b),a)) 
		(rewriteTerm(solvers,boundVars,P,
			     addDemodRules(assertRules(context,negate M,"if else",false),rules))))
         | SortedTerm(M,s,b) ->
           LazyList.map (fn (M,a) -> (SortedTerm(M,s,b),a))
		(rewriteTerm(solvers,boundVars,M,rules))
         | Pi(tvs,M,b) ->
           LazyList.map (fn (M,a) -> (Pi(tvs,M,b),a))
		(rewriteTerm(solvers,boundVars,M,rules))
       %  | And(tms,b) ->
 	 | _ -> Nil)

(* Trace utilities *)

 op printTerm: Nat * MS.Term -> String
 def printTerm (indent,term) = 
     let indent   = PrettyPrint.blanks indent in
     let context  = initialize(asciiPrinter,false) in 
     let argument = ([],Top) in
     let termPP   = ppTerm context argument term in
     let termPP   = PrettyPrint.prettysNone [PrettyPrint.string indent,termPP] in
     PrettyPrint.toString(PrettyPrint.format(60,termPP))

 op traceTerm : Context * MS.Term * SubstC -> ()
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
	let depth = toString(! context.traceDepth) in
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
	 def loop(term:MS.Term):Boolean = 
	     case term
	       of Fun(top,srt,_) -> true
	        | Var((id,srt), _)  -> true
	        | Let(decls,bdy,_) -> 
	          all (fn (_,M) -> loop M) decls & loop bdy
	        | LetRec(decls,bdy,_) -> 
	          all (fn (_,M) -> loop M) decls & loop bdy
	        | Record(row, _) -> 
	          all (fn (_,M) -> loop M) row
	        | IfThenElse(t1,t2,t3,_) -> loop t1 & loop t2 & loop t3
	        | Lambda(match,_) -> 
	          all  (fn (_,_,M) -> loop M) match
                | The(var,trm,_) -> loop trm
                | Bind(bnd,vars,trm,_) -> loop trm
	        | Apply(t1,t2,_) -> 
	          (case isFlexVar?(term) 
		     of Some n -> NatMap.inDomain(S,n) 
		      | None -> loop t1 & loop t2)
	        | Seq(terms,_) -> all loop terms
     in
     loop term

 op backwardChainMaxDepth: Nat = 10

 type History = List (RewriteRule * MS.Term * SubstC)

 op historyRepetition: History -> Boolean
 def historyRepetition = 
     fn (_,term1,_)::(_,term2,_)::_ -> equalTerm?(term1,term2)
      | _ -> false

 op rewriteRecursive : 
    Context * List Var * RewriteRules * MS.Term * Nat -> LazyList (History)

 op rewriteRecursivePre : 
    Context * List Var * Demod RewriteRule * MS.Term * Nat -> LazyList (History)


%%
%% Apply unconditional rewrite rules using inner-most strategy.
%% Apply conditional rewrite rules using outer-most strategy.
%%

 def rewriteRecursive(context,boundVars,rules,term,maxDepth) = 
%      let rules = {unconditional = addDemodRules(rules.unconditional,Demod.empty),
% 		  conditional   = addDemodRules(rules.conditional,Demod.empty)}
     let rules = addDemodRules(rules.unconditional ++ rules.conditional,Demod.empty)
     in rewriteRecursivePre(context,boundVars,rules,term,maxDepth)

 def rewriteRecursivePre(context,boundVars,rules0,term,maxDepth) = 
   let	
      def rewritesToTrue(rules,term,boundVars,subst,history,backChain): Option SubstC =
          if trueTerm? term then Some subst
          else
	  let results = rewriteRec(rules,subst,term,boundVars,history,backChain+1) in
          case LazyList.find (fn (rl,t,c_subst)::_ -> trueTerm? t || falseTerm? t || evalRule? rl
                               | [] -> false)
                 results
	    of None -> None
	     | Some((rl,t,c_subst)::_) ->
               %% Substitutions, history and conditional rewrites need work
	       if trueTerm? t then Some c_subst else None

      def solveCondition(rules,rule,(sortSubst,termSubst,typeConds),boundVars,history,backChain)
          : Option SubstC = 
        let subst = (sortSubst,termSubst,[])
        in
        let conds = case rule.condition of
                      | None -> typeConds
                      | Some cond -> Cons(cond, typeConds)
        in
	if conds = []
          then
	     (traceRule(context,rule);
	      Some subst)
        else
	if backChain < backwardChainMaxDepth && completeMatch(rule.lhs,subst) then 
            let cond = foldl Utilities.mkAnd trueTerm conds in
            let cond = dereferenceAll subst cond in
	    let traceIndent = ! context.traceIndent in
	    let res = if traceRewriting > 0 then
                        (context.traceIndent := traceIndent + 3;
                         toScreen ("=  "^PrettyPrint.blanks traceIndent^"{ "); 
                         writeLine (toString(! context.traceDepth)^" : "^rule.name);
                         %%              printSubst subst;
                         context.traceDepth := 0;
                         rewritesToTrue(rules,cond,boundVars,emptySubstitution,history,backChain))
                      else 
                        (context.traceDepth := 0;
                         rewritesToTrue(rules,cond,boundVars,emptySubstitution,history,backChain))
            in
	    if traceRewriting > 0 then
	      (context.traceIndent := traceIndent;
	       writeLine ("   "^PrettyPrint.blanks traceIndent ^"}");
	       res)
	    else
	       res
	else None

      def rewriteRec(rules0,subst,term,boundVars,history,backChain) =
	let _ = traceTerm(context,term,subst)     in
	let traceDepth = ! context.traceDepth + 1 in
        if traceDepth > maxDepth then unit history
        else
	let def rewrite(strategy,rules) =
%                 let _ = writeLine("Rules:") in
%                 let _ = app printRule (listRules rules) in
		rewriteTerm 
		  ({strategy = strategy,
		    rewriter = applyDemodRewrites(context,subst,maxDepth > 1),
		    context = context},
		   boundVars,term,rules)     
	in
	if historyRepetition(history)
	    then unit (tl history)
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
	     case solveCondition(rules1,rule,subst,boundVars,history,backChain+1)
	       of Some subst -> 
		 (context.traceDepth := traceDepth;
		  let term = dereferenceAll subst term in
		  let term = renameBound term in
                  let history = Cons((rule,term,subst),history) in
		  let rec_results
                     = rewriteRec(rules0,emptySubstitution,term,boundVars, history, backChain)
                   in
                   if rec_results = Nil
                     then unit history
                     else rec_results)
	       | None -> Nil
                     ))
   in
      let term = dereferenceAll emptySubstitution term in
      rewriteRec(rules0,emptySubstitution,term,boundVars,[],0)

 op rewriteOnce : 
    Context * List Var * RewriteRules * MS.Term -> List MS.Term

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
\subsection{Discussion}

\begin{itemize}
\item This allows to use rewriting as abstract execution. 
      What about compiled forms? A la type based partial evaluation forms, or
      unboxing analysis?

      Code generation should generate code of the form
      \begin{verbatim}
      (defun f (x) 
        (let ((x-unboxed (unbox x)))
             (if (boxed? x)
                 (box (cons :|Apply| AST-for-symbol-f x-unboxed))
	      (unboxed (standard-code-for-f x-unboxed)))))
      \end{verbatim}
\item Implement the boxification as a Spec to Spec transformation that allows
      to reuse one code generator.
      \begin{verbatim}
        sort Box a = | Boxed Term | UnBoxed a
        op  boxifySpec : Spec -> Spec
        op  boxifyTerm : Term -> Term
        op  boxifySort : Sort -> Sort
            
        boxifyDef(def f = fn x -> body) = 
            def f = fn Boxed x -> Boxed('Apply(f,x)) | UnBoxed x -> boxifyTerm body

        boxifyTerm(Apply(f,g)) = 
            case f
              of Boxed f -> Boxed('Apply(f,'g))
               | Unboxed f -> 
            case g
              of Unboxed g -> Apply(f,g)
               | Boxed g -> Boxed('Apply(f,g))

      \end{verbatim}
      
\item Extend partial evaluation/boxing format with calls to rewrite engine, or
      interleave these steps.

\end{itemize}
*)