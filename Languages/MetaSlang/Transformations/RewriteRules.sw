(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Conditional rewrite rules

Convert an axiom of the form

   fa (x) p x => M x = N x

to a rewrite rule in the internal representation, turning 
universally quantified variables into meta variables.
Equalities are not directed in other ways than their representation.
Positive occurrences of universal quantifiers are turned into 
($\lambda$) bound variables. Since bound variables cannot occur 
freely in solutions to meta-variables, this scheme ensures correct
skolemization.
*)

RewriteRules qualifying spec 
 import HigherOrderMatching
 import ../Specs/Proof
 % import ../AbstractSyntax/PathTerm

 type Context = HigherOrderMatching.Context

 type Decl  = 
   | Var      MSVar 
   | Cond     MSTerm 
   | LetRec   MSVarSubst
   | Let List (MSPattern * MSTerm)

 type Gamma = List Decl * TyVars * Spec * String * StringSet.Set

 type RewriteRule = 
   { 
	name      : String,
        rule_spec : RuleSpec,
        opt_proof : Option Proof,
        % README: opt_proof is a proof of a predicate of the form
        %
        % fa (x1,...,xn) condition' => lhs' = rhs'
        %
        % for some MSVars x1,...,xn, where "condition' =>" is dropped
        % when condition=None. The terms contiion', lhs', and rhs' are
        % the result of substituting the variables x1,...,xn for the
        % flex variables listed in freeVars in the condition, lhs, and
        % rhs of the rule.
        sym_proof : Bool,
        % If sym_proof = true, then the proof predicate is backwards,
        % i.e., proves ... => rhs' = lhs'. Thus, when using the proof,
        % prove_equalSym should be applied after type substitution,
        % forall elimination, and cut
	lhs       : MSTerm,
	rhs       : MSTerm, 
	tyVars    : List String,
	freeVars  : List (Nat * MSType),
	condition : Option MSTerm,
        trans_fn  : Option(TypedFun)
   } 


%%
%% Replace this by discrimination tree based rewrite rule application.
%%

 type RewriteRules = 
      {unconditional : List RewriteRule,
       conditional   : List RewriteRule} 

 op splitConditionalRules(rls: List RewriteRule): RewriteRules =
   {unconditional = filter (fn rl -> none? rl.condition) rls,
    conditional   = filter (fn rl -> some? rl.condition) rls}

%%
%% freshRule generates fresh variable names in a rule for
%% type and individual variables.
%% freshRule is only relevant when matching against non-ground terms.
%%

op freshRuleElements(context: Context, tyVars: List TyVar, freeVars: List (Nat * MSType), name: Id)
   : (MSTerm -> MSTerm) * (MSType -> MSType) * List(Nat * MSType) * StringMap.Map TyVar * TSP_Maps_St = 
     %% tyVMap = {| name -> a | name in tyVars ... |}
     let tyVMap = foldr (fn (name,tyVMap) -> 
                           let num = ! context.counter in
                           let a = "'a%"^Nat.show num in
                           (context.counter := num + 1;
                            StringMap.insert(tyVMap,name,a)))
	            StringMap.empty tyVars
     in
     let
	 def doType(srt: MSType): MSType = 
	     case srt
	       of TyVar(v,a) -> 
		  (case StringMap.find(tyVMap,v)
		     of Some w -> TyVar(w,a)
		      | None -> TyVar(v,a)) 
		%% Unabstracted type variables are treated as rigid
		| _ -> srt
	 def freshType srt = 
	     mapType(id,doType,id) srt
     in
     %% varMap = {| num -> (num1,srt) | (num,srt) in freeVars && num1 = ... |}
     let var_alist = map (fn (num,srt) ->
                            let num1 = ! context.counter in
                            (context.counter := num1 + 1;
                             (num,(num1,freshType srt)))) freeVars in
     let varMap = NatMap.fromList var_alist in
     let
	 def doType(srt: MSType): MSType = 
	     case srt
	       of TyVar(v,a) -> 
		  (case StringMap.find(tyVMap,v)
		     of Some w -> TyVar(w,a)
		      | None -> TyVar(v,a)) 
		%% Unabstracted type variables are treated as rigid
		| _ -> srt
	 def doTerm(term: MSTerm): MSTerm = 
	     case flexVarNum(term)
	       of Some n -> 
		  (case NatMap.find(varMap,n)
		     of Some x -> mkVar x
		      | None ->
                        if context.allowUnboundVars?   % Maybe temporary
                          then term
                          else System.fail ("freshRule: "^show n^" not found in "^name))
		| None -> term
	 def freshTerm trm = 
	     mapTerm(doTerm, doType, id) trm
	 def freshType srt = 
	     mapType(doTerm,doType,id) srt
     in
	(freshTerm, freshType, List.map (fn (_,var) -> var) var_alist, tyVMap, (doTerm, doType, id))

 op freshRule(context: Context, rule as {name,rule_spec,opt_proof,sym_proof,lhs,rhs,condition,freeVars,tyVars,trans_fn}: RewriteRule)
     : RewriteRule =
     % let _ = (writeLine("freshRule: "); printRule rule) in
     let (freshTerm,freshType,freeVars',tyVMap,tsp) = 
	 freshRuleElements(context,tyVars,freeVars,name) in
     rule << {lhs  = freshTerm lhs,
              rhs  = freshTerm rhs,
              condition = (case condition of None -> None | Some c -> Some(freshTerm c)),
              freeVars = freeVars',
              tyVars = StringMap.listItems tyVMap,
              trans_fn = None,
              opt_proof = mapOption (mapProof "freshRule" tsp ) opt_proof
              }


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Extract rewrite rules from function definition.

 op defRule (context: Context, q: String, id: String, rule_spec: RuleSpec,
             info : OpInfo, includeAll?: Bool): List RewriteRule =
   if definedOpInfo? info then
     let qid = Qualified (q, id) in
     let (tvs, srt, term) = unpackFirstRealTerm info.dfn in
     let rule = 
         {name      = id,
          rule_spec = rule_spec,
          opt_proof = None,
          sym_proof = false,
	  lhs       = Fun (Op (qid, info.fixity), srt, noPos),
	  rhs       = term,
	  condition = None,
	  freeVars  = [],
	  tyVars    = tvs,
          trans_fn   = None}
     in
     let rules = deleteLambdaFromRule context includeAll? ([rule], if includeAll? then [rule] else []) in
     % add unfolding proofs to each of these rules (which should
     % presumably hold by unfolding qid).
     let rules =
       map (fn rule ->
              % Instantiate all the flex vars in the lhs and rhs with
              % regular vars, in order to call prove_equalUnfold
              let def mkVari (i, tp) = ("x"^show i, tp) in
              let var_map =
                map (fn (i, tp) -> (i, MS.mkVar (mkVari (i,tp)))) rule.freeVars
              in
              let subst = buildTermSubstC var_map in
              let vars = map mkVari rule.freeVars in
              let typ = inferType (context.spc, rule.lhs) in
              rule << { opt_proof =
                         Some (prove_equalUnfold
                                 (typ, qid, vars,
                                  dereferenceAll subst rule.lhs,
                                  dereferenceAll subst rule.rhs)) }) rules
     in       
     % let _ = app printRule rules in
     rules
   else
     []

%% lhs = fn x -> body -->  lhs x = body
%% Move lambda binding from right to left hand side,
%% assuming that the matches are disjoint (that is, can be
%% applied as rewrite rules without ambiguity).
%% If this is not possible, return the empty list of
%% rules, disabling the further use of the rule.
%%
 op equalToArg?(tm: MSTerm, apply_tm: MSTerm): Bool =
   case apply_tm of
     | Apply(_, arg_tm, _) -> equalTerm?(tm, arg_tm)
     | _ -> false

 op equalToSomeArg?(tm: MSTerm, apply_tm: MSTerm): Bool =
   case apply_tm of
     | Apply(fn_tm, arg_tm, _) ->
       equalTerm?(tm, arg_tm)
         || equalToSomeArg?(tm, arg_tm)
         || equalToSomeArg?(tm, fn_tm)   % For curried args
     | Record(flds, _ ) ->
       exists? (fn (_,fld) -> equalTerm?(tm, fld)) flds
     | _ -> false

 op replaceArg(old_tm: MSTerm, new_tm, apply_tm: MSTerm): MSTerm =
   if equalTerm?(old_tm, apply_tm) then new_tm
   else
   case apply_tm of
     | Apply(fn_tm, arg_tm, _) ->
       mkApply(replaceArg(old_tm, new_tm, fn_tm), replaceArg(old_tm, new_tm, arg_tm))
     | Record(flds, _ ) ->
       mkRecord (map (fn (id,fld) -> (id, replaceArg(old_tm, new_tm, fld))) flds)
     | _ -> apply_tm

 % Convert rules of the form (fn x -> M1) = (fn x -> M2) to M1 =
 % M2. The input pair of lists of rewrite rules are (rules that have
 % yet to be processed, rules that have been processed already)
 op deleteLambdaFromRule (context: Context) (includeAll?: Bool)
     : List RewriteRule * List RewriteRule -> List RewriteRule = 
     fn ([], old) -> old
      | (rule::rules, old) ->
        (case rule.rhs
           of Lambda(matches, _) | disjointMatches matches ->
              let new_rule = freshRule(context, rule) in
              deleteMatches(context, matches, None, rule, rules,
                            if includeAll? then new_rule::old else old,
                            includeAll?) 
            | Apply(Lambda(matches, _), case_tm, _)    % As above with implicit eta
                | equalToSomeArg?(case_tm, rule.lhs) && disjointMatches matches
                    && ~(exists? (fn (_,_,rhs) -> existsSubTerm (fn s_tm -> equalTerm?(s_tm, case_tm)) rhs) matches)->
              let new_rule = freshRule(context, rule) in
              deleteMatches(context, matches, Some case_tm, rule, rules,
                            if includeAll? then new_rule::old else old,
                            includeAll?) 
            | IfThenElse(p, q, r, _) ->
              let new_rule = freshRule(context, rule) in
              let p_rule = rule << {condition = addToCondition(rule.condition,p),
                                    rhs = q} in
              let not_p_rule = rule << {condition = addToCondition(rule.condition,negate p),
                                        rhs = r} in
              deleteLambdaFromRule context includeAll?
                (p_rule :: not_p_rule :: rules, if includeAll? then new_rule::old else old)
	    | _ ->
              let new_rule = freshRule(context, rule) in
              deleteLambdaFromRule context includeAll? (rules, new_rule::old))

 % Used by deleteLambdaFromRule...
 op deleteMatches(context: Context, matches: MSMatch, opt_case_tm: Option MSTerm,
                  rule: RewriteRule, rules: List RewriteRule,
                  old: List RewriteRule, includeAll?: Bool)
     : List RewriteRule = 
     case matches
       of [] -> deleteLambdaFromRule context includeAll? (rules,old)
	| (pat,cond,body)::r_matches ->
     % let _ = writeLine("deleteMatches: "^printPattern pat) in
     case patternToTerm(context,pat,[],[])
       of None -> []
        | Some (patternTerm,vars,S) ->
          % let _ = writeLine("patternTerm: "^printTerm patternTerm) in
          let cond : MSTerm = Utilities.substitute(cond : MSTerm,S) in
          let body = substitute(body,S) in
          let rule1 = rule << {lhs  = case opt_case_tm of
                                        | Some case_tm -> replaceArg(case_tm, patternTerm, rule.lhs)
                                        | None -> mkApply(rule.lhs, patternTerm),
                               rhs  = body,
                               condition = addToCondition(rule.condition,cond),
                               freeVars = rule.freeVars ++ vars,
                               trans_fn = None}
          in
          deleteMatches(context, r_matches, opt_case_tm, rule, rule1::rules, old, includeAll?)

 def addToCondition(condition : Option MSTerm,cond:MSTerm):Option MSTerm = 
     case (condition,cond)
       of (_,Fun(Bool true,_,_)) -> condition
        | (None,_) -> Some cond
	| (Some cond1,_) -> Some (Utilities.mkAnd(cond1,cond))

 type PatternToTermOut =  Option (MSTerm * List (Nat * MSType) * MSVarSubst)

 op patternToTerm : Context * MSPattern * List (Nat * MSType) * MSVarSubst -> PatternToTermOut

 def patternToTerm(context,pat,vars,S) = 
     case pat
       of EmbedPat(con,None,srt,a) -> 
          Some(Fun(Op(con, Constructor0),srt,a),vars,S)
        | EmbedPat(con,Some p,srt,a) -> 
          (case patternToTerm(context,p,vars,S)
             of None -> None
	      | Some (trm,vars,S) -> 
		let srt1 = patternType p in
		Some (Apply(Fun(Op(con, Constructor1),Arrow(srt1,srt,a),a),trm,a),vars,S))
        | RecordPat(fields,a) -> 
	  let
	     def loop(new,old,vars,S):PatternToTermOut = 
	         case new
                   of [] -> Some(Record(reverse old,a),vars,S)
	            | (l,p)::new -> 
	         case patternToTerm(context,p,vars,S)
	           of None -> None
	            | Some(trm,vars,S) -> 
	              loop(new,Cons((l,trm),old),vars,S)
          in
          loop(fields,[],vars,S)
        | NatPat(i, _) -> Some(mkNat i,vars,S)
        | BoolPat(b, _) -> Some(mkBool b,vars,S)
        | StringPat(s, _) -> Some(mkString s,vars,S)
        | CharPat(c, _) -> Some(mkChar c,vars,S)
        | VarPat((v,srt), _) -> 
	  let num = ! context.counter in
          let w = HigherOrderMatching.freshVar(context,srt)     in
          Some(w,Cons((num,srt),vars),Cons(((v,srt),w),S))
        | WildPat(srt,_) -> 
	  let num = ! context.counter in
          let w = HigherOrderMatching.freshVar(context,srt)     in
          Some(w,Cons((num,srt),vars),S)
        | QuotientPat(pat,cond,_,_)  -> None %% Not implemented
        | RestrictedPat(pat,cond,_)  -> patternToTerm(context,pat,vars,S) %% Not implemented
	| AliasPat(VarPat(v, _),p,_) -> 
	  (case patternToTerm(context,p,vars,S) 
             of None -> None
	      | Some(trm,vars,S) -> 
	        Some(trm,vars,(v,trm)::S))
	| AliasPat _ -> None %% Not supported
	   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Extract rewrite rules from a specification.

 op specRules (context: Context) (spc: Spec): RewriteRules = 
     let spc      = normalizeSpec spc in
     let axmRules = flatten (map (fn p -> axiomRules context p Either None) (allProperties spc)) in
     let opRules  = foldriAQualifierMap
                      (fn (q,id,opinfo,val) ->
		        (defRule (context,q,id,Rewrite(Qualified(q,id)),opinfo,false)) ++ val)
		      [] spc.ops
     in
     let rules = axmRules ++ opRules in
     let rules = map (etaExpand context) rules in
     let rules = prioritizeRules(rules)  in
     rules


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
(*
Eta-expand rewrite rules, such that a matching equality:
\[
	(M x) = N\ \ \ \ \ \ \ x \not\in FV(M)
\]
is rewritten to
\[
	M = \lambda x \ . \ N\enspace .
\]
*)

  op  etaExpand:  Context -> RewriteRule -> RewriteRule
  def etaExpand (* context *)_ rule = rule

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def prioritizeRules(rules) = 
     let
	def loop(rules,uncond,cond) = 
	    case rules
	      of [] -> {unconditional = uncond,conditional = cond}
	       | rule::rules -> 
	    case redirectRule rule 
	      of None -> loop(rules,uncond,cond)
	       | Some rule -> 
	    case rule.condition
	      of None -> loop(rules,Cons(rule,uncond),cond)
	       | Some _ -> loop(rules,uncond,Cons(rule,cond))
     in
     loop(rules,[],[])


%%
%% Simple primitive pruning mechanism for deleting 
%% rewrite rules that obviously lead to diverging behaviour.
%%    

  def isFlexibleTerm(term:MSTerm) = 
      if isFlexVar?(term) then true else
        (case term
           of Apply(M,N,_) -> isFlexibleTerm(M)
            | Record(fields, _) -> forall? (fn (_,M) -> isFlexibleTerm M) fields
            | _ -> false)

  def deleteFlexTail(term:MSTerm) = 
      case term 
        of Apply(M,N,_) -> 
	   if isFlexibleTerm N
		then deleteFlexTail M
	   else term
	 | term -> term

  def diverging(lhs,rhs) = 
      let lhs = deleteFlexTail lhs in
      existsSubTerm (fn term -> lhs = term) rhs

  op  redirectRule : RewriteRule -> Option RewriteRule
  def redirectRule (rule as {name,lhs,rhs,rule_spec,opt_proof,sym_proof,tyVars,freeVars,condition,trans_fn}) = 
      if diverging(lhs,rhs)
	 then 
	 if diverging(rhs,lhs)
	     then None
	 else Some {name = name, rule_spec = reverseRuleSpec rule_spec,
                    opt_proof = opt_proof, sym_proof = ~sym_proof,
                    lhs = rhs, rhs = lhs,
                    tyVars = tyVars, freeVars = freeVars,
                    condition = condition, trans_fn = trans_fn}
      else Some rule

 %% If term is a qf binder then Introduce a number for each Var and return:
 %% 1. a list of the numbers paired with the type
 %% 2. the number of variables introduced
 %% 3. A substitution mapping old Var to new flex var with that number
 %% 4. The body of the binder (handles nested binders of the same type)
 op bound(qf: Binder, n: Nat, term: MSTerm, freeVars: List(Nat * MSType),
          S: MSVarSubst)
    : List (Nat * MSType) * Nat * MSVarSubst * MSTerm =
   case term
     of Bind(binder,vars,body,_) -> 
        if qf = binder
           then 
           let (new_freeVars,S,n) =
               foldr (fn ((x,srt),(freeVars,S,n)) -> 
                        let y = mkVar(n,srt) in
                        (Cons((n,srt),freeVars),
                         Cons(((x,srt),y),S),n + 1))
                 ([],S,n) vars
           in
           bound(qf,n,body,freeVars++new_freeVars,S)
        else (freeVars,n,S,term)
      | _ -> (freeVars,n,S,term)

% Disambiguate between HigerOrderMatchingMetaSlang and MetaSlang
  def mkVar = HigherOrderMatching.mkVar     

  op equality : Context -> MSVarSubst * MSTerm -> Option (MSTerm * MSTerm)

  def equality context (S,N)  = 
      case N
        of Apply(Fun(Equals,_,_),Record([(_,N1),(_,N2)], _),_) -> 
  	   Some (substitute(N1,S),substitute(N2,S))
	 | Bind(Forall,vars,N,_) -> 
	   let S1 = map (fn (v,s) -> ((v,s),mkVar(freshBoundVar(context,s)))) vars in
           let N = substitute(N,S1) in
           equality context (S,N)
         | _ -> None
 
op simpleRwTerm?(t: MSTerm): Bool =
   case t of
     | Var _ -> true
     | Fun _ -> true
     | Apply(Fun(Project _,_,_),a1,_) -> simpleRwTerm? a1
     | _ -> false

 op hasUnboundVars?(new_term: MSTerm, match_term: MSTerm, opt_condn: Option MSTerm, subst: MSVarSubst): Bool =
   let boundVars = freeVarsAll match_term in
   let boundVars =  case opt_condn of
                      | None -> boundVars
                      | Some condn -> freeVars condn ++ boundVars
   in
   exists? (fn v -> ~(inVars?(v, boundVars)) && exists? (fn (fv, _) -> equalVar?(fv, v)) subst) (freeVars new_term)

 op expandIfThenElse?: Bool = false

 type Direction = | LeftToRight | RightToLeft | Either

 op compatibleDirection?(e1: MSTerm, e2: MSTerm, condition: Option MSTerm, lr?: Bool, dirn: Direction,
                         allowUnboundVars?: Bool, subst: MSVarSubst): Bool =
   case dirn of
     | LeftToRight ->  lr? && (allowUnboundVars? || ~(hasUnboundVars?(e2, e1, condition, subst)))
     | RightToLeft -> ~lr? && (allowUnboundVars? || ~(hasUnboundVars?(e1, e2, condition, subst)))
     | Either -> if lr? then    % constantTerm? e2 &&
                           (allowUnboundVars? || ~(hasUnboundVars?(e2, e1, condition, subst)))
                  else simpleRwTerm? e1 && ~(varTerm? e2)
                    && (allowUnboundVars? || ~(hasUnboundVars?(e1, e2, condition, subst)))

 op contextRuleDirection(rs: RuleSpec): Option Direction =
   case rs of
     | LeftToRight _ -> Some LeftToRight
     | RightToLeft _ -> Some RightToLeft
     | _ -> None

 op assertRules (context: Context, term: MSTerm, desc: String, rsp: RuleSpec, dirn: Direction, o_prf: Option Proof, tyvars: TyVars)
      : List RewriteRule =
   %% lr? true means that there is an explicit lr orientation, otherwise we orient equality only if obvious
   let rules = assertRulesRec(context, term, desc, rsp, dirn, o_prf, tyvars, [], [], None, false) in
   % let _ = app printRule rules in
   rules

 op assertRulesRec (context   : Context,
                    term      : MSTerm, 
                    desc      : String, 
                    rsp       : RuleSpec, 
                    dirn      : Direction,
                    o_prf     : Option Proof,
                    tyvars    : TyVars,
                    free_vs  : List (Nat * MSType), 
                    subst     : MSVarSubst, 
                    condition : Option MSTerm,
                    subterm?  : Bool)   % If we are at a subterm of the original theorem
   : List RewriteRule =
   % let _ = writeLine("assertRules "^anyToString dirn^" "^desc^":\n"^printTerm term) in
   let (fvs,n,S,formula) = bound(Forall,0,term,[],[]) in
   let free_vs = fvs ++ free_vs in
   let subst = S ++ subst in
   let (condn,fml) = 
	case formula of
	  | Apply(Fun(Implies, _,_), Record([(_,M),(_,N)], _),_) -> 
            (Some (substitute(M,subst)),N)
	  | _ -> (None,formula)
   in
   let condition = case condition of
                     | None -> condn
                     | Some c1 ->
                   case condn of
                     | None -> condition
                     | Some c2 -> Some(Utilities.mkAnd (c1,c2))
   in
   let def equalityRules(e1: MSTerm, e2: MSTerm, lr?: Bool, o_prf: Option Proof): List RewriteRule =
         case e1 of
           | Apply(Fun(Not, _,_), p,_) ->
             let n_e2 = negate e2 in
             equalityRules0(p, n_e2, lr?,
                            mapOption (replaceProofTerm (mkEquality(boolType, p, n_e2)))
                              o_prf)
               ++ equalityRules0(e1, e2, lr?, o_prf)
           | _ -> equalityRules0(e1, e2, lr?, o_prf)
             
       def equalityRules0(e1: MSTerm, e2: MSTerm, lr?: Bool, o_prf: Option Proof): List RewriteRule =
         let (lhs, rhs) = if lr? then (e1, e2) else (e2, e1) in
         let lhs_ty = inferType(context.spc, lhs) in
         let o_prf = if subterm? then mapOption (extendProofAuto (mkEquality(lhs_ty, lhs, rhs))) o_prf else o_prf in
         let s_lhs = substitute(lhs,subst) in
         let s_rhs = substitute(rhs,subst) in
         let main_rule = freshRule(context,
                                   {name      = desc,   condition = condition, rule_spec = rsp,
                                    opt_proof = o_prf,  sym_proof = ~lr?,
                                    lhs       = s_lhs,  rhs       = s_rhs,
                                    tyVars    = tyvars, freeVars  = free_vs,
                                    trans_fn = None})
         in
         case e2 of
           | IfThenElse(p, q, r, _) | expandIfThenElse? ->
             (if lr? || ~(hasUnboundVars?(q, e1, condition, subst))
                then [freshRule(context, {name      = desc,   condition = addCondn p, rule_spec = rsp,
                                          opt_proof = o_prf,  sym_proof = ~lr?,
                                          lhs       = if lr? then s_lhs else substitute(q,subst),
                                          rhs       = if lr? then substitute(q,subst) else s_rhs,
                                          tyVars    = tyvars, freeVars  = free_vs, trans_fn = None})]
                else [])
             ++ (if lr? || ~(hasUnboundVars?(r, e1, condition, subst))
                then [freshRule(context, {name      = desc,   condition = addCondn(negate p), rule_spec = rsp,
                                          opt_proof = o_prf,  sym_proof = ~lr?,
                                          lhs       = if lr? then s_lhs else substitute(r,subst),
                                          rhs       = if lr? then substitute(r,subst) else s_rhs,
                                          tyVars    = tyvars, freeVars  = free_vs, trans_fn = None})]
                else [])
             ++ [main_rule]
           | _ -> [main_rule]
       def addCondn(p: MSTerm): Option MSTerm =
         case condition of
           | None -> Some p
           | Some c1 -> Some(Utilities.mkAnd(c1, p))
   in
   case fml of
     % | Apply(Fun(Not, _,_), Apply(Fun(Not, _,_), p,_),_) ->
     %   assertRulesRec(context,p,desc,rsp,dirn,o_prf,tyvars,free_vs,subst,condition)
     | Apply(Fun(Not, _,_), p,_) ->
       if falseTerm? p then []
	else
        [freshRule(context,
		   {name      = desc,   condition = condition, rule_spec = rsp,
                    opt_proof = o_prf,   sym_proof = false,
		    lhs       = substitute(fml,subst), rhs       = trueTerm,
		    tyVars    = [],     freeVars  = free_vs, trans_fn = None}),
         freshRule(context,
		   {name      = desc,   condition = condition, rule_spec = rsp,
                    opt_proof = o_prf,   sym_proof = false,
		    lhs       = substitute(p,subst),      rhs       = falseTerm,
		    tyVars    = [],     freeVars  = free_vs, trans_fn = None})]
     | Apply(Fun(Equals,_,_),Record([(_,e1),(_,e2)], _),_)
         | compatibleDirection?(e1, e2, condition, true, dirn, context.allowUnboundVars?, subst) ->
       equalityRules(e1, e2, true, o_prf)
     | Apply(Fun(Equals,_,_),Record([(_,e1),(_,e2)], _),_)
         | compatibleDirection?(e1, e2, condition, false, dirn, context.allowUnboundVars?, subst) ->
       equalityRules(e1, e2, false, o_prf)
     | Apply(Fun(And,_,_),Record([(_,e1),(_,e2)], _),_) ->
       assertRulesRec(context,e1,desc^"-1",rsp,dirn,o_prf,tyvars,free_vs,subst,condition, true)
         ++ assertRulesRec(context,e2,desc^"-2",rsp,dirn,o_prf,tyvars,free_vs,subst,condition, true)
     | Let([(VarPat(v,_),val)],body,pos) ->
       assertRulesRec(context,substitute(body,[(v,val)]),desc,rsp,dirn,o_prf,tyvars,free_vs,subst,condition, subterm?)
     | _ ->
       if trueTerm? fml then []
       else
         let o_prf = if subterm? then mapOption (extendProofAuto (mkEquality(boolType, fml, trueTerm))) o_prf else o_prf in
         let lhs = substitute(fml,subst) in
         [freshRule(context,
                    {name      = desc,   condition = condition, rule_spec = rsp,
                     opt_proof = o_prf,  sym_proof = false,
                     lhs       = lhs,    rhs       = trueTerm,
                     tyVars    = tyvars, freeVars  = free_vs, trans_fn = None})]

 op axiomRules (context: Context) ((pt,desc,tyVars,formula,a): Property) (dirn: Direction) (o_prf: Option Proof)
      : List RewriteRule = 
%      case pt
%        of Conjecture -> []
%  	| _ ->
   assertRules(context, formula, printQualifiedId desc,
               case dirn of RightToLeft -> RightToLeft desc | _ -> LeftToRight desc,
               dirn, o_prf, tyVars)

%  op axiomRule (context: Context) ((pt,desc,tyVars,formula,a): Property): Option RewriteRule = 
% %      case pt
% %        of Conjecture -> None
% % 	| _ -> 
%      let freeVars = [] in
%      let (freeVars,n,S,formula) = bound(Forall,0,formula,freeVars,[]) in
%      let (condition,fml) = 
% 	  case formula of 
%             | Apply(Fun(Implies,_,_), Record([(_,M),(_,N)], _),_) -> 
% 		(Some (substitute(M,S)), N)
% 	    | _ -> (None, formula)
%      in
%      case equality context (S,fml)
%        of Some(N1,N2) -> 
%           Some (freshRule(context,
% 		 {name      = printQualifiedId(desc),   condition = condition,
% 		  lhs       = N1,     rhs       = N2,
%   	          tyVars    = tyVars, freeVars  = freeVars}))
% 	| None -> None

 op printRule({name,tyVars,freeVars,condition,lhs,rhs,rule_spec,opt_proof,sym_proof,trans_fn}:RewriteRule): () = 
     ( writeLine ("Rewrite rule ------- "^name^" -------");
       if some? trans_fn then ()
       else
       (app (fn tv -> toScreen(tv^" ")) tyVars;
        if empty? tyVars then () else writeLine "";
        app (fn (n,srt) -> toScreen(show n^" : " ^ printType srt^" "))
          freeVars;
        if empty? freeVars then () else writeLine "";
        (case condition 
           of Some c -> (writeLine(printTerm c)) 
            | None -> ());
        writeLine ("Rewrite : "^printTerm lhs^ " ---> "^
                     printTerm rhs));
       case opt_proof of
         | Some prf -> writeLine(printProof prf)
         | None -> ()
     )	


%%
%% Ignores name capture:
%%
%% axiom p  add rule p -> true
%% axiom ~p add rule p -> false

 %%% sjw: This doesn't seem to be used
 def rulesFromGamma (context: Context) (gamma: Gamma): RewriteRules = 
     let (ds,tvs,env,name,names) = gamma in
     let subst0 = HigherOrderMatching.emptySubstitution in
     let
	 def loop(d,rules) = 
	     case d
	       of Cond c -> 
		  let c = HigherOrderMatching.dereferenceAll subst0 c in
		  (case axiomRules context
		         (Axiom,
			  mkUnQualifiedId("Context-condition: "^printTerm c),tvs,c,noPos)
                         Either None
		     of new_rules as (_::_) -> new_rules ++ rules
		      | [] ->
		   let rules
		        = (axiomRules context
				(Axiom:PropertyType,
				 mkUnQualifiedId("Context-condition: " ^printTerm c),
				 tvs, mkEquality(boolType,c,trueTerm),noPos)
                                Either None)
			    ++ rules
		   in 
		   case c of
		     | Apply(Fun(Not,_,_), nc,_) -> 
		       (axiomRules context
			  (Axiom,
			   mkUnQualifiedId("Context-condition: " ^printTerm nc
			   ^" = false"),
			   tvs, mkEquality(boolType,nc,falseTerm),noPos)
                          Either None)
			++ rules
		     | _ -> rules)
		| _ -> rules
     in
     let rules = foldr loop [] ds in
     let rules = prioritizeRules(rules)  in
     rules

  op  mergeRules : List RewriteRules -> RewriteRules
  def mergeRules = 
     fn [] -> {unconditional = [],conditional = []}
      | [rules] -> rules
      | rules1::rules2::rules -> 
        let rules1 = {unconditional = rules1.unconditional ++ rules2.unconditional,
		        conditional = rules1.conditional ++ rules2.conditional}
	in
	mergeRules(Cons(rules1,rules))

end-spec

