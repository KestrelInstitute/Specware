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
 % import ../AbstractSyntax/PathTerm

 type Context = HigherOrderMatching.Context

 type Decl  = 
   | Var Var 
   | Cond MSTerm 
   | LetRec List (Var * MSTerm) 
   | Let List (MSPattern * MSTerm)

 type Gamma = List Decl * TyVars * Spec * String * StringSet.Set

 type RewriteRule = 
   { 
	name      : String,
        rule_spec : RuleSpec,
	lhs       : MSTerm,
	rhs       : MSTerm, 
	tyVars    : List String,
	freeVars  : List (Nat * MSType),
	condition : Option MSTerm,
        trans_fn   : Option(MSTerm -> Option MSTerm)
   } 

 op showRuleSpec(rs: RuleSpec): String =
   case rs of
     | Unfold  qid -> "unfold " ^ show qid
     | Fold    qid -> "fold " ^ show qid
     | Rewrite qid -> "rewrite " ^ show qid
     | LeftToRight qid -> "lr " ^ show qid
     | RightToLeft qid -> "rl " ^ show qid
     | MetaRule    qid -> "apply " ^ show qid
     | RLeibniz    qid -> "rev-leibniz " ^ show qid
     | Weaken      qid -> "weaken " ^ show qid
     | MetaRule      qid -> "meta-rule " ^ show qid
     | Eval -> "eval"
     | Context -> "context"
     | AllDefs -> "alldefs"

 op reverseRuleSpec(rs: RuleSpec): RuleSpec =
   case rs of
     | Unfold qid -> Fold qid
     | Fold qid -> Unfold qid
     | Rewrite qid -> Fold qid
     | LeftToRight qid -> RightToLeft qid
     | RightToLeft qid -> LeftToRight qid
     | _ -> (warn("Trying to reverse rule "^showRuleSpec rs))

 op printTransformHistory(hist: TransformHistory): () =
   if hist = [] then ()
   else
   (writeLine("Transformation History:");
    % let changed_terms = tabulate(length hist - 1,
    %                              fn i -> let (t1, t2) = ((hist@i).1, (hist@(i+1)).1) in
    %                                      let (_, path) = changedPathTerm(t1, t2) in
    %                                      (fromPathTerm(t1, path), fromPathTerm(t2, path)))
    % in
    (app (fn (tm, rs) -> (writeLine(showRuleSpec rs);
                         writeLine(printTerm tm)))
      hist
    %; app (fn (t1, t2) -> writeLine(printTerm t1^" --> "^printTerm t2)) changed_terms
     ))

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

op freshRuleElements(context: Context, tyVars: List TyVar, freeVars: List (Nat * MSType))
   : (MSTerm -> MSTerm) * (MSType -> MSType) * NatMap.Map(Nat * MSType) * StringMap.Map TyVar = 
% tyVMap = {| name -> a | name in tyVars ... |}
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
	     mapType((fn M -> M),doType,fn p -> p) srt
     in
% varMap = {| num -> (num1,srt) | (num,srt) in freeVars & num1 = ... |}
     let varMap = 
	 foldr (fn ((num,srt), varMap) -> 
                  let num1 = ! context.counter in
                  (context.counter := num1 + 1;
                   NatMap.insert(varMap,num,(num1,freshType srt))))
	   NatMap.empty freeVars	
     in
     let
	 def doTerm(term: MSTerm): MSTerm = 
	     case isFlexVar?(term)
	       of Some n -> 
		  (case NatMap.find(varMap,n)
		     of Some x -> mkVar x
		      | None -> System.fail (show n^" not found"))
		| None -> term
	 def freshTerm trm = 
	     mapTerm(doTerm, doType, id) trm
     in
	(freshTerm, freshType, varMap, tyVMap)

 def freshRule(context: Context, {name,rule_spec,lhs,rhs,condition,freeVars,tyVars,trans_fn}: RewriteRule)
     : RewriteRule = 
     let (freshTerm,freshType,varMap,tyVMap) = 
	 freshRuleElements(context,tyVars,freeVars) in
     {  name = name,
        rule_spec = rule_spec,
	lhs  = freshTerm lhs,
	rhs  = freshTerm rhs,
	condition = (case condition of None -> None | Some c -> Some(freshTerm c)),
	freeVars = NatMap.listItems varMap,
	tyVars = StringMap.listItems tyVMap,
        trans_fn = None
     }


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Extract rewrite rules from function definition.

 op defRule (context: Context, q: String, id: String, rule_spec: RuleSpec, info : OpInfo, includeAll?: Bool): List RewriteRule = 
   if definedOpInfo? info then
     let (tvs, srt, term) = unpackFirstTerm info.dfn in
     let rule = 
         {name      = id,
          rule_spec = rule_spec,
	  lhs       = Fun (Op (Qualified (q, id), info.fixity), srt, noPos),
	  rhs       = term,
	  condition = None,
	  freeVars  = [],	
	  tyVars    = tvs,
          trans_fn   = None}
     in
     let rules = deleteLambdaFromRule context includeAll? ([rule], if includeAll? then [rule] else []) in
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

 op deleteLambdaFromRule (context: Context) (includeAll?: Bool)
     : List RewriteRule * List RewriteRule -> List RewriteRule = 
     fn ([], old) -> old
      | (rule::rules, old) ->
        % let _ = writeLine("del_lam: "^printTerm rule.rhs) in
        (case rule.rhs
           of Lambda(matches, _) | disjointMatches matches ->
              let new_rule = freshRule(context, rule) in
              deleteMatches(context, matches, None, rule, rules,
                            if includeAll? then new_rule::old else old,
                            includeAll?) 
            | Apply(Lambda(matches, _), case_tm, _)    % As above with implicit eta
                | equalToSomeArg?(case_tm, rule.lhs) && disjointMatches matches ->
              % let Apply(hd, _, _) = rule.lhs in
              % let rule = rule << {lhs = hd} in
              let new_rule = freshRule(context, rule) in
              deleteMatches(context, matches, Some case_tm, rule, rules,
                            if includeAll? then new_rule::old else old,
                            includeAll?) 
	    | _ ->
              let new_rule = freshRule(context, rule) in
              deleteLambdaFromRule context includeAll? (rules, new_rule::old))

 op deleteMatches(context: Context, matches: Match, opt_case_tm: Option MSTerm,
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
          let cond = substitute(cond,S) in
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

 type PatternToTermOut =  Option (MSTerm * List (Nat * MSType) * List (Var * MSTerm))

 op patternToTerm : Context * MSPattern * List (Nat * MSType) * List (Var * MSTerm) -> PatternToTermOut

 def patternToTerm(context,pat,vars,S) = 
     case pat
       of EmbedPat(con,None,srt,a) -> 
          Some(Fun(Embed(con,false),srt,a),vars,S)
        | EmbedPat(con,Some p,srt,a) -> 
          (case patternToTerm(context,p,vars,S)
             of None -> None
	      | Some (trm,vars,S) -> 
		let srt1 = patternType p in
		Some (Apply(Fun(Embed(con,true),Arrow(srt1,srt,a),a),trm,a),vars,S))
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
        | QuotientPat(pat,cond,_)  -> None %% Not implemented
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
     let spc      = normalizeSpec spc            in
     let axmRules = flatten (map (axiomRules context) (allProperties spc)) in
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
      case isFlexVar?(term)
        of Some m -> true
	 | None -> 
      case term
        of Apply(M,N,_) -> isFlexibleTerm(M)
	 | Record(fields, _) -> forall? (fn (_,M) -> isFlexibleTerm M) fields
	 | _ -> false

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
  def redirectRule (rule as {name,lhs,rhs,rule_spec,tyVars,freeVars,condition,trans_fn}) = 
      if diverging(lhs,rhs)
	 then 
	 if diverging(rhs,lhs)
	     then None
	 else Some {name = name, rule_spec = reverseRuleSpec rule_spec, lhs = rhs, rhs = lhs,
                    tyVars = tyVars, freeVars = freeVars, condition = condition, trans_fn = trans_fn}
      else Some rule

 %% If term is a qf binder then Introduce a number for each Var and return
 %% a list of the numbers paired with the type
 %% A substitution mapping old Var to new flex var with that number
 %% The body of the binder (handles nested binders of the same type)
 op bound(qf: Binder, n: Nat, term: MSTerm, freeVars: List(Nat * MSType),
          S: List(Var * MSTerm)) 
    : List (Nat * MSType) * Nat * List (Var * MSTerm) * MSTerm =
   case term
     of Bind(binder,vars,body,_) -> 
        if qf = binder
           then 
           let (freeVars,S,n) =
               foldr (fn ((x,srt),(freeVars,S,n)) -> 
                        let y = mkVar(n,srt) in
                        (Cons((n,srt),freeVars),
                         Cons(((x,srt),y),S),n + 1))
                 (freeVars,S,n) vars
           in
           bound(qf,n,body,freeVars,S)
        else (freeVars,n,S,term)
      | _ -> (freeVars,n,S,term)

% Disambiguate between HigerOrderMatchingMetaSlang and MetaSlang
  def mkVar = HigherOrderMatching.mkVar     

  op equality : Context -> List (Var * MSTerm) * MSTerm -> Option (MSTerm * MSTerm)

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

 op assertRules (context: Context, term: MSTerm, desc: String, rsp: RuleSpec, lr?: Bool): List RewriteRule =
   %% lr? true means that there is an explicit lr orientation, otherwise we orient equality only if obvious
   assertRulesRec(context, term, desc, rsp, lr?, [], [], None)

 op assertRulesRec (context: Context, term: MSTerm, desc: String, rsp: RuleSpec, lr?: Bool, freeVars: List (Nat * MSType), 
                    subst: VarSubst, condition: Option MSTerm)
    : List RewriteRule =
   let (fvs,n,S,formula) = bound(Forall,0,term,[],[]) in
   let freeVars = fvs ++ freeVars in
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
   case fml of
     | Apply(Fun(Not, _,_), p,_) ->
       if falseTerm? p then []
	else
        [freshRule(context,
		   {name      = desc,   condition = condition, rule_spec = rsp,
		    lhs       = substitute(p,subst),      rhs       = falseTerm,
		    tyVars    = [],     freeVars  = freeVars, trans_fn = None})]
     | Apply(Fun(Equals,_,_),Record([(_,e1),(_,e2)], _),_) | lr? || constantTerm? e2 ->
       [freshRule(context,
                  {name      = desc,   condition = condition, rule_spec = rsp,
                   lhs       = substitute(e1,subst),     rhs       = substitute(e2,subst),
                   tyVars    = [],     freeVars  = freeVars, trans_fn = None})]
     | Apply(Fun(Equals,_,_),Record([(_,e1),(_,e2)], _),_) | simpleRwTerm? e1 && ~(varTerm? e2)->
       [freshRule(context,
                  {name      = desc,   condition = condition, rule_spec = rsp,
                   lhs       = substitute(e2,subst),     rhs       = substitute(e1,subst),
                   tyVars    = [],     freeVars  = freeVars, trans_fn = None})]
     | Apply(Fun(And,_,_),Record([(_,e1),(_,e2)], _),_) ->
       assertRulesRec(context,e1,desc^"-1",rsp,lr?,freeVars,subst,condition)
         ++ assertRulesRec(context,e2,desc^"-2",rsp,lr?,freeVars,subst,condition)
     | Let([(VarPat(v,_),val)],body,pos) ->
       assertRulesRec(context,substitute(body,[(v,val)]),desc,rsp,lr?,freeVars,subst,condition)
     | _ ->
       if trueTerm? fml then []
       else
         [freshRule(context,
                    {name      = desc,   condition = condition, rule_spec = rsp,
                     lhs       = substitute(fml,subst),    rhs       = trueTerm,
                     tyVars    = [],     freeVars  = freeVars, trans_fn = None})]

 op axiomRules (context: Context) ((pt,desc,tyVars,formula,a): Property): List RewriteRule = 
%      case pt
%        of Conjecture -> []
%  	| _ ->
   assertRules(context, formula, printQualifiedId desc, LeftToRight desc, true)

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

 op printRule({name,tyVars,freeVars,condition,lhs,rhs,rule_spec,trans_fn}:RewriteRule): () = 
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
                     printTerm rhs))
     )	

  def renameBound(term) = 
      let free = freeVars term in
      let free = map (fn (s,_) -> s) free in
      let env0 = StringMap.empty in     
      let env1 = foldr (fn (s,m) -> StringMap.insert(m,s,s)) env0 free in
      let env  = Ref env1 : Ref (StringMap String) in
      let vrs  = Ref (StringSet.fromList(StringMap.listDomain env1)) in
      let 
	  def doVar(x,srt) = 
	      if String.length(x) >= 2 && 
		 x@1 = #%
		 then 
	      (case StringMap.find(! env,x)
		 of Some y -> (y,srt)
		  | None -> 
	       let y = StringUtilities.freshName("x",! vrs) in
	       (vrs := StringSet.add(! vrs,y);
		env := StringMap.insert(! env,x,y);
		(y,srt)))
	      else (x,srt)

	  def doTerm(term:MSTerm):MSTerm = 
	      case term of
		 | Var(v,a) -> Var(doVar v,a)
		 | Bind(qf,vars,body,a) -> Bind(qf,map doVar vars,body,a)
		 | The (var,body,a) -> The (doVar var,body,a)
		 | term -> term
	   def doPat(pat:MSPattern):MSPattern = 
	       case pat
		 of VarPat(v,a) -> VarPat(doVar v,a)
		  | _ -> pat
      in
      mapTerm(doTerm,fn s -> s,doPat) term


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
		     of new_rules as (_::_) -> new_rules ++ rules
		      | [] ->
		   let rules
		        = (axiomRules context
				(Axiom:PropertyType,
				 mkUnQualifiedId("Context-condition: " ^printTerm c),
				 tvs, mkEquality(boolType,c,trueTerm),noPos))
			    ++ rules
		   in 
		   case c of
		     | Apply(Fun(Not,_,_), nc,_) -> 
		       (axiomRules context
			  (Axiom,
			   mkUnQualifiedId("Context-condition: " ^printTerm nc
			   ^" = false"),
			   tvs, mkEquality(boolType,nc,falseTerm),noPos))
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

