(* Conditional rewrite rules

Convert an axiom of the form
\[
   \forall \vec{x} \vec{M} \ = \ \vec{N} \Rightarrow M = N
\]
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

 type Context = HigherOrderMatching.Context

 type Decl  = 
   | Var Var 
   | Cond MS.Term 
   | LetRec List (Var * MS.Term) 
   | Let List (Pattern * MS.Term)

 type Gamma = List Decl * TyVars * Spec * String * StringSet.Set

 type RewriteRule = 
   { 
	name      : String,
	lhs       : MS.Term,
	rhs       : MS.Term, 
	tyVars    : List String,
	freeVars  : List (Nat * Sort),
	condition : Option MS.Term
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

op freshRuleElements(context: Context, tyVars: List TyVar, freeVars: List (Nat * Sort))
   : (MS.Term -> MS.Term) * (Sort -> Sort) * NatMap.Map(Nat * Sort) * StringMap.Map TyVar = 
% tyVMap = {| name -> a | name in tyVars ... |}
     let tyVMap = foldr (fn (name,tyVMap) -> 
                           let num = ! context.counter in
                           let a = "'a%"^Nat.toString num in
                           (context.counter := num + 1;
                            StringMap.insert(tyVMap,name,a)))
	            StringMap.empty tyVars
     in
     let
	 def doSort(srt: Sort): Sort = 
	     case srt
	       of TyVar(v,a) -> 
		  (case StringMap.find(tyVMap,v)
		     of Some w -> TyVar(w,a)
		      | None -> TyVar(v,a)) 
		%% Unabstracted type variables are treated as rigid
		| _ -> srt
	 def freshSort srt = 
	     mapSort((fn M -> M),doSort,fn p -> p) srt
     in
% varMap = {| num -> (num1,srt) | (num,srt) in freeVars & num1 = ... |}
     let varMap = 
	 foldr (fn ((num,srt), varMap) -> 
                  let num1 = ! context.counter in
                  (context.counter := num1 + 1;
                   NatMap.insert(varMap,num,(num1,freshSort srt))))
	   NatMap.empty freeVars	
     in
     let
	 def doTerm(term: MS.Term): MS.Term = 
	     case isFlexVar?(term)
	       of Some n -> 
		  (case NatMap.find(varMap,n)
		     of Some x -> mkVar x
		      | None -> System.fail (toString n^" not found"))
		| None -> term
	 def freshTerm trm = 
	     mapTerm(doTerm, doSort, id) trm
     in
	(freshTerm, freshSort, varMap, tyVMap)

 def freshRule(context: Context, {name,lhs,rhs,condition,freeVars,tyVars}: RewriteRule)
     : RewriteRule = 
     let (freshTerm,freshSort,varMap,tyVMap) = 
	 freshRuleElements(context,tyVars,freeVars) in
     {  name = name,
	lhs  = freshTerm lhs,
	rhs  = freshTerm rhs,
	condition = (case condition of None -> None | Some c -> Some(freshTerm c)),
	freeVars = NatMap.listItems varMap,
	tyVars = StringMap.listItems tyVMap
     }


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Extract rewrite rules from function definition.

 op defRule (context: Context, q: String, id: String, info : OpInfo, includeLambdaRules?: Boolean): List RewriteRule = 
   if definedOpInfo? info then
     let (tvs, srt, term) = unpackFirstOpDef info in
     let rule = 
         {name      = id,
	  lhs       = Fun (Op (Qualified (q, id), info.fixity), srt, noPos),
	  rhs       = term,
	  condition = None,
	  freeVars  = [],	
	  tyVars    = tvs}
     in
       deleteLambdaFromRule context ([rule],if includeLambdaRules? then [rule] else [])
   else
     []

%% lhs = fn x -> body -->  lhs x = body
%% Move lambda binding from right to left hand side,
%% assuming that the matches are disjoint (that is, can be
%% applied as rewrite rules without ambiguity).
%% If this is not possible, return the empty list of
%% rules, disabling the further use of the rule.
%%

 def deleteLambdaFromRule context = 
     fn ([],old) -> old
      | (rule::rules,old) -> 
        (case rule.rhs
           of Lambda(matches, _) ->
	      if disjointMatches matches
		 then
		 deleteMatches(context,matches,rule,rules, Cons(freshRule(context,rule),old)) 
	      else old 
	    | _ -> deleteLambdaFromRule context 
			(rules, Cons(freshRule(context,rule),old)))

 def deleteMatches(context,matches,rule,rules,old) = 
     case matches
       of [] -> deleteLambdaFromRule context (rules,old)
	| (pat,cond,body)::matches -> 
     case patternToTerm(context,pat,[],[])
       of None -> []
        | Some (patternTerm,vars,S) -> 
          let cond = substitute(cond,S) in
          let body = substitute(body,S) in
          let rule1 = 
              { name = rule.name,
                lhs  = Apply(rule.lhs,patternTerm,noPos),
                rhs  = body,
		condition = addToCondition(rule.condition,cond),
		freeVars = rule.freeVars ++ vars,
		tyVars = rule.tyVars
	      }
          in
          deleteMatches(context,matches,
			rule,cons(rule1,rules),old)

 def addToCondition(condition : Option MS.Term,cond:MS.Term):Option MS.Term = 
     case (condition,cond)
       of (_,Fun(Bool true,_,_)) -> condition
        | (None,_) -> Some cond
	| (Some cond1,_) -> Some (Utilities.mkAnd(cond1,cond))

 type PatternToTermOut = 
      Option (MS.Term * List (Nat * Sort) * List (Var * MS.Term))

 op patternToTerm : 
    Context * Pattern * List (Nat * Sort) * List (Var * MS.Term) -> 
       PatternToTermOut

 def patternToTerm(context,pat,vars,S) = 
     case pat
       of EmbedPat(con,None,srt,a) -> 
          Some(Fun(Embed(con,false),srt,a),vars,S)
        | EmbedPat(con,Some p,srt,a) -> 
          (case patternToTerm(context,p,vars,S)
             of None -> None
	      | Some (trm,vars,S) -> 
		let srt1 = patternSort p in
		Some (Apply(Fun(Embed(con,true),Arrow(srt1,srt,a),a),trm,a),vars,S))
        | RecordPat(fields,a) -> 
	  let
	     def loop(new,old,vars,S):PatternToTermOut = 
	         case new
                   of [] -> Some(Record(rev old,a),vars,S)
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
	        Some(trm,vars,cons((v,trm),S)))
	| AliasPat _ -> None %% Not supported
	   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Extract rewrite rules from a specification.

 op specRules (context: Context) (spc: Spec): RewriteRules = 
     let spc      = normalizeSpec spc            in
     let axmRules = flatten (map (axiomRules context) (allProperties spc)) in
     let opRules  = foldriAQualifierMap
                      (fn (q,id,opinfo,val) ->
		        (defRule (context,q,id,opinfo,false)) ++ val)
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

  def isFlexibleTerm(term:MS.Term) = 
      case isFlexVar?(term)
        of Some m -> true
	 | None -> 
      case term
        of Apply(M,N,_) -> isFlexibleTerm(M)
	 | Record(fields, _) -> all (fn (_,M) -> isFlexibleTerm M) fields
	 | _ -> false

  def deleteFlexTail(term:MS.Term) = 
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
  def redirectRule (rule as {name,lhs,rhs,tyVars,freeVars,condition}) = 
      if diverging(lhs,rhs)
	 then 
	 if diverging(rhs,lhs)
	     then None
	 else Some {name = name,lhs = rhs,rhs = lhs,tyVars = tyVars,
		    freeVars = freeVars,condition = condition}
      else Some rule

 %% If term is a qf binder then Introduce a number for each Var and return
 %% a list of the numbers paired with the sort
 %% A substitution mapping old Var to new flex var with that number
 %% The body of the binder (handles nested binders of the same type)
 op bound(qf: Binder, n: Nat, term: MS.Term, freeVars: List(Nat * Sort),
          S: List(Var * MS.Term)) 
    : List (Nat * Sort) * Nat * List (Var * MS.Term) * MS.Term =
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

  op equality : Context -> List (Var * MS.Term) * MS.Term -> Option (MS.Term * MS.Term)

  def equality context (S,N)  = 
      case N
        of Apply(Fun(Equals,_,_),Record([(_,N1),(_,N2)], _),_) -> 
  	   Some (substitute(N1,S),substitute(N2,S))
	 | Bind(Forall,vars,N,_) -> 
	   let S1 = map (fn (v,s) -> ((v,s),mkVar(freshBoundVar(context,s)))) vars in
           let N = substitute(N,S1) in
           equality context (S,N)
         | _ -> None
 
op simpleRwTerm?(t: MS.Term): Boolean =
   case t of
     | Var _ -> true
     | Fun _ -> true
     | Apply(Fun(Project _,_,_),a1,_) -> simpleRwTerm? a1
     | _ -> false

 op assertRules (context: Context, term: MS.Term, desc: String, lr?: Boolean): List RewriteRule =
   %% lr? true means that there is an explicit lr orientation, otherwise we orient equality only if obvious
   assertRulesRec(context, term, desc, lr?, [], [], None)

 op assertRulesRec (context: Context, term: MS.Term, desc: String, lr?: Boolean, freeVars: List (Nat * Sort), 
                    subst: VarSubst, condition: Option MS.Term)
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
		   {name      = desc,   condition = condition,
		    lhs       = substitute(p,subst),      rhs       = falseTerm,
		    tyVars    = [],     freeVars  = freeVars})]
     | Apply(Fun(Equals,_,_),Record([(_,e1),(_,e2)], _),_) | lr? || constantTerm? e2 ->
       [freshRule(context,
                  {name      = desc,   condition = condition,
                   lhs       = substitute(e1,subst),     rhs       = substitute(e2,subst),
                   tyVars    = [],     freeVars  = freeVars})]
     | Apply(Fun(Equals,_,_),Record([(_,e1),(_,e2)], _),_) | simpleRwTerm? e1 && ~(varTerm? e2)->
       [freshRule(context,
                  {name      = desc,   condition = condition,
                   lhs       = substitute(e2,subst),     rhs       = substitute(e1,subst),
                   tyVars    = [],     freeVars  = freeVars})]
     | Apply(Fun(And,_,_),Record([(_,e1),(_,e2)], _),_) ->
       assertRulesRec(context,e1,desc^"-1",lr?,freeVars,subst,condition)
         ++ assertRulesRec(context,e2,desc^"-2",lr?,freeVars,subst,condition)
     | Let([(VarPat(v,_),val)],body,pos) ->
       assertRulesRec(context,substitute(body,[(v,val)]),desc,lr?,freeVars,subst,condition)
     | _ ->
       if trueTerm? fml then []
       else
         [freshRule(context,
                    {name      = desc,   condition = condition,
                     lhs       = substitute(fml,subst),    rhs       = trueTerm,
                     tyVars    = [],     freeVars  = freeVars})]

 op axiomRules (context: Context) ((pt,desc,tyVars,formula,a): Property): List RewriteRule = 
%      case pt
%        of Conjecture -> []
%  	| _ ->
   assertRules(context, formula, printQualifiedId desc, true)

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

 op printRule({name,tyVars,freeVars,condition,lhs,rhs}:RewriteRule): () = 
     ( writeLine ("Rewrite rule ------- "^name^" -------");
       app (fn tv -> toScreen(tv^" ")) tyVars;
       if null tyVars then () else writeLine "";
       app (fn (n,srt) -> toScreen(toString n^" : " ^ printSort srt^" "))
         freeVars;
       if null freeVars then () else String.writeLine "";
       (case condition 
          of Some c -> (writeLine(printTerm c)) 
           | None -> ());
       writeLine ("Rewrite : "^printTerm lhs^ " ---> "^
                    printTerm rhs)  
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
	      if String.length(x) >= 2 & 
		 String.sub(x,1) = #%
		 then 
	      (case StringMap.find(! env,x)
		 of Some y -> (y,srt)
		  | None -> 
	       let y = StringUtilities.freshName("x",! vrs) in
	       (vrs := StringSet.add(! vrs,y);
		env := StringMap.insert(! env,x,y);
		(y,srt)))
	      else (x,srt)

	  def doTerm(term:MS.Term):MS.Term = 
	      case term of
		 | Var(v,a) -> Var(doVar v,a)
		 | Bind(qf,vars,body,a) -> Bind(qf,map doVar vars,body,a)
		 | The (var,body,a) -> The (doVar var,body,a)
		 | term -> term
	   def doPat(pat:Pattern):Pattern = 
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
				 tvs, mkEquality(boolSort,c,trueTerm),noPos))
			    ++ rules
		   in 
		   case c of
		     | Apply(Fun(Not,_,_), nc,_) -> 
		       (axiomRules context
			  (Axiom,
			   mkUnQualifiedId("Context-condition: " ^printTerm nc
			   ^" = false"),
			   tvs, mkEquality(boolSort,nc,falseTerm),noPos))
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

