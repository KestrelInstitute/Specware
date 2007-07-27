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

 op specRules : Context -> Spec -> RewriteRules
 op axiomRule : Context -> Property -> Option RewriteRule
 op axiomRules: Context -> Property -> List RewriteRule
 op defRule :   Context * String * String * OpInfo * Boolean -> List RewriteRule
 op etaExpand:  Context -> RewriteRule -> RewriteRule

 op rulesFromGamma : Context -> Gamma -> RewriteRules
 op mergeRules : List RewriteRules -> RewriteRules
 

%%
%% freshRule generates fresh variable names in a rule for
%% type and individual variables.
%% freshRule is only relevant when matching against non-ground terms.
%%

 op freshRule : Context * RewriteRule -> RewriteRule
 
%%
%% def freshRule(context,(desc,tyVars,bound,premises,lhs,rhs)) = 
%%     
 def freshRuleElements(context,tyVars,freeVars) = 
% tyVMap = {| name -> a | name in tyVars ... |}

     let tyVMap = List.foldr 
	 (fn (name,tyVMap) -> 
	     let num = ! context.counter in
	     let a = "'a%"^Nat.toString num in
	     (context.counter := num + 1;
	      StringMap.insert(tyVMap,name,a)))
	    StringMap.empty
		tyVars
     in
     let
	 def doSort(srt:Sort):Sort = 
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
	 List.foldr
	 (fn ((num,srt),varMap) -> 
	  let num1 = ! context.counter in
          (context.counter := num1 + 1;
	  NatMap.insert(varMap,num,(num1,freshSort srt))))
	 NatMap.empty 
	 freeVars	
     in
     let
	 def doTerm(term:MS.Term):MS.Term = 
	     case isFlexVar?(term)
	       of Some n -> 
		  (case NatMap.find(varMap,n)
		     of Some x -> mkVar x
		      | None -> System.fail (Nat.toString n^" not found"))
		| None -> term
	 def freshTerm trm = 
	     mapTerm(doTerm,doSort,fn p -> p) trm
     in
	(freshTerm,freshSort,varMap,tyVMap)

 def freshRule(context,{name,lhs,rhs,condition,freeVars,tyVars}) = 
     let (freshTerm,freshSort,varMap,tyVMap) = 
	 freshRuleElements(context,tyVars,freeVars) in
     {
	name = name,
	lhs  = freshTerm lhs,
	rhs  = freshTerm rhs,
	condition = (case condition of None -> None | Some c -> Some(freshTerm c)),
	freeVars = NatMap.listItems varMap,
	tyVars = StringMap.listItems tyVMap
     }


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Extract rewrite rules from function definition.

 def defRule (context, q, id, info : OpInfo, includeLambdaRules?: Boolean) = 
   if definedOpInfo? info then
     let (tvs, srt, term) = unpackFirstOpDef info in
     let rule:RewriteRule = 
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
      | ((rule:RewriteRule)::rules,old) -> 
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
          let rule1 : RewriteRule = 
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
	              loop(new,List.cons((l,trm),old),vars,S)
          in
          loop(fields,[],vars,S)
        | NatPat(i, _) -> Some(mkNat i,vars,S)
        | BoolPat(b, _) -> Some(mkBool b,vars,S)
        | StringPat(s, _) -> Some(mkString s,vars,S)
        | CharPat(c, _) -> Some(mkChar c,vars,S)
        | VarPat((v,srt), _) -> 
	  let num = ! context.counter in
          let w = HigherOrderMatching.freshVar(context,srt)     in
          Some(w,List.cons((num,srt),vars),List.cons(((v,srt),w),S))
        | WildPat(srt,_) -> 
	  let num = ! context.counter in
          let w = HigherOrderMatching.freshVar(context,srt)     in
          Some(w,List.cons((num,srt),vars),S)
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

 def specRules context spc = 
     let spc      = normalizeSpec spc            in
     let axmRules = flatten (List.map (axiomRules context) (allProperties spc)) in
     let opRules  = foldriAQualifierMap
                      (fn (q,id,opinfo,val) ->
		        (defRule (context,q,id,opinfo,false)) ++ val)
		      [] spc.ops
     in
     let rules = axmRules ++ opRules in
     let rules = List.map (etaExpand context) rules in
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

  def etaExpand (* context *)_ rule = rule

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def prioritizeRules(rules) = 
     let
	def loop(rules,uncond,cond) = 
	    case rules
	      of [] -> {unconditional = uncond,conditional = cond}
	       | (rule:RewriteRule)::rules -> 
	    case redirectRule rule 
	      of None -> loop(rules,uncond,cond)
	       | Some rule -> 
	    case rule.condition
	      of None -> loop(rules,List.cons(rule,uncond),cond)
	       | Some _ -> loop(rules,uncond,List.cons(rule,cond))
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
	 | Record(fields, _) -> List.all (fn (_,M) -> isFlexibleTerm M) fields
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



 op bound : Binder * Nat * MS.Term * List (Nat * Sort) * List (Var * MS.Term) -> 
		List (Nat * Sort) * Nat * List (Var * MS.Term) * MS.Term

 %% If term is a qf binder then Introduce a number for each Var and return
 %% a list of the numbers paired with the sort
 %% A substitution mapping old Var to new flex var with that number
 %% The body of the binder (handles nested binders of the same type)
 def bound(qf,n,term:MS.Term,freeVars,S) = 
     case term
       of Bind(binder,vars,body,_) -> 
	  if qf = binder
	     then 
	     let (freeVars,S,n) = List.foldr 
		 (fn ((x,srt),(freeVars,S,n)) -> 
		     let y = mkVar(n,srt) in
		     (List.cons((n,srt),freeVars),
		      List.cons(((x,srt),y),S),n + 1))
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
	   let S1 = 
	       List.map 
		(fn (v,s) -> ((v,s),Var((freshBoundVar(context,s)),noPos):MS.Term))
		  vars 
	  in
	  let N = substitute(N,S1) in
	  equality context (S,N)
	| _ -> None
 
 def axiomRules context (pt:PropertyType,desc,tyVars,formula,a) = 
     case pt
       of Conjecture -> []
 	| _ -> 
     let def visitConjunct str formula =
       case formula of
	 | Apply(Fun(And,_,_), Record([(_,M),(_,N)], _),_) -> 
             (visitConjunct (str ^ " (l)") M)
               ++ (visitConjunct (str ^ " (r)") N)
         | _ -> 
             (case axiomRule context (pt,desc,tyVars,formula,a) of
                   None -> []
                 | Some rule -> [rule]) in
     visitConjunct "" formula

 def axiomRule context (pt:PropertyType,desc,tyVars,formula,a) = 
     case pt
       of Conjecture -> None
	| _ -> 
     let freeVars = [] in
     let (freeVars,n,S,formula) = bound(Forall:Binder,0,formula,freeVars,[]) in
     let (condition,fml) = 
	  case formula of 
            | Apply(Fun(Implies,_,_), Record([(_,M),(_,N)], _),_) -> 
		(Some (substitute(M,S)): Option MS.Term,N)
	    | _ -> (None,formula)
     in
     case equality context (S,fml)
       of Some(N1,N2) -> 
          Some (freshRule(context,
		 {name      = printQualifiedId(desc),   condition = condition,
		  lhs       = N1,     rhs       = N2,
  	          tyVars    = tyVars, freeVars  = freeVars}))
	| None -> None


 op printRule: RewriteRule -> ()
 def printRule({name,tyVars,freeVars,condition,lhs,rhs}:RewriteRule) = 
     (
       writeLine ("Rewrite rule ------- "^name^" -------");
       app (fn tv -> toScreen(tv^" ")) tyVars;
       if null tyVars then () else writeLine "";
       app (fn (n,srt) -> toScreen(toString n^" : " ^ printSort srt^" "))
         freeVars;
       if List.null freeVars then () else String.writeLine "";
       (case condition 
          of Some c -> (writeLine(printTerm c)) 
           | None -> ());
       writeLine ("Rewrite : "^printTerm lhs^ " ---> "^
                    printTerm rhs)  
     )	


  def renameBound(term) = 
      let free = freeVars term in
      let free = List.map (fn (s,_) -> s) free in
      let env0 = StringMap.empty in     
      let env1 = (List.foldr (fn (s,m) -> StringMap.insert(m,s,s)) env0 free) in
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
		 | Bind(qf,vars,body,a) -> Bind(qf,List.map doVar vars,body,a)
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

 def rulesFromGamma context gamma = 
     let (ds,tvs,env,name,names) = gamma in
     let subst0 = HigherOrderMatching.emptySubstitution in
     let
	 def loop(d,rules) = 
	     case d
	       of Cond c -> 
		  let c = HigherOrderMatching.dereferenceAll subst0 c in
		  (case axiomRule context
		         (Axiom:PropertyType,
			  mkUnQualifiedId("Context-condition: "^printTerm c),tvs,c,noPos)
		     of Some rule -> List.cons(rule,rules)
		      | None ->
		   let rules
		        = case axiomRule context
				(Axiom:PropertyType,
				 mkUnQualifiedId("Context-condition: " ^printTerm c),
				 tvs, mkEquality(boolSort,c,mkTrue()),noPos)
			    of Some rule -> List.cons(rule,rules)
			     | None -> rules
		   in 
		   case c of
		     | Apply(Fun(Not,_,_), nc,_) -> 
		       (case axiomRule context
			  (Axiom:PropertyType,
			   mkUnQualifiedId("Context-condition: " ^printTerm nc
			   ^" = false"),
			   tvs, mkEquality(boolSort,nc,mkFalse()),noPos)
			  of 
			   | Some rule -> List.cons(rule,rules)
			   | None -> rules)
		     | _ -> rules)
		| _ -> rules
     in
     let rules = List.foldr loop [] ds in
     let rules = prioritizeRules(rules)  in
     rules

 def mergeRules = 
     fn [] -> {unconditional = [],conditional = []}
      | [rules] -> rules
      | rules1::rules2::rules -> 
        let rules1 = {unconditional = rules1.unconditional ++ 
						rules2.unconditional,
		        conditional = rules1.conditional ++ 
					      rules2.conditional}
	in
	mergeRules(List.cons(rules1,rules))

end-spec

