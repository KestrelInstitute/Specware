% Synchronized with version 1.3 of SW4/Languages/MetaSlang/Transformations/Match.sl

(*
   Pattern matching compiler for Meta-Slang.
   Matches of the form
	
	  pattern_1 where condition_1 -> body_1
	| pattern_2 where condition_2 -> body_2
	| ..
	| pattern_n where condition_n -> body_n

   are translated to expressions without patterns,
   using If-Then-Else expressions instead.

   The pattern matching compiler should
   
	. Generate the If-Then-Else expressions as described above
	  With minimal branching.
	  References
		Phil's chapter in Preyton Jones' book
	  	The pattern matching compilers in HOL
		The matching compiler in Moscow ML 
                (does use sharing, but branches).

	. Handle patterns from:
		Coproducts: embed
		Products:   tuple
		Subsort:    relax
		Quotient:   quotient
		Natural, String, character constants.
		Variables.

	  There is a question what to do with patterns from non-free 
          constructors.

	  Free constructors in Slang may be translated into 
          recursive co-products in Meta-Slang.

	. Generate error messages on non-exhaustive and redundant 
          matches when these can be detected statically.

	  Generate proof-obligations for exhaustive pattern 
          matching when these cannot be detected statically.


   The pattern matching compiler generates expressions of the form:

   match-term ::= TranslationBuiltIn.block block-term
  
   BLOCK-TERM ::= if TERM then BLOCK-TERM else BREAK
		| if TERM then BLOCK-TERM else SUCCESS
		| if TERM then BLOCK-TERM else FAIL
   		| let x = TERM in BLOCK-TERM
		| FAIL
		| SUCCESS
		| BREAK
		| TranslationBuiltIn.failWith (BLOCK-TERM, BLOCK-TERM)


   BREAK      ::= TranslationBuiltIn.mkBreak
   SUCCESS    ::= TranslationBuiltIn.mkSuccess TERM
 *)

PatternMatch qualifying spec { 
  import ArityNormalize
   
  % import MetaSlangPrint	% imported by ArityNormalize

  op  translateMatch : Spec -> Spec

  def match_type(srt) = mkBase(Qualified("TranslationBuiltIn","Match"),[srt])

  def mkBreak(srt) = mkOp(Qualified("TranslationBuiltIn","mkBreak"),match_type srt)
  def isBreak(term:Term) = 
      case term
	of Fun(Op(Qualified("TranslationBuiltIn","mkBreak"),_),_,_) -> true
         | _ -> false

  def mkSuccess(srt0,trm) = 
      let srt = mkArrow(srt0,match_type srt0) in 
      mkApply(mkOp(Qualified("TranslationBuiltIn","mkSuccess"),srt),trm)

  def isSuccess(trm) = 
      case trm
	of Apply(Fun(Op(Qualified("TranslationBuiltIn","mkSuccess"),_),_,_),_,_) ->
	   true
	 | _ -> false

  def isTrue(term:Term) = 
      case term
	of Fun(Bool true,_,_) -> true
	 | _ -> false

(*
   The function failWith implements exception handling.
   It unfolds to the primitive:

   failWith(t1,t2) = 
   case evaluate(t1)
     of	Break -> evaluate(t2)
      | Succcess result -> Success result
      | Fail -> evaluate(t2)

   when compiled to LISP, C, JAVA failWith unfolds to
   the continuations used in block statements.
   Break results in a break;
   IfThenElse(a,b,Break) translates to if(a) {b};
   Success(result) translates to return(result);
   
 *)

  op failWith : Context -> Term -> Term -> Term
  def failWith context t1 t2 = 
      (if isBreak(t2) then t1 else
	 if isSuccess(t1) then (warnUnreachable context; t1) else
      let srt  = inferType(context.spc,t1) in
      let srt  = mkArrow(mkProduct [srt,srt],srt) in
      let trm  = mkApply(mkOp(Qualified("TranslationBuiltIn","failWith"),srt), mkRecord [("1",t1),("2",t2)]) in
       trm
     )

  def warnUnreachable context =
    writeLine("Warning: Redundant case in "^context.funName^"
"
	      ^ (case context.term
		   of Some t -> printTerm t
		    | _ -> ""))
  
  sort Rule  = List(Pattern) * Term * Term
  sort Rules = List Rule
  

  sort Context = {counter : Ref Nat,
		  spc     : Spec,
		  funName : String,
		  term    : Option Term}

  def storeTerm(tm,{counter, spc, funName, term}) =
    {counter=counter, spc=spc, funName=funName, term=Some tm}

%  op mkProjectTerm : Spec * Id * Term -> Term
%  def mkProjectTerm = SpecEnvironment.mkProjectTerm
%  op mkRestrict :    Spec * {pred:Term,term: Term} -> Term
%  def mkRestrict = SpecEnvironment.mkRestrict
  

  op match :  Context * List(Term) * Rules * Term * Term -> Term

  (* The following invariant holds of the patterns:
     - for a call to match(vars,rules,default):
	each list of patterns in the rules has the same length and sorting 
        as the list of vars.

     Pattern matching compilation proceeds according to 
     the following transformation rules on the arguments of match 
     (Wadler's chapter in Peyton Jones contains all relevant information too).

     The empty rule:
       There are no variables left to match with.
       The rules are of the form

	[]
	  [([],p1,E1),....,([],pn,En)]
	default

       return 
	  if p1 then E1 else break() failWith 
	  if p2 then E2 else break() failWith 
	  if p3 then E3 else break() failWith ... failWith default.

     When there are variables left to match with, there rules are
     partitioned to contain first column elements of the same form.
     These are either all variable patterns, constructor patterns,
     alias patterns, relax, or quotient patterns.
     They are processed according to the following rules:

     The variable rule:
        All elements in the first column are variable patterns.
        We substitute each variable pattern by the first parameter
        variable in each of the bodies.

     The constructor rule:
	All elements in the first column are constructors.
        Constructors with the same head symbol are grouped together
	(this is only necessary for embed patterns).
	
	Say we have rules of the form

	v:: vars		
	  [(CONS b1 :: patterns_1,cond1,e1),...,
	   (CONS bn :: patterns_n,condn,en)]
	default

	return
	  if CONS?(v)
	     then 
	     extract(CONS)(v)::vars
		  [(b1 :: patterns_1,cond1,e1),...,
		   (bn :: patterns_n,condn,en)]
	     	  break()
	  else break()
	  failWith 
	  default

    The alias rule:
        Aliased patterns are duplicated:

	v::vars
	[(Alias(p1,p2)::patterns,cond,e)]
	default
	
        return

	v::v::vars
	[(p1::p2::patterns,cond,e)]
	default

    Subsort rule:

	v::vars
	[(RelaxPat(pat:t|pred-> t)::patterns,cond,e)]
	default

	return

	if pred(v)
	   then restrict(v)::vars
		[(pat::patterns,cond,e)]
	 	break()
	else break()
	failWith
	default
	

   Quotient rule:

	(v:t/pred)::vars
	[(QuotientPat(pat: t,pred)::patterns,cond,e)]
	default

	return

	choose(x,v)
	(
	 x::vars
	 [(pat::patterns,cond,e)]
	 default
	)

	Alternatively 

	 rep(v)::vars
	 [(pat::patterns,cond,e)]
	 default


	case e::es 
	  of (quotient(q?) pattern,...) -> term
	   | .. -> term2

        translate to:

	choose x from e in
	case x::es
	  of (pattern,...) -> term1
	   | ... -> term2
 *)

  def substPat(e,pat:Pattern,t) = 
      if isTrue(e) then e else 
      case pat
	of WildPat _ -> e
         | VarPat _ -> mkLet([(pat,t)],e)
	 | _ -> e (* Should not happen *)
      

(* 
   We generate tester functions for the various constructor formats.
 *)

  def embedded(constructorName:String) term = 
      mkApply(mkEmbedded(constructorName,termSort term),term)


  def relaxed(predicate) term = mkApply(predicate,term)
 
  def equalToConstant(srt,constantTerm:Term) term =
      mkEquality(srt,constantTerm,term)


  def mkLet(lets:List(Pattern*Term),term) = 
      case lets
        of [] -> term : Term
         | _  -> StandardSpec.mkLet(lets,term)
        	
  op partition : fa(A,B) (A -> B) -> List(A) -> List(List(A))
  op tack : fa(A) A -> List(List(A)) -> List(List(A))
  def partition f qs = 
      case qs
        of [] -> []
         | [x] -> [[x]]
         | Cons(x,Cons(y,xs)) -> 
 	   if f x = f y 
              then tack x (partition f (cons(y,xs)))
           else Cons([x],partition f (cons(y,xs)))
      
  def tack x xss = Cons(Cons(x,hd xss),tl xss)


  sort RuleType = 
     | Var | Con | Alias  Pattern * Pattern
     | Relax  Pattern * Term | Quotient  Pattern * Term

  def ruleType (q:Rule) : RuleType = 
      case q
        of ((VarPat _)::_,_,_)     -> Var
	 | ((WildPat _)::_,_,_)    -> Var
 	 | ((AliasPat(p1,p2,_))::_,_,_) -> Alias(p1,p2)
 	 | ((EmbedPat _)::_,_,_)   -> Con
         | ((RecordPat _)::_,_,_)  -> Con
         | ((StringPat _)::_,_,_)  -> Con
         | ((BoolPat _)::_,_,_)    -> Con
         | ((NatPat _)::_,_,_)     -> Con
         | ((CharPat _)::_,_,_)    -> Con
         | ((RelaxPat (pat,pred,_))::_,_,_) -> Relax (pat,pred)
         | ((QuotientPat(pat,pred,_))::_,_,_) -> Quotient(pat,pred) 
      

  op printRule: fa(a) List(APattern a) * ATerm a * ATerm a -> ()
  def printRule(pats,cond,body) = 
      (toScreen "Pattern : ";
       app (fn p -> toScreen (printPattern p^" ")) pats;
       writeLine "";
       writeLine ("Condition: "^printTerm cond);
       writeLine ("Body: "^printTerm body))

  def sameConstructor(pat1:Pattern,pat2:Pattern) = 
      case (pat1,pat2)
        of (EmbedPat(e1,_,_,_),EmbedPat(e2,_,_,_)) -> e1 = e2
	 | (RecordPat _,RecordPat _) -> true
	 | _ -> equalPattern?(pat1,pat2)
      

(*
   op partitionConstructors : Var * Rules -> List(DestructedRule]

   Given a list of rules, where the first pattern of each rule is a constructor
   we partition the rules into sequences of the same constructor, and for each
   segment of the form:

	CONSTR pats_1,patterns_1, cond_1,body_1
	CONSTR pats_2,patterns_2, cond_2,body_2
	...
	CONSTR pats_n,patterns_n, cond_n,body_n

   we transform:
	
	pats_1,patterns_1, cond_1,body_1
	pats_2,patterns_2, cond_2,body_2
	...
	pats_n,patterns_n, cond_n,body_n

   and also return one version of:

	vars	- a list of variables of the same type as pats_i.
	lets	- a list of let bindings that bind vars to destructors of 
		  a variable v that is given as argument to partitionConstructors.
		  For example, for the pattern {head:pat1,tail:pat2}
		  lets = [(VarPat v1,Apply(Fun(Project(head),_),Var v)),
			  (VarPat v2,Apply(Fun(Project(tail),_),Var v))]
		  which in human terms reads into:

			let v1 = v.head and v2 = v.tail in ...
	query   - term determining if the input variable v is an instance of
		   constructor CONSTR.
		
 *)
  sort DestructedRule = Term * List(Term) * List(Pattern * Term) * Pattern * Rules
  op partitionConstructors : Context * Term * Rules -> List(DestructedRule)

  op freshVar : Context * Sort -> Var

  def freshVar(context,srt) = 
      let num = ! context.counter + 1 in
      (context.counter := num;
       ("pV" ++ (Nat.toString num),srt)
      )

  def freshVars(num,context,pat:Pattern) = 
      if num = 0 
	then [] 
      else
      if num = 1
      	then [("",freshVar(context,patternSort(pat)))]
      else
      case pat
	of  RecordPat(fields,_) -> 
	    map (fn(l,p) -> (l,freshVar(context,patternSort(p)))) fields
	 | _ -> System.fail "Record pattern expected"

  (* 
   *  Generates the query term used to identify variable being an instance
   *  of the pattern 
   *)

  def queryPat(pattern:Pattern): Term -> Term = 
      case pattern
        of EmbedPat(e,_,_,_) -> embedded(e)
	 | NatPat(n,_)    ->    equalToConstant(natSort,mkNat(n))
	 | CharPat(ch,_)  ->    equalToConstant(charSort,mkChar(ch))
	 | BoolPat(b,_)   ->    equalToConstant(boolSort,mkBool(b))
	 | StringPat(s,_) ->    equalToConstant(stringSort,mkString s)
	 | RecordPat _ -> (fn _ -> mkTrue())
	 | _ -> (fn _ -> mkTrue())
              

  def coproductFields(spc,srt) = 
      case unfoldBase(spc,srt)
        of CoProduct(fields,_) -> fields
	 | Subsort(tau,_,_) -> coproductFields(spc,tau)
         | _ -> System.fail 
		("CoProduct sort expected, but got "^printSort srt)

  def partitionConstructors(context,t,rules) =
      let
	  def patDecompose(pattern: Pattern):List(Pattern*Term) = 
	      case pattern
	        of RecordPat(pats,_) -> 
		   map (fn(index,p)-> (p,mkProjectTerm(context.spc,index,t))) pats
	         | EmbedPat(id,Some p,srt,_) -> 
	           let fields = coproductFields(context.spc,srt) in
		   let trm = 
		       (case find (fn (id2,s) -> id = id2) fields
			  of Some(_,Some s) ->
			     mkApply((Fun(Select id,mkArrow(srt,s),noPos)),t)
			   | _ -> System.fail "Selection index not found in product")
		   in
		   [(p,trm)]
	 	 | _ -> []	
      	      
      in
      let
	 def insert(rule,rules:List(DestructedRule)):List(DestructedRule) = 
	     case (rule:Rule,rules)
	       of ((pat::pats,cond,body),[]) -> 
		  let query         = queryPat(pat)(t)  in
		  let decomposition = patDecompose(pat) in
		  let newVars = 
		      map (fn(p,_)-> freshVar(context,patternSort(p))) 
		      decomposition 
		  in
		  let lets  = 
		      ListPair.map (fn((p,t),v)-> (mkVarPat v,t)) 
			(decomposition,newVars) 
		  in
		  let newPats = map (fn(p,_)-> p) decomposition in
		  [(query,map mkVar newVars,lets,pat,
			[(concat(newPats,pats),cond,body)])]
	        | ((pat::pats,cond,body),
		    (destrRule as (query,newVars,lets,pat2,rules2))::rules) -> 
	          if sameConstructor(pat,pat2)
                     then 
		     let decomposition = patDecompose(pat) in
		     let newPats       = map (fn(p,_)-> p) decomposition in
		     let rule          = (concat(newPats,pats),cond,body):Rule in
		     Cons((query,newVars,lets,pat2,Cons(rule,rules2)),rules)
		  else if exists (fn (_,_,_,pat3,_) -> sameConstructor(pat,pat3))
		            rules
			 then cons(destrRule,insert(rule,rules))
			 else concat(insert(rule,[]),cons(destrRule,rules))
                | _ -> rules (* should not happen *)
              
      in
      foldr insert [] rules 
	       
  
  
  def abstract(vs:List(String * Var),t:Term,srt):Term = 
      let srt = mkArrow(match_type(srt),srt) in
      let oper = mkOp(Qualified("TranslationBuiltIn","block"),srt) in
      let t  = mkApply(oper,t) in
      let pat = 
          case vs of [(_,v)] -> mkVarPat v
	     | _ -> RecordPat(map (fn(l,v)-> (l,mkVarPat v)) vs,noPos)
      in
      Lambda([(pat,mkTrue(),t)],noPos)

  def mkOptimizedIfThenElse(cond,thenBranch,elseBranch) = 
      if isTrue(cond)
	 then thenBranch
      else mkIfThenElse(cond,thenBranch,elseBranch)
 
  def match(context,vars,rules:Rules,default,break) = 
      (%%%writeLine "Match ";
      case vars
        of [] -> foldr 
                 (fn((_,cond,body),default) -> 
		    failWith context 
		    (mkOptimizedIfThenElse(cond,body,break))
		    default) default rules
         | Cons _ -> 
%%	   let _ = writeLine "Matching list " in
	   let rules = (partition ruleType rules) in
           foldr (matchRules (context,break,vars)) default rules
      )
  
  def matchRules (context,break,vars) (rules,default) = 
      (%%%writeLine "matchRules ";
      case ruleType (hd rules)
        of Var -> matchVar(context,vars,rules,default,break)
         | Con -> matchCon(context,vars,rules,default,break)
	 | Alias(p1,p2) -> matchAlias(context,p1,p2,vars,rules,default,break)
         | Relax(pat,pred) -> 
           matchSubsort(context,pred,vars,rules,default,break)
         | Quotient _ -> matchQuotient(context,vars,rules,default,break)
      )
  def matchVar(context,terms,rules,default,break) = 
%%      let _ = writeLine "Matching var " in
      let t = hd terms in
      let terms = tl terms in
%%      let _ = writeLine "Matching var " in
      let rules = 
	  map
		 (fn ((Cons(pat,pats),cond,body):Rule) ->
		     (pats,substPat(cond,pat,t),substPat(body,pat,t))
		   | _ -> System.fail "Empty list of patterns ") rules
      in
%%      let _ = writeLine "Matching var " in
      match(context,terms,rules,default,break)

  def matchCon(context,terms,rules,default,break) = 
      let t    = hd terms in
      let terms = tl terms in
      let rulePartition = partitionConstructors(context,t,rules) in
      let rule = foldr 
	        (fn ((query,newVars,lets,_,rules),default) ->   
	            mkOptimizedIfThenElse(query,
		      mkLet(lets,
			    match(context,newVars @ terms,rules,break,break)),
		      default)) break rulePartition
      in
	 failWith context rule default
  def matchAlias(context,pat1,pat2,terms,rules,default,break) = 
      let t = hd terms in
      let rules = map (fn( (Cons(_,pats),cond,e):Rule)->
				(Cons(pat1,Cons(pat2,pats)),cond,e):Rule)
		  rules in
      match(context,cons(t,terms),rules,default,break)
  def matchSubsort(context,pred,t::terms,rules,default,break) =
%%    let _ = writeLine "match Subsort " in
      let _(* srt *) = inferType(context.spc,t)                   in
      let t1     = mkRestrict(context.spc,{pred = pred,term = t}) in
      let rules  = map (fn(((RelaxPat(p,_,_))::pats,cond,e):Rule) ->
			      (cons(p,pats),cond,e):Rule) rules in
      failWith context 
	(mkIfThenElse(mkApply(pred,t),
	           match(context,cons(t1,terms),rules,break,break),
		   break))  default 
  def matchQuotient(context:Context,t::terms,rules,default,break) = 
      let Quotient(srt,pred,_)  = inferType(context.spc,t)  in
%%
%%    Given current implementation of choose, we compile
%%     t1 = choose(fn x -> x) t 
%%
      let v = ("v",srt)                                   in
      let f = mkLambda(VarPat(v,noPos),Var(v,noPos))                    in
      let t1 = mkApply(mkChooseFun(pred,srt,srt,f),t)	  in
      let rules  = map (fn((Cons((QuotientPat(p,pred,_)):Pattern,pats),cond,e):Rule) ->
			      (Cons(p,pats),cond,e):Rule) rules in
      failWith context
      (match(context,cons(t1,terms),rules,break,break))
      default 	


 def simplePattern pattern = 
      case pattern:Pattern
	of VarPat _ -> true
	 | _ -> false
 
 def simpleAbstraction(rules:Match) = 
     case rules
       of [(RecordPat(fields,_),cond,_)] -> 
	  isTrue cond & all (fn(_,p)-> simplePattern p) fields
        | [(pat,cond,_)] -> simplePattern pat & isTrue cond
	| _ -> false

 %% fn (x as pat) -> bod  -->  fn x -> let pat = x in bod
 %% Without this other normalizations such as arity normalization break
 def normalizeSimpleAlias(rules:Match): Match =
     case rules
       of [(AliasPat(VarPat(v,a1),p2,a2),cond,body)] ->
	  [(VarPat(v,a1),mkTrue(),Apply(Lambda([(p2,cond,body)],a2),Var(v,a1),a2))]
	| _ -> rules

 def splitPattern(arity,pat:Pattern):List Pattern =
     if arity = 1 then [pat] else
     case pat
       of RecordPat(fields,_) -> map (fn(_,p)-> p) fields
        | WildPat(srt,_) -> tabulate(arity,fn _ -> pat)
        | _ -> System.fail "Unexpected pattern" 

def zipFields(fields,terms) =
    case (fields,terms)
      of ([],[]) -> []
       | ((_,pat)::fields,(_,t)::terms) -> cons((pat,t),zipFields(fields,terms))
       | _ -> System.fail "zipFields: Uneven length of fields"

def flattenLetDecl((pat:Pattern,term:Term),(context,decls)) =
    case (pat,term)
      of (WildPat(srt,_),Var _) -> (context,decls)
       | (WildPat(srt,_),Record([],_)) -> (context,decls)
       | (WildPat(srt,_),term) -> 
	  (context,
           cons((mkVarPat(freshVar(context,patternSort(pat))),term),decls))
       | (RecordPat(fields,_),Record(terms,_)) ->
	 foldr flattenLetDecl (context,decls) (zipFields(fields,terms)) 
       | (RecordPat(fields,_),term) -> 
          let v = freshVar(context,inferType(context.spc,term)) in
	  let vTerm = mkVar v 				    in
	  let decls1 = map (fn(id,pat) -> (pat,mkProjectTerm(context.spc,id,vTerm))) fields in
	  let (context,decls2) = foldr flattenLetDecl (context,decls) decls1                in
	  (context,cons((mkVarPat v,term),decls2 @ decls))
       | _ -> (context,cons((pat,term),decls))

op  eliminatePattern: Context -> Pattern -> Pattern 
op  eliminateTerm   : Context -> Term -> Term
op  eliminateSort   : Context -> Sort -> Sort

%def elimPattern x = x % dummy implementation

def eliminatePattern context pat = 
    case pat
      of AliasPat(p1,p2,a) -> 
	 AliasPat(eliminatePattern context p1,
	          eliminatePattern context p2,a)
       | VarPat((n,s),a) -> VarPat((n,eliminateSort context s),a)
       | EmbedPat(i,Some p,s,a) ->
	 EmbedPat(i,Some(eliminatePattern context p),eliminateSort context s,a)
       | EmbedPat(i,None,s,a) ->
	 EmbedPat(i,None,eliminateSort context s,a)
       | RecordPat(fields,a) -> 
	 RecordPat(map (fn(i,p)-> (i,eliminatePattern context p)) fields,a)
       | WildPat(s,a) -> VarPat(freshVar(context,eliminateSort context s),a)
       | StringPat(s,a) -> StringPat(s,a)
       | BoolPat(b,a)    -> BoolPat(b,a)
       | CharPat(ch,a)   -> CharPat(ch,a)
       | NatPat(n,a)     -> NatPat(n,a)
       | RelaxPat(p,t,a)  ->
	 RelaxPat(eliminatePattern context p,eliminateTerm context t,a)
       | QuotientPat (p,t,a) ->
	 QuotientPat(eliminatePattern context p,eliminateTerm context t,a)

def eliminateSort context srt =
    case srt
      of Arrow(s1,s2,a) -> Arrow(eliminateSort context s1,
			       eliminateSort context s2,a)
       | Product(fields,a) -> 
	 Product(map (fn (i,s) -> (i,eliminateSort context s)) fields,a)
       | CoProduct(fields,a) -> 
	 CoProduct(map (fn (i,Some s) -> 
				(i,Some (eliminateSort context s))
			      | (i,None) -> 
				(i,None)) fields,a)
       | Quotient(s,t,a) -> Quotient(eliminateSort context s,
				   eliminateTerm context t,a)
       | Subsort(s,t,a) -> Subsort(eliminateSort context s,
				eliminateTerm context t,a)
       | Base(qid,sorts,a) -> Base(qid,map (eliminateSort context) sorts,a)
       | TyVar _ -> srt

(*
 * Generate the default catch all case
 * given a set of rules 
 *)

def makeFail(name,srt,_(* term *)) = 
    let srt1 = mkArrow(srt,match_type srt) in
    let msg  = "Nonexhaustive match failure in "^name
    in    
    mkApply(mkOp(Qualified("TranslationBuiltIn","mkFail"),srt1),
	    mkString msg)

def makeDefault(context:Context,srt,rules,vs,term) = 
    let 
	def loop(rules:Match,firstRules) = 
	    case rules
	      of [] -> 
    		 (rev firstRules,makeFail(context.funName,srt,term))
	       | [(WildPat _,Fun(Bool true,_,_),body)] ->
		 (rev firstRules,mkSuccess(srt,body))
	       | [(VarPat(v,_),Fun(Bool true,_,_),body)] ->
		let term: Term = 
		    case vs
		      of [(_,v)] -> Var(v,noPos)
		       | _ -> Record(map (fn(l,v)-> (l,mkVar v)) vs,noPos) 
		in
		let body = mkLet([(VarPat(v,noPos),term)],body) in
		 (rev firstRules,mkSuccess(srt,body))
	       | rule::rules ->
		 loop(rules,cons(rule,firstRules))
    in
	loop(rules,[])

def wildPattern? rule =
  case rule
    of (WildPat _,Fun(Bool true,_,_),_) -> true
     | (VarPat(v,_),Fun(Bool true,_,_),_) -> true
     | _ -> false

def checkUnreachableCase(context,term,rules) =
  let def nonfinalWildPattern?(rules) =
        case rules
	  of [] -> false
	   | [_] -> false
	   | rule :: rules ->
	     wildPattern? rule or nonfinalWildPattern? rules
  in if nonfinalWildPattern? rules
      then writeLine("Warning: Unreachable case in "^context.funName^"
"
			    ^  printTerm term)
      else ()

def eliminateTerm context term = 
    case term
      of Lambda(rules,_) ->
	 let rules = normalizeSimpleAlias rules in
	 let arity = matchArity(rules) in
	 let rules = map (fn(p,c,b)-> (eliminatePattern context p,
				       eliminateTerm context c,
				       eliminateTerm context b)) rules 
	 in
	 if  simpleAbstraction(rules) 
	     then Lambda(rules,noPos)
	 else 

	 %%%	 let _ = writeLine "Elimination from lambda " in
	 let _ = checkUnreachableCase(context,term,rules) in
	 let (pat,cond,bdy) = hd rules in
	 let bdySort = inferType(context.spc,bdy) in
	 let vs = freshVars(arity,context,pat) in
	 %%%	 let  _ = writeLine "Elimination from lambda: rules " in
	 let (rules,default) = makeDefault(context,bdySort,rules,vs,term) in
	 let rules = map 
	    (fn(p,c,t)-> (splitPattern(arity,p),c,mkSuccess(bdySort,t))) rules in
	 let vars = map (fn (lbl,v) -> mkVar v) vs in
	 let trm = 
	     match(storeTerm(term,context),
		   vars,rules,default,mkBreak(bdySort)) in
	 let trm = abstract(vs,trm,bdySort) in
	 trm
(* 
 * Treatment of let-bound patterns is optimized with respect to a number
 * of special cases: Wildcards, trivially satisfiable patterns, Non-flattened patterns, et.c.
 *)
       | Let(decls,body,_) -> 
	 let decls = map (fn(p,e) -> (eliminatePattern context p,
				      eliminateTerm context e))
	               decls
	 in
	 let body  = eliminateTerm context body in
      	(* Translate non-recursive non-simple let patterns into application *)
	 	 
	 let (context,decls) = 
	     foldr flattenLetDecl (context,decls) [] 
	 in
	 if all (fn(pat,e)-> simplePattern pat) decls
 		then mkLet(decls,body)
	 else 

	 let (pats,terms) = ListPair.unzip decls in
	 %% let _ = writeLine "Let pattern elimination " in
	 %% let _ = app (fn p -> writeLine (printPattern p)) pats in
	 
        let trm = 
      	     case terms
	       of [trm] -> trm
	 	| terms -> mkTuple(terms)
	in
	let bdySrt = inferType(context.spc,body) in
%%       let _  = writeLine "Let pattern elimination tabulating " in
	let vs = map (fn pat -> freshVar(context,patternSort(pat)))
	           pats 
	in
	let (vars,_)  = 
	    foldl (fn (v,(vars,num)) -> 
		   (cons((Nat.toString num,v),vars),num + 1))
	      ([],1) vs
	in
%%%	let _ = writeLine "Let pattern elimination: match" in
	let t = match(context,
		      map mkVar vs,
		      [(pats,mkTrue(),mkSuccess(bdySrt,body))] :Rules,
		      makeFail(context.funName,bdySrt,term),
		      mkBreak(bdySrt)) 
	in
	let t = abstract(vars,t,bdySrt) in
	mkApply(t,trm)
      | Apply (t1,t2,a) -> 
	Apply(eliminateTerm context t1,eliminateTerm context t2,a)
      | Record(fields,a) ->
	Record (map (fn(id,t)-> (id,eliminateTerm context t)) fields,a)
      | Bind(b,vars,t,a) -> 
	Bind(b,map (fn(n,s)-> (n,eliminateSort context s)) vars,
	     eliminateTerm context t,a)
      | LetRec(decls,body,a) -> 
	LetRec(map (fn ((n,s),t)->
			     ((n,eliminateSort context s),
			      eliminateTerm context t)) decls,
		eliminateTerm context body,a)
       | Var((n,s),a) -> Var((n,eliminateSort context s),a)
       | Fun(f,s,a) -> Fun(f,eliminateSort context s,a)
       | IfThenElse(s1,s2,s3,a) -> 
	 IfThenElse(eliminateTerm context s1,
		    eliminateTerm context s2,
		    eliminateTerm context s3,a)
       | Seq(terms,a) -> Seq(map (eliminateTerm context) terms,a)


%- --------------------------------------------------------------------------------
%- checks whether Record is a Product or a user-level Record

 op isShortTuple : fa(A) Nat * List(Id * A) -> Boolean
 def isShortTuple(i,row) = 
     case row
       of [] -> true
	| (lbl,r)::row -> lbl = Nat.toString i & isShortTuple(i + 1,row)

 op recordfields? : fa(A) List (Id * A) -> Boolean
 def recordfields?(fields) = ~(isShortTuple(1,fields))

(*****
%%%%%%
%%
%%  Dropped arity raising for the first round of pattern matching compilation.
%% 
%%  let term = mapTerm(arityRaising,fn x -> x,fn x -> x) term in
%%%%%%

    let term = mapTerm(elimPattern,fn x -> x,fn x -> x) term in

    (%%% writeLine "Pattern eliminated";
     term)
*****)
	 

 def translateMatch (spc : Spec) = 
   let counter = (Ref 0) : Ref Nat in
   let mkContext = fn funName -> 
                    {counter = counter,
		     spc     = spc,
		     funName = %spc.name ^"."^ % ???
		     funName,
		     term    = None} 
   in
     {importInfo    = spc.importInfo,
      sorts         = mapiAQualifierMap
                        (fn (qname, name, (sort_names, tyVars, Some srt : Option Sort)) -> 
			    (sort_names, tyVars, Some (eliminateSort (mkContext name) srt))
		          | (qname, name, (sort_names, tyVars, None)) -> 
			    (sort_names, tyVars, None))
			spc.sorts,
      ops           = mapiAQualifierMap
                        (fn (qname, name, (op_names, fixity, (tyVars, srt), Some term : Option Term)) ->
			    (op_names, 
			     fixity, 
			     (tyVars, eliminateSort (mkContext name) srt),
			     Some (eliminateTerm (mkContext name) term))
		          | (qname, name, (op_names, fixity, (tyVars, srt), None)) -> 
			     (op_names, fixity, (tyVars, eliminateSort (mkContext name) srt), None))
			spc.ops,
      properties    = map (fn (pt, name, tyvars, term) -> 
    		  	      (pt, name, tyvars, eliminateTerm (mkContext name) term)) 
                          spc.properties
     } : Spec

}










