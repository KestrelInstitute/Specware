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
		Phil's chapter in Peyton Jones' book
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
  def isBreak(term:MS.Term) = 
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

  def isTrue(term:MS.Term) = 
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

  op failWith : Context -> MS.Term -> MS.Term -> MS.Term
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
  
  sort Rule  = List(Pattern) * MS.Term * MS.Term
  sort Rules = List Rule
  

  sort Context = {counter : Ref Nat,
		  spc     : Spec,
		  funName : String,
		  term    : Option MS.Term}

  def storeTerm(tm,{counter, spc, funName, term}) =
    {counter=counter, spc=spc, funName=funName, term=Some tm}

%  op mkProjectTerm : Spec * Id * MS.Term -> MS.Term
%  def mkProjectTerm = SpecEnvironment.mkProjectTerm
%  op mkRestrict :    Spec * {pred:MS.Term,term: MS.Term} -> MS.Term
%  def mkRestrict = SpecEnvironment.mkRestrict
  

  op match :  Context * List(MS.Term) * Rules * MS.Term * MS.Term -> MS.Term

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
 
  def equalToConstant(srt,constantTerm:MS.Term) term =
      mkEquality(srt,constantTerm,term)


  def mkLet(lets:List(Pattern*MS.Term),term) = 
      case lets
        of [] -> term : MS.Term
         | _  -> MS.mkLet(lets,term)
        	
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
     | Relax  Pattern * MS.Term | Quotient  Pattern * MS.Term

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
  sort DestructedRule = MS.Term * List(MS.Term) * List(Pattern * MS.Term) * Pattern * Rules
  op partitionConstructors : Context * MS.Term * Rules -> List(DestructedRule)

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

  def queryPat(pattern:Pattern): MS.Term -> MS.Term = 
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
	  def patDecompose(pattern: Pattern):List(Pattern*MS.Term) = 
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
	       
  
  
  def abstract(vs:List(String * Var),t:MS.Term,srt):MS.Term = 
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
      (case vars
        of [] -> foldr 
                 (fn((_,cond,body),default) -> 
		    failWith context 
		    (mkOptimizedIfThenElse(cond,body,break))
		    default) default rules
         | Cons _ -> 
	   let rules = (partition ruleType rules) in
           foldr (matchRules (context,break,vars)) default rules
      )
  
  def matchRules (context,break,vars) (rules,default) = 
      (case ruleType (hd rules)
        of Var -> matchVar(context,vars,rules,default,break)
         | Con -> matchCon(context,vars,rules,default,break)
	 | Alias(p1,p2) -> matchAlias(context,p1,p2,vars,rules,default,break)
         | Relax(pat,pred) -> 
           matchSubsort(context,pred,vars,rules,default,break)
         | Quotient _ -> matchQuotient(context,vars,rules,default,break)
      )
  def matchVar(context,terms,rules,default,break) = 
      let t = hd terms in
      let terms = tl terms in
      let rules = 
	  map
		 (fn ((Cons(pat,pats),cond,body):Rule) ->
		     (pats,substPat(cond,pat,t),substPat(body,pat,t))
		   | _ -> System.fail "Empty list of patterns ") rules
      in
      match(context,terms,rules,default,break)

  def matchCon(context,terms,rules,default,break) = 
      let t    = hd terms in
      let terms = tl terms in
      let rulePartition = partitionConstructors(context,t,rules) in
      let rule = foldr 
	           (fn ((query,newVars,lets,_,rules),default) ->   
	            mkOptimizedIfThenElse
		      (query, mkLet(lets,
				    match(context,newVars ++ terms,rules,break,break)),
		       default))
		   break rulePartition
      in
	 failWith context rule default
  def matchAlias(context,pat1,pat2,terms,rules,default,break) = 
      let t = hd terms in
      let rules = map (fn( (Cons(_,pats),cond,e):Rule)->
				(Cons(pat1,Cons(pat2,pats)),cond,e):Rule)
		  rules in
      match(context,cons(t,terms),rules,default,break)
  def matchSubsort(context,pred,t::terms,rules,default,break) =
      let _(* srt *) = inferType(context.spc,t) in
      let t1     = mkRestrict(context.spc,{pred = pred,term = t}) in
      let rules  = map (fn((RelaxPat(p,_,_))::pats,cond,e) ->
			      (cons(p,pats),cond,e))
                     rules
      in
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

def flattenLetDecl((pat:Pattern,term:MS.Term),(context,decls)) =
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
	  (context,cons((mkVarPat v,term),decls2 ++ decls))
       | _ -> (context,cons((pat,term),decls))

op  eliminatePattern: Context -> Pattern -> Pattern 
op  eliminateTerm   : Context -> MS.Term -> MS.Term
op  eliminateSort   : Context -> Sort -> Sort

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
		let term: MS.Term = 
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
   % sjw: Moved (Ref 0) in-line so it is reexecuted for each call so the counter is reinitialized for each
   % call. (This was presumably what was intended as otherwise there would be no need for mkContext
   % to be a function). This means that compiled functions will have the same generated variables
   % independent of the rest of the file.
   %let counter = (Ref 0) : Ref Nat in
   let mkContext = fn funName -> 
                    {counter = Ref 0,
		     spc     = spc,
		     funName = %spc.name ^"."^ % ???
		     funName,
		     term    = None} 
   in
     {importInfo    = spc.importInfo,
      sorts         = mapiAQualifierMap
                        (fn (qname, name, (sort_names, tyVars, defs)) ->
			    (sort_names, 
			     tyVars, 
			     map (fn (type_vars, srt) -> 
				  (type_vars, eliminateSort (mkContext name) srt))
			         defs))
			spc.sorts,
      ops           = mapiAQualifierMap
                        (fn (qname, name, (op_names, fixity, (tyVars, srt), defs)) ->
			    (op_names, 
			     fixity, 
			     (tyVars, eliminateSort (mkContext name) srt),
			     map (fn (type_vars, term) -> 
				  (type_vars, eliminateTerm (mkContext name) term))
			         defs))
			spc.ops,
      properties    = map (fn (pt, name, tyvars, term) -> 
    		  	      (pt, name, tyvars, eliminateTerm (mkContext name) term)) 
                          spc.properties
     } : Spec

}



(**********


% Arity raising must take place before or during 
% pattern matching compilation
% because that flattens the record patterns.

 def arityRaising(term:MS.Term):MS.Term = 
     case term
       of (Lambda 
	   [((VarPat(v1,_),pos0),(Fun(Bool true,_),_),
	     (Let([(pat as (RecordPat fields,_),(Var v2,_))],body),_))],_) -> 
	  if (v1 = v2) &  
	     all (fn(_,(VarPat v3,_))-> ~(v1 = v3) | _ -> false) fields
	  then 
	  let letTerm:MS.Term = mkRecord(map (fn(id,(VarPat v,p))-> (id,(Var v,p))) fields) in
	  (Lambda [(pat,mkTrue(),Match.mkLet([(mkVarPat v1,letTerm)],body))],pos0)
	  else term
	| _ -> term




(*******

 Computation of a decision DAG together with static checks
 for exhaustive and redundant branches. 
 Finally, proof-obligations for exhaustive branch coverage
 are generated. 

 ******)

(* 
   Internal representation of constructors and patterns supplied
   with adequate arity and span information.

 *)

sort con = 
 | CON :: {arity : Nat, span : Nat, name : String}
 | RELAX :: Term
 | QUOTIENT :: Term
 | CONST :: {const : const, span : Nat}
and const = 
 | NAT  :: Nat
 | BOOL :: Boolean
 | CHAR :: Char
 | STRING :: String

def printConst(c:const) = 
    case c
      of NAT n -> toString n
       | BOOL b -> Boolean.toString b
       | CHAR ch -> Char.toString ch
       | STRING s -> s

def printCon(c:con) = 
    case c 
      of CON{name,arity,span} -> name
       | RELAX term -> "relax("^printTerm term^")"
       | QUOTIENT term -> "quotient("^printTerm term^")"
       | CONST{const,span} -> printConst const

def span (c:con) = 
    case c
      of CON{span,arity,name} -> span
       | RELAX s -> 0 (* infinity *)
       | QUOTIENT _ -> 0
       | CONST{const,span} -> span

def arity (c:con) = 
    case c
      of CON{arity,span,name} -> arity
       | RELAX s -> 1
       | QUOTIENT _ -> 1
       | CONST _ -> 0

(*
 *  Internal simplified pattern representation 
 *)

sort pattern = 
  | Var :: String * Sort
  | Con :: con * List[pattern] * Sort
  | Alias :: pattern * pattern

(*
 * convertPattern : SpecEnvironment * Pattern -> pattern
 * 
 * Convert MetaSlang Ast pattern into internal simplified pattern
 * representation.
 * 
 *)

def coProductLength(spc,srt) = 
    case unfoldBase(spc,srt)
      of (CoProduct fields,_) -> length fields
       | _ -> System.fail "Not a co-product sort"

def relaxTerm(srt:Sort) = 
    case srt
      of (Arrow((Subsort(_,trm),_),_),_) -> trm
       | _ -> mkTrue() (* Should not happen *)
    

def convertPattern(spc,pat as (p,_):Pattern):pattern = 
    case p
      of VarPat var -> Var var
       | AliasPat(p1,p2) -> Alias(convertPattern(spc,p1),
				  convertPattern(spc,p2))
       | RelaxPat(p) -> Con(RELAX(relaxTerm(patternSort(p))),
			    [convertPattern(spc,p)],patternSort(pat)) 
       | QuotientPat(p,t) -> 
	 Con(QUOTIENT(t),[convertPattern(spc,p)],patternSort(pat))
       | EmbedPat(con,Some arg,srt) ->
	 Con(CON{arity = 1,name = con,span = coProductLength(spc,srt)},
	    [convertPattern(spc,arg)],srt) 
       | EmbedPat(con,None,srt) ->
	 Con(CON{arity = 0,name = con,span = coProductLength(spc,srt)},
	     [],srt) 
       | RecordPat(fields) -> 
	 Con(CON{arity = length fields,name = "",span = 1},
		map (fn(id,p) -> convertPattern(spc,p)) fields,
	        patternSort(pat))
	 (* 
	  * The empty constructor name is reserved for record
	  * constructors.
          *)
       | WildPat srt -> Var("",srt)
       | StringPat s -> Con(CONST{const = STRING s,span = 0},[],stringSort())
       | BoolPat b   -> Con(CONST{const = BOOL b,span = 2},[],boolSort())
       | NatPat n    -> Con(CONST{const = NAT n,span = 0},[],intSort())
       | CharPat ch  -> Con(CONST{const = CHAR ch,span = 256},[],charSort())

def patternSort(pat:pattern):Sort = 
    case pat
      of Var(_,srt) -> srt
       | Con(_,_,srt) -> srt
       | Alias(p1,p2) -> patternSort p1

(* Term descriptions *)

sort termd =
  | Pos :: con * List[termd]       (* All arguments in proper order *)
  | Neg :: List[con]                (* No duplicates                 *)

    
op printTermD : termd -> String
op printTermDs : List[termd] -> String

def printTermD(termd:termd) =
    case termd
      of Pos(con,termDs) ->    printCon(con)^"("^printTermDs(termDs)^")"
       | Neg conses ->    "Neg("^printCons conses^")"
and printTermDs tds = 
    case tds
      of [] -> ""
       | [td] -> printTermD td
       | (td::tds) -> printTermD td^","^printTermDs tds
and printCons cs = 
    case cs
      of [] -> ""
       | [c] -> printCon c
       | (c::cs) -> printCon c ^","^printCons cs

def Bot() = Neg [] : termd          (* The absence of information    *)

def bots n = tabulate(n, fn _ -> Bot())

(* Contexts, or inside-out partial term descriptions:
 * Example: The context [(c2, [a2, a1]), (c1, [b2, b1])] represents
 * a term description with a hole, of the form
 *           c1(b1, b2, c2(a1, a2, Bot, ..., Bot), Bot, ..., Bot) 
 * where the number of Bots is determined by the arity of c1 and c2.
 *) 


sort context = List[con * Option[termd] * List[termd]]

def augment(context:context,dsc) = 
    case context
      of [] -> []
       | Cons((con,optDsc,args),rest) -> 
	 cons((con,optDsc,cons(dsc,args)),rest)

(* Static matching *)



sort matchresult = | Yes | No | Maybe

def staticmatch (pcon:con) (td:termd) : matchresult = 
    case (pcon,td)
      of (RELAX _,_)  -> Maybe
       | (QUOTIENT _,_) -> Maybe
       | (_,Pos(scon,_)) -> 
         if pcon = scon then Yes else No
       | (_,Neg nonset)  ->
        if exists (fn x -> x =  pcon) nonset then 
           No
        else if span pcon = 1 + length nonset then 
           Yes
        else 
           Maybe

(* Managing partial terms and contexts *)

def addneg (dsc:termd) (con:con) = 
    case dsc 
      of Neg nonset -> Neg(cons(con,nonset)):termd
       | _ -> dsc

op revappend : [T] List[T] * List[T] -> List[T]
def revappend(xs,res) = 
    case xs
      of [] -> res
       | x::xs -> revappend(xs,cons(x,res))

def builddsc(ctx,dsc0:termd,work) = 
    let
	def loop(context:context,dsc:termd,work) = 
	    case (context,work)
	      of ([],[]) -> dsc
	       | ((con,Some dsc,_)::rest,work) -> dsc
	       | ((con,None,args)::rest,(_,_,sargs)::work) -> 
	         builddsc(rest,(Pos(con, revappend(args,cons(dsc,sargs)))),work)
	       |  _ -> System.fail "Match.builddsc"
    in
	loop(ctx,dsc0,work)
    

(* Runtime data access and matching actions *)

sort access = 
 | Select :: String
 | Project :: Nat
 | Restrict :: Term
 | Choose :: Term 
def selectproject(sel,i):access = 
    case sel
      of "" -> Project(i)  (* 
			      The empty string is reserved for record
			      constructors 
			    *)
       | _ -> Select(sel)
def restrict(pred):access = Restrict pred
def chooseTerm(pred):access = Choose pred

def printAccess (access:access) = 
    case access
      of Project(i) -> 
         "project_"^toString i
       | Select(sel) -> 
         "select_"^sel
       | Restrict s -> "restrict_"^printTerm s
       | Choose s -> "choose_"^printTerm s

sort var = String * Sort

sort test = 
 | Embedded :: String * var
 | Relaxed  :: Term * var
 | Condition :: Term

def testToTerm(test:test) = 
    case test
      of Embedded(embedOp,(name,srt)) -> 
	 mkApply(mkEmbedded(embedOp,srt),mkVar (name,srt))
       | Relaxed(term,(name,srt)) -> 
	 mkApply(term,mkVar(name,srt))
       | Condition term -> term

def printTest(test:test) = 
    (case test
       of Embedded(s,(var,srt)) ->  s^"?("^var^")"
        | Relaxed(s,(var,srt)) -> printTerm s^"?("^var^")"
        | Condition term -> printTerm term)

sort decl = var * access * var


sort dec =
  | Failure
  | Success :: Term			(* right-hand side *)
  | IfEq :: test * decision * decision
  | Let  :: List[decl] * decision 
and decision = Ref[{tree : dec, refs : Ref[Nat]}]

def shared (Ref {refs,tree}   : decision) = ! refs > 1
def used   (Ref {refs,tree}   : decision) = ! refs > 0
def incrnode (Ref {refs,tree} : decision) = refs := 1 + ! refs
op mkDecision : dec -> decision
def mkDecision t = Ref {tree = t, refs = Ref 0}:decision


(* Hash-consing, to get a decision dag rather than a decision tree *)

def insertNode(table,node,ts) =  
    (case HashTable.lookup(node,table)
       of Some n -> n
        | None ->
	  let rnode = mkDecision node
	  in 
	    (
	       app incrnode ts;
	       HashTable.insert(node,rnode,table);
	       rnode
	    )
     )

op  unique : HashTable.HashTable[dec,decision] * dec -> decision
def unique (table,node:dec) = 
    (case node
       of IfEq(_, t1, t2) -> 
          if t1 = t2 then t1 else insertNode(table,node,[t1,t2])
        | Let([],t) -> t
        | Let(_,t) -> insertNode(table,node,[t])
        | _ -> System.fail "Match.unique")

def compile(table,failure,allmrules) = 
    let
	def fail(dsc,rules) = 
            case rules
	      of [] -> failure
	       | (pat1,cond1,rhs1)::rulerest -> 
	         match(pat1,"x",dsc,[],[],cond1,rhs1,rulerest)
	and succeed(ctx,work,cond:Term,rhs,rules,fail) =
	    case work
	      of [] -> 
	         (case cond
	       	    of (Fun(Bool true,_),_) -> rhs
		     | _ -> 
		  unique
		    (table,IfEq
		      (Condition cond,
		       rhs,
		       mkDecision Failure
		      )
		    ))
	       | work1::workrest ->
	    (case work1: List[pattern] *List[String]  * List[termd]
	       of 
		([], [], []) -> 
		succeed(ctx,workrest,cond,rhs,rules,fail)
	      | ((Alias(pat1,pat2):pattern)::patrest, 
		  obj1::objrest, dsc1::dscrest) ->
		succeed(ctx,
		cons((cons((pat1,cons(pat2,patrest))),
			   cons(obj1,cons(obj1,objrest)),
			   cons(dsc1,cons(dsc1,dscrest))),workrest),
		cond,rhs,rules,fail)
	      | (pat1::patrest, obj1::objrest, dsc1::dscrest) ->
		    match(pat1,obj1,dsc1,ctx, 
		    (cons((patrest, objrest, dscrest),workrest)),cond,rhs,rules)
	      | ([],[],(Pos(con,_):termd)::_) -> 
		    System.fail ("Too much dsc "^printCon con)
	      | ([],[],(Neg(con::_):termd)::_) -> 
		    System.fail ("Too much negative dsc "^printCon con)
	      | ([],_,[]) -> System.fail "Too much obj"
	      | (_,[],[]) -> System.fail "Too much pat"

	      | _ -> System.fail "Match.succeed")
	and match(pat:pattern,obj,dsc,ctx,work,cond,rhs,rules) = 
	    case pat
	      of Var s -> 
		 let def failP() = fail(builddsc(ctx,dsc,work),rules) in
		 let ctx = augment(ctx,dsc) in
		     succeed(ctx,work,cond,rhs,rules,failP)
		 
	       | Con(pcon as CON {name,arity,span},pargs,srt) -> 
		 let def getdargs(dsc:termd) = 
		         case dsc
			   of Neg _ -> tabulate(arity,fn _ -> Bot())
		            | Pos(con,dargs) -> dargs
		 in
		 let def decls() = 
			 tabulate(arity,fn i -> 
			      let sp = selectproject(name,i+1) in
			      let pat_i = nth(pargs,i) in
			      let srt_i = patternSort(pat_i) in
			      let s  = if name = "" 
					then "project"^toString i
				       else "select_"^name
			      in
				  ((s^obj,srt_i),sp,(obj,srt))
			      )
		 in
	         let def failP newdsc = 
			 fail(builddsc(ctx,newdsc,work),rules)
		 in
		 let def staticfail() = failP dsc in
		 let def dynamicfail() = failP (addneg dsc pcon) in
		 let def staticsuccess(oargs) = 
			 succeed(cons((pcon,None,[]),ctx),
				 cons((pargs,oargs,getdargs dsc),work),
				 cond,rhs,rules,staticfail)
		 in
		 let def succeedP() = 
			 let decls = decls() in
			 let oargs = map (fn((d,_),_,_)-> d) decls in 
			 let dec = staticsuccess(oargs) in
			     unique(table,Let(decls,dec))
		 in
		 let test:test = Embedded(name,(obj,srt)) in
		 (case staticmatch pcon dsc
		    of Yes   -> staticsuccess
		           (tabulate(arity,
				fn i-> printAccess
					(selectproject(name,i+1))))
		     | No    -> staticfail() 
		     | Maybe -> 
		       unique(table,IfEq(test, 
				       succeedP (),
				       dynamicfail()))
		 )

		   
	       | Con(pcon as RELAX term,pargs,srt) ->
		 let acc  = restrict(term) in 
		 let oarg = "relax_"^obj in 
		 let srt0 = termSort term in
		 let decls = [((oarg,srt0),acc,(obj,srt))] in 
		 let test:test = Relaxed(term,(obj,srt)) in 
		 let def dynamicfail() = 
			 fail(builddsc(ctx,dsc,work),rules)  in 
		 let succeed = 
			 unique
			   (table,Let
			    (decls,
			     succeed(cons((pcon,Some dsc,[]),ctx),
				     cons((pargs,[oarg],
				      [Bot()]),work),
				     cond,rhs,rules,dynamicfail)))
		 in
		     unique 
		       (table,IfEq(test,  succeed,  dynamicfail()) )
	    | _ -> System.fail "Match case not covered"
		 
    in
	fail(Bot(),allmrules)
   

def mkTest(p,l:Term,r:Term):Term = 
    case (l,r)
      of ((Fun(Bool true,_),_), (Fun(Bool true,_),_)) -> r
       | ((Fun(Bool false,_),_),(Fun(Bool false,_),_)) -> r
       | ((Fun(Bool true,_),_), (Fun(Bool false,_),_)) -> testToTerm p
       | _ -> mkIfThenElse(testToTerm p,l,r)

def mkDecl(v1,access:access,v2) = 
    case access
      of Select embedOp -> (mkVarPat v1,mkSelectTerm(embedOp,mkVar v2))
       | Project n -> (mkVarPat v1,mkProjectTerm(context.spc,toString n,mkVar v2))
       | Restrict query -> 
	 (mkVarPat v1,mkRestrict{term = mkVar v2,pred = query})
       | Choose equiv -> 
	 (mkVarPat v1,mkChoose(mkVar v2,equiv))

(* Generate proof obligation for exhaustive match branching *)
def checkExhaustive(dag as Ref {tree,refs}:decision):Term = 
    (case tree
      of Failure -> mkFalse()
       | Success _ -> mkTrue()
       | IfEq(test,l,r) -> 
	 let l = checkExhaustive(l) in 
	 let r = checkExhaustive(r) in
	 mkTest(test,l,r)
	 
       | Let(decls,d) -> 
	 let d = checkExhaustive(d) in
	     (case d
	       of (Fun(Bool _,_),_) -> d
		| _ -> mkLet(map mkDecl decls,d)
	     ))

sort MatchResult = | Redundant | NonExhaustive :: Term | Ok  

    
def checkMatch (spc,rules: Match): MatchResult = 
    let	failure = mkDecision Failure    in
    let	table = HashTable.initialize(fn (x,y) -> x = y,20)    in
    let	rules = map 
		(fn (pat,cond,rhs)->
		    (convertPattern(spc,pat),
		     cond,
		     mkDecision (Success rhs))
		) rules
    in
    let	dag = compile(table,failure,rules)  in
    (case find (fn (_,_, rhs) -> ~ (used rhs)) rules
       of Some (_,_,Ref{tree = Success s,refs}:decision) -> Redundant 
        | _ -> 
         if used failure
	    then NonExhaustive(checkExhaustive(dag))
	 else Ok)   

*********)
