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

PatternMatch qualifying spec
  import ArityNormalize
  import Simplify
   
  % import MetaSlangPrint	% imported by ArityNormalize

  op  translateMatch : Spec -> Spec

  def match_type srt = mkBase (Qualified("TranslationBuiltIn","Match"), [srt])

  def mkBreak    srt = mkOp (Qualified("TranslationBuiltIn","mkBreak"), match_type srt)

  def isBreak (term : MS.Term) = 
    case term of
      | Fun (Op (Qualified("TranslationBuiltIn","mkBreak"), _), _, _) -> true
      | _ -> false

  def mkSuccess (srt0, trm) = 
    let srt = mkArrow(srt0,match_type srt0) in 
    mkApply (mkOp (Qualified("TranslationBuiltIn","mkSuccess"), srt), 
             trm)

  def isSuccess trm = 
    case trm of
      | Apply (Fun (Op(Qualified("TranslationBuiltIn","mkSuccess"), _), _, _), _, _) -> true
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

  op failWith (context : Context) (t1 : MS.Term) (t2 : MS.Term) : MS.Term =
    if isBreak t2 then 
      t1 
    else 
      if isSuccess t1 then 
        let _ = warnUnreachable context in
        t1
      else
        let srt  = inferType (context.spc, t1) in
        let srt  = mkArrow (mkProduct [srt,srt], srt) in
        let trm  = mkApply (mkOp (Qualified("TranslationBuiltIn","failWith"), srt), 
                            mkRecord [("1",t1), ("2",t2)])
        in
        trm

  def warnUnreachable context =
    writeLine ("Warning: Redundant case in " ^ context.funName ^ "\n" ^ 
                 (case context.term of
                    | Some t -> printTerm t
                    | _ -> ""))
  
  type Rule  = List Pattern * MS.Term * MS.Term
  type Rules = List Rule
  
  type Context = {counter    : Ref Nat,
		  spc        : Spec,
		  funName    : String,
		  errorIndex : Ref Nat,
		  term       : Option MS.Term}

  def storeTerm (tm, ctx) =
    ctx << {term = Some tm}

%  op  mkProjectTerm : Spec * Id * MS.Term -> MS.Term
%  def mkProjectTerm = SpecEnvironment.mkProjectTerm
%  op  mkRestrict :    Spec * {pred:MS.Term,term: MS.Term} -> MS.Term
%  def mkRestrict = SpecEnvironment.mkRestrict
  
  op match : Context * List MS.Term * Rules * MS.Term * MS.Term -> MS.Term

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

   Quotient rule:

	(v:Q)::vars
	[(QuotientPat(pat: t, Q)::patterns,cond,e)]
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
	  of (quotient(Q) pattern,...) -> term
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

  def embedded (constructorName : String) term = 
    mkApply (mkEmbedded (constructorName, termSort term),
             term)


  def relaxed predicate term = 
    mkApply (predicate, term)
 
  def equalToConstant (srt, constantTerm : MS.Term) term =
    mkEquality (srt, constantTerm, term)

  def mkLet (lets : List (Pattern * MS.Term), term) = 
    case lets of
      | [] -> term : MS.Term
      | _  -> MS.mkLet (lets, term)
        	
  op [A,B] partition : (A -> B) -> List A        -> List (List A)
  op [A]   tack      : A        -> List (List A) -> List (List A)

  def partition f qs = 
    case qs of
      | [] -> []
      | [x] -> [[x]]
      | Cons (x, Cons (y, xs)) -> 
        if f x = f y then
          tack x (partition f (y::xs))
        else 
          Cons ([x], partition f (y::xs))
      
  def tack x (xs::xss) = (x::xs) :: xss

  type RuleType = | Var 
                  | Con 
                  | Alias      Pattern * Pattern
                  | Relax      Pattern * MS.Term 
                  | Quotient   Pattern * SortName
                  | Restricted Pattern * MS.Term 

  op ruleType (q : Rule) : RuleType = 
    case q of
      | ((VarPat        _)                  ::_, _, _) -> Var
      | ((WildPat       _)                  ::_, _, _) -> Var

      | ((EmbedPat      _)                  ::_, _, _) -> Con
      | ((RecordPat     _)                  ::_, _, _) -> Con
      | ((StringPat     _)                  ::_, _, _) -> Con
      | ((BoolPat       _)                  ::_, _, _) -> Con
      | ((NatPat        _)                  ::_, _, _) -> Con
      | ((CharPat       _)                  ::_, _, _) -> Con

      | ((AliasPat      (p1,  p2,        _))::_, _, _) -> Alias      (p1,  p2)
      | ((QuotientPat   (pat, qid,       _))::_, _, _) -> Quotient   (pat, qid)
      | ((RestrictedPat (pat, bool_expr, _))::_, _, _) -> Restricted (pat, bool_expr)

  op [a] printRule (pats : List (APattern a), cond : ATerm a, body : ATerm a) : () =
    let _ = toScreen "Pattern : " in
    let _ = app (fn p -> toScreen (printPattern p ^ " ")) pats in
    let _ = writeLine "" in
    let _ = writeLine ("Condition: " ^ printTerm cond) in
    writeLine ("Body: " ^ printTerm body)

  def sameConstructor spc (pat1 : Pattern, pat2 : Pattern) = 
    case (pat1, pat2) of
      | (RecordPat _,         RecordPat _       ) -> true
      | (EmbedPat (e1,_,_,_), EmbedPat(e2,_,_,_)) -> e1 = e2
      | _ -> equivPattern? spc (pat1, pat2)
      

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

  type DestructedRule = MS.Term * List MS.Term * List (Pattern * MS.Term) * Pattern * Rules

  op partitionConstructors : Context * MS.Term * Rules -> List DestructedRule

  op freshVar (context : Context, srt : Sort) : Var =
   let num = ! context.counter + 1 in
   (context.counter := num;
    ("pV" ^ (Nat.show num), srt))

  op freshVars (num : Nat, context : Context, pat : Pattern) : List (String * Var) =
   case num of
     | 0 -> []
     | 1 -> [("", freshVar (context, patternSort pat))]
     | _ ->
       case pat of
         | RecordPat(fields,_) -> 
           map (fn (l, p) -> (l, freshVar (context, patternSort p)))
               fields
         | _ -> System.fail "Record pattern expected"

  (* 
   *  Generates the query term used to identify variable being an instance
   *  of the pattern 
   *)

  op queryPat (pattern : Pattern) : MS.Term -> MS.Term = 
   case pattern of
     | EmbedPat  (e,_,_, _) -> embedded e
     | NatPat    (n,     _) -> equalToConstant (natSort,    mkNat    n)
     | CharPat   (c,     _) -> equalToConstant (charSort,   mkChar   c)
     | BoolPat   (b,     _) -> equalToConstant (boolSort,   mkBool   b)
     | StringPat (s,     _) -> equalToConstant (stringSort, mkString s)
     | RecordPat _          -> (fn _ -> trueTerm)
     | _                    -> (fn _ -> trueTerm)
              

  op coproductFields (spc: Spec, srt: Sort) : List (Id * Option Sort) = 
   let srt = unfoldBase (spc, srt) in
   case srt of
     | CoProduct (fields, _) -> fields
     | Subsort   (tau, _, _) -> coproductFields (spc, tau)
     | Base (Qualified ("List", "List"), [x], _) -> 
       [("Nil",  None), 
        ("Cons", Some (Product ([("1", x), ("2", srt)], 
                                sortAnn srt)))]
     | _ -> System.fail ("CoProduct sort expected, but got " ^ printSort srt)

  def partitionConstructors (context, t, rules) =
    let
      def patDecompose (pattern : Pattern) : List (Pattern * MS.Term) = 
        case pattern of
          | RecordPat (pats,_) -> 
            map (fn (index, p)-> (p, mkProjectTerm(context.spc, index, t))) 
                pats
          | EmbedPat (id, Some p, srt, _) -> 
            let fields = coproductFields (context.spc, srt) in
            let trm = (case findLeftmost (fn (id2, s) -> id = id2) fields of
                         | Some (_, Some s) ->
                           mkApply ((Fun(Select id, mkArrow (srt, s), noPos)), 
                                    t)
                         | _ -> System.fail "Selection index not found in product")
            in
            [(p, trm)]
          | _ -> []	

      def insert (rule, rules : List DestructedRule) : List DestructedRule = 
        case (rule : Rule, rules) of
          | ((pat::pats,cond,body),[]) -> 
            let query         = queryPat pat t   in
            let decomposition = patDecompose pat in
            let newVars       = map (fn (p, _) -> freshVar (context, patternSort p)) 
                                    decomposition 
            in
            let lets          = ListPair.map (fn ((p, t), v)-> (mkVarPat v, t))
                                             (decomposition, newVars) 
            in
            let newPats       = map (fn (p, _) -> p) decomposition in
            [(query, map mkVar newVars, lets, pat, [(newPats ++ pats, cond, body)])]

          | ((pat::pats, cond, body),
             (destrRule as (query, newVars, lets, pat2, rules2)) :: rules) -> 
            let spc = context.spc in
            if sameConstructor spc (pat, pat2) then
              let decomposition = patDecompose pat in
              let newPats       = map (fn (p, _) -> p) decomposition in
              let rule          = (newPats ++ pats, cond, body) in
              (query, newVars, lets, pat2, rule :: rules2) :: rules
            else 
              if exists? (fn (_,_,_,pat3,_) -> sameConstructor spc (pat,pat3)) rules then
                destrRule :: insert (rule, rules)
              else 
                insert (rule, []) ++ (destrRule :: rules)
            | _ -> rules (* should not happen *)
      in
      foldr insert [] rules 
	       
  op abstract (vs: List (String * Var), tm : MS.Term, srt) : MS.Term = 
    let st? = simplifyPatternMatchResult tm in
    let tm  = case st? of
                | Some tm -> tm
                | _ -> mkApply (mkOp (Qualified("TranslationBuiltIn","block"),
                                      mkArrow (match_type srt, srt)), 
                                tm)
    in
    let pat = case vs of 
                | [(_,v)] -> mkVarPat v
                | _ -> RecordPat (map (fn (l, v)-> (l, mkVarPat v)) vs, 
                                  noPos)
    in
    Lambda ([(pat, trueTerm, tm)], noPos)

  def match (context, vars, rules, default, break) = 
    case vars of
      | [] -> foldr (fn ((_,cond,body),default) -> 
                       failWith context 
                                (Utilities.mkIfThenElse (cond, body, break))
                                default)
                    default
                    rules
      | Cons _ -> 
        let rules = (partition ruleType rules) in
        foldr (matchRules (context, break, vars)) 
              default 
              rules
  
  def matchRules (context, break, vars) (rules, default) = 
    case ruleType (head rules) of
      %% Restricted should be unnecessary because top-level Restricteds have been removed in eliminateTerm
      | Var                        -> matchVar        (context,           vars, rules, default, break)
      | Con                        -> matchCon        (context,           vars, rules, default, break)
      | Alias      (p1,  p2)       -> matchAlias      (context, p1, p2,   vars, rules, default, break)
      | Relax      (pat, pred)     -> matchSubsort    (context, pred,     vars, rules, default, break)
      | Restricted (pat, bool_exp) -> matchRestricted (context, bool_exp, vars, rules, default, break)
      | Quotient    _              -> matchQuotient   (context,           vars, rules, default, break) 
      
  def matchVar (context, terms, rules, default, break) = 
    let tm    = head terms in
    let terms = tail terms in
    let rules = map (fn (rule : Rule) ->
                       case rule of
                         | (Cons (pat, pats), condn, body) ->
                           (pats, 
                            substPat (condn, pat, tm),
                            substPat (body,  pat, tm))
                         | _ -> System.fail "Empty list of patterns ")
                    rules
      in
      match (context, terms, rules, default, break)

  def matchCon (context, terms, rules, default, break) = 
    let term          = head terms in
    let terms         = tail terms in
    let rulePartition = partitionConstructors (context, term, rules) in
    let rule          = foldr (fn ((query, newVars, lets, _, rules), default) ->   
                                 Utilities.mkIfThenElse (query, 
                                                         mkLet (lets,
                                                                match (context,
                                                                       newVars ++ terms,
                                                                       rules,
                                                                       break,
                                                                       break)),
                                                         default))
                              break 
                              rulePartition
    in
    failWith context rule default

  def matchAlias (context, pat1, pat2, terms, rules, default, break) = 
    let tm    = head terms in
    let rules = map (fn (rule : Rule) ->
                       case rule of
                         | (Cons (_, pats), cond, e) ->
                           (Cons (pat1, Cons (pat2, pats)), cond, e))
                    rules 
    in
    match (context, tm :: terms, rules, default, break)

  def matchSubsort (context, pred, tm::terms, rules, default, break) =
    let _(* srt *) = inferType  (context.spc, tm) in
    let t1         = mkRestrict (context.spc, {pred = pred, term = tm}) in
    failWith context 
             (Utilities.mkIfThenElse(mkApply (pred, tm),
                                     match (context, t1::terms, rules, break, break),
                                     break))
             default 

  def matchRestricted (context, bool_expr, tm::terms, rules, default, break) =
    let rules  = map (fn rule ->
                        case rule of
                          | ((RestrictedPat (p,_,_))::pats, cond, e) ->
                            (p :: pats,
                             mkSimpConj [cond, bool_expr], 
                             e)
                          | _ -> rule)
                     rules
    in
    match (context, tm::terms, rules, default, break) 

  def matchQuotient (context : Context, tm::terms, rules, default, break) = 
    let q = inferType (context.spc, tm) in
    case unfoldBase (context.spc, q) of
      | Quotient (srt, pred, _) -> 
        %%
        %%    Given current implementation of choose, we compile
        %%     t1 = choose[q] t 
        %%
        let v     = ("v",srt)                                    in
        let f     = mkLambda (VarPat (v, noPos), Var (v, noPos)) in
        let t1    = mkApply  (mkChooseFun (q, srt, srt, f), tm)  in
        let rules = map (fn ((Cons ((QuotientPat (p, pred, _)):Pattern, pats), cond, e) : Rule) ->
                           (p::pats, cond, e))
                        rules 
        in
        failWith context
                 (match (context, t1::terms, rules, break, break))
                 default 	
      | _ -> fail ("Internal confusion in matchQuotient: expected " ^ printSort q ^ " to name a quotient type")


 %% fn (x as pat) -> bod  -->  fn x -> let pat = x in bod
 %% Without this other normalizations such as arity normalization break
 op normalizeSimpleAlias (rules: Match) : Match =
  case rules of
    | [(AliasPat (VarPat (v, a1), p2, a2), cond, body)] ->
      [(VarPat (v, a1), 
        trueTerm, 
        Apply (Lambda ([(p2, cond, body)], a2), 
               Var (v, a1), 
               a2))]
    | _ -> rules

 def splitPattern (arity, pat : Pattern) :List Pattern =
   if arity = 1 then 
     [pat] 
   else
     case pat of
       | RecordPat  (fields, _) -> map (fn (_, p)-> p) fields
       | WildPat    (srt,    _) -> tabulate(arity, fn _ -> pat)
       | _ -> System.fail "Unexpected pattern" 

 def zipFields (fields, terms) =
   case (fields, terms) of
     | ([], []) -> []
     | ((_, pat)::fields, (_,t)::terms) -> (pat,t) :: zipFields (fields, terms)
     | _ -> System.fail "zipFields: Uneven length of fields"

 def flattenLetDecl ((pat : Pattern, term : MS.Term), (context, decls)) =
   case (pat, term) of
     | (WildPat (srt,_), Var _)        -> (context, decls)
     | (WildPat (srt,_), Record([],_)) -> (context, decls)
     | (WildPat (srt,_), term)         -> (context, Cons ((mkVarPat (freshVar (context, patternSort pat)), term), 
                                                          decls))

     | (RecordPat (fields, _), Record (terms, _)) ->
       foldr flattenLetDecl 
             (context,decls) 
             (zipFields (fields, terms)) 

     | (RecordPat(fields,_),term) -> 
       let v      = freshVar (context, inferType(context.spc, term)) in
       let vTerm  = mkVar v 				             in
       let decls1 = map (fn (id, pat) -> (pat, mkProjectTerm (context.spc, id, vTerm))) 
                        fields 
       in
       let (context, decls2) = foldr flattenLetDecl (context,decls) decls1 in
       (context, Cons ((mkVarPat v, term), decls2 ++ decls))

     | _ -> 
       (context, (pat, term) :: decls)

 op eliminatePattern: Context -> Pattern -> Pattern 
 op eliminateTerm   : Context -> MS.Term -> MS.Term
 op eliminateSort   : Context -> Sort    -> Sort

 def eliminatePattern context pat = 
   case pat of

     | AliasPat (p1,                          p2,                          a) -> 
       AliasPat (eliminatePattern context p1, eliminatePattern context p2, a)

     | VarPat ((n, s),                       a) -> 
       VarPat ((n, eliminateSort context s), a)

     | EmbedPat (i, Some p,                            s,                       a) ->
       EmbedPat (i, Some (eliminatePattern context p), eliminateSort context s, a)

     | EmbedPat (i, None, s,                       a) ->
       EmbedPat (i, None, eliminateSort context s, a)

     | RecordPat (fields,                                                   a) -> 
       RecordPat (map (fn (i, p)-> (i, eliminatePattern context p)) fields, a)

     | WildPat   (s, a) -> VarPat (freshVar (context, eliminateSort context s), a)
     | StringPat (s, a) -> StringPat (s, a)
     | BoolPat   (b, a) -> BoolPat   (b, a)
     | CharPat   (c, a) -> CharPat   (c, a)
     | NatPat    (n, a) -> NatPat    (n, a)

     | QuotientPat  (p,                          qid, a) ->
       QuotientPat  (eliminatePattern context p, qid, a)

     | RestrictedPat (p,                          tm,                       a) ->
       RestrictedPat (eliminatePattern context p, eliminateTerm context tm, a)

     | SortedPat (p,                          ty,                       a) ->
       SortedPat (eliminatePattern context p, eliminateSort context ty, a)

 def eliminateSort context srt =
   case srt of

     | Arrow (s1,                       s2,                       a) -> 
       Arrow (eliminateSort context s1, eliminateSort context s2, a)

     | Product (fields,                                                 a) -> 
       Product (map (fn (i, s) -> (i, eliminateSort context s)) fields, a)

     | CoProduct (fields, a) -> 
       CoProduct (map (fn (i, x) -> 
                         (i,
                          case x of
                            | Some s -> Some (eliminateSort context s)
                            | _ -> None))
                      fields,
                  a)

     | Quotient (s,                       tm,                       a) -> 
       Quotient (eliminateSort context s, eliminateTerm context tm, a)

     | Subsort (s,                       tm, a) -> 
       % Subsort predicates aren't used in code generation (??), so omit eliminateTerm context tm,  ????
       Subsort (eliminateSort context s, tm, a) 

     | Base (qid, sorts,                             a) -> 
       Base (qid, map (eliminateSort context) sorts, a)

     | Boolean _ -> srt
     | TyVar   _ -> srt
     | Any     _ -> srt
     | And (srts,     a) -> And (map (eliminateSort context) srts, a)
     | Pi  (tvs, srt, a) -> Pi  (tvs, eliminateSort context srt,   a)

 (* Generate the default catch all case given a set of rules *)

 def makeFail (context, srt, _(* term *)) = 
   let index = ! context.errorIndex + 1 in
   (context.errorIndex := index;
    let srt1 = mkArrow(srt,match_type srt) in
    let msg  = "Nonexhaustive match failure [\#" ^ (show index) ^ "] in " ^ context.funName in
    mkApply (mkOp(Qualified("TranslationBuiltIn","mkFail"), srt1),
	     mkString msg))

 def makeDefault (context : Context, srt, rules, vs, term) = 
   let 
     def loop (rules : Match, firstRules) = 
       case rules of

         | [] -> 
           (reverse firstRules, makeFail (context, srt, term))

         | [(WildPat _, Fun (Bool true, _, _), body)] ->
           (reverse firstRules, mkSuccess (srt, body))

         | [(VarPat (v, _), Fun(Bool true, _, _), body)] ->
           let term : MS.Term = 
               case vs of
                 | [(_, v)] -> Var (v, noPos)
                 | _ -> Record (map (fn(l,v)-> (l, mkVar v)) vs, 
                                noPos) 
           in
           let body = mkLet ([(VarPat (v, noPos),term)], body) in
           (reverse firstRules, mkSuccess (srt, body))

         | rule :: rules ->
           loop (rules, rule :: firstRules)
   in
   loop (rules, [])

 def wildPattern? rule =
   case rule of
     | (WildPat _,     Fun (Bool true,_,_), _) -> true
     | (VarPat (v, _), Fun (Bool true,_,_), _) -> true
     | _ -> false

 def checkUnreachableCase (context, term, rules) =
  let 
    def nonfinalWildPattern? rules =
      case rules of
        | []  -> false
        | [_] -> false
        | rule :: rules ->
          wildPattern? rule || nonfinalWildPattern? rules
  in
  if nonfinalWildPattern? rules then
    writeLine ("Warning: Unreachable case in " ^ context.funName ^ "\n" ^ printTerm term)
  else 
    ()

 %%% The last case of a Lambda case has the obligation of always matching, so if it
 %%% is has | (such-that) clause, there is the obligation that it is true

 op alwaysCheckRestrictedPatInLambda?: Boolean = false

 def eliminateTerm context term = 
   case term of
     | Lambda(rules,_) ->
       let rules = normalizeSimpleAlias rules in
       let arity = matchArity(rules) in
       let rules = map (fn (p, c, b)-> (eliminatePattern context p,
                                        eliminateTerm    context c,
                                        eliminateTerm    context b)) 
                       rules 
       in
       if simpleAbstraction rules then
         let rules = map (fn (p, c, a) -> (deRestrict p, c, a)) rules in
         Lambda (rules, noPos)
       else 
	 %%% let _ = writeLine "Elimination from lambda " in
	 let _ = checkUnreachableCase (context, term, rules) in
         %%% Move RestrictedPat conditions to condition
         %%% Not singleton because obligation should ensure this is always true
         %%% unless alwaysCheckRestrictedPatInLambda?
	 let rules =
             case rules of

               | [(RestrictedPat (pat, rcond, _), cond, bdy)] | ~ alwaysCheckRestrictedPatInLambda? ->
                 [(pat, cond, bdy)]

               | _ -> map (fn rule ->
                             case rule of 
                               | (RestrictedPat (pat, rcond, _), cond,                     bdy) ->
                                 (pat,                           mkSimpConj [rcond, cond], bdy)
                               | _ -> rule)
                          rules
	 in			      
	 let (pat, cond, bdy)  = head rules                                      in
	 let bdySort           = inferType (context.spc, bdy)                    in
	 let vs                = freshVars (arity, context, pat)                 in
	 %%%	 let  _ = writeLine "Elimination from lambda: rules "            in
	 let (rules, default)  = makeDefault (context, bdySort, rules, vs, term) in
	 let rules = map (fn (p, c, t) -> 
                            (splitPattern(arity,p), c, mkSuccess (bdySort, t))) 
                         rules 
         in
	 let vars = map (fn (_, v) -> mkVar v) vs                                            in
	 let trm  = match (storeTerm (term, context), vars, rules, default, mkBreak bdySort) in
	 let trm  = abstract (vs, trm, bdySort)                                              in
	 trm

     (* 
      * Treatment of let-bound patterns is optimized with respect to a number
      * of special cases: Wildcards, trivially satisfiable patterns, Non-flattened patterns, et.c.
      *)

     | Let (decls, body,_) -> 
       let decls = map (fn (p, e) -> (eliminatePattern context p,
                                      eliminateTerm context e))
                       decls
       in
       let body  = eliminateTerm context body in
       (* Translate non-recursive non-simple let patterns into application *)
	 	 
       let (context, decls) = 
           foldr flattenLetDecl (context,decls) [] 
       in
       if forall? (fn (pat, _)-> simplePattern pat) decls then
         mkLet(decls,body)
       else 
	 let (pats, terms) = unzip decls in
	 % let _ = writeLine "Let pattern elimination " in
	 % let _ = app (fn p -> writeLine (printPattern p)) pats in
         let trm = 
      	     case terms of
	       | [tm]  -> tm
               | terms -> mkTuple terms
         in
         let bdySrt = inferType (context. spc, body) in
         % let _  = writeLine "Let pattern elimination tabulating " in
         let vs = map (fn pat -> freshVar (context, patternSort pat)) pats in
         let (vars,_) = 
             foldl (fn ((vars, num), v) -> 
                      (Cons ((Nat.show num, v), vars), num + 1))
                   ([],1) 
                   vs
         in
         % let _ = writeLine "Let pattern elimination: match" in
         let tm = match (context,
                         map mkVar vs,
                         [(pats, trueTerm, mkSuccess (bdySrt, body))] : Rules,
                         makeFail (context, bdySrt, term),
                         mkBreak bdySrt) 
         in
         let tm = abstract (vars, tm, bdySrt) in
         mkApply (tm,trm)

      %% case e of p -> body --> let p = e in body

      | Apply (Lambda ([(p, Fun (Bool true,_,_), body)],_), e, pos) ->
        eliminateTerm context (Let ([(p,e)], body, pos))

      | Apply (t1,                       t2,                       a) -> 
	Apply (eliminateTerm context t1, eliminateTerm context t2, a)

      | Record (fields,                                                   a) ->
	Record (map (fn (id, t) -> (id, eliminateTerm context t)) fields, a)

      | Bind (b, vars,                                             tm,                       a) -> 
	Bind (b, map (fn(n,s)-> (n,eliminateSort context s)) vars, eliminateTerm context tm, a)

      | The ((id, srt),                       tm,                       a) -> 
	The ((id, eliminateSort context srt), eliminateTerm context tm, a)

      | LetRec (decls, body, a) -> 
	LetRec (map (fn ((n, s), t)->
                       ((n, eliminateSort context s),
                        eliminateTerm context t)) 
                    decls,
                eliminateTerm context body,
                a)

      | Var ((n, s),                       a) -> 
        Var ((n, eliminateSort context s), a)

      | Fun (f, s,                       a) -> 
        Fun (f, eliminateSort context s, a)

      | IfThenElse (s1, s2, s3, a) -> 
        IfThenElse (eliminateTerm context s1,
                    eliminateTerm context s2,
                    eliminateTerm context s3,
                    a)

      | Seq (terms,                             a) -> 
        Seq (map (eliminateTerm context) terms, a)

      | And (tm                       :: r_tms, a) -> 
        And (eliminateTerm context tm :: r_tms, a)

      | SortedTerm (tm,                       ty,                       a) ->
        SortedTerm (eliminateTerm context tm, eliminateSort context ty, a)

      | tm -> tm

 op simplifyPatternMatchResult (t : MS.Term) : Option MS.Term =
  let 

    def simpRec (t1, t2) =
      case t1 of
        | IfThenElse (p, x, y, pos) ->
          (case simpSuccess x of
             | Some sx ->
               (case simpRec(y,t2) of
                  | Some ny -> Some(IfThenElse(p,sx,ny,pos))
                  | None -> None)
             | None ->
               if simpleSuccTerm? t2 then
                 case simpRec(x,t2) of
                   | Some sx ->
                     (case simpRec(y,t2) of
                        | Some ny -> Some(IfThenElse(p,sx,ny,pos))
                        | None -> None)
                   | None -> None
               else 
                 None)

        | Fun(Op(Qualified("TranslationBuiltIn","mkBreak"),_),_,_) -> simpSuccess t2

        | Apply(Fun(Op(Qualified("TranslationBuiltIn","mkSuccess"),_),_,_),st1,_) ->
          Some st1			% t2 is unreachable

        | Let(matches,st1,pos) ->
          (case simpRec(st1,t2) of
             | Some nt1 -> Some(Let(matches,nt1,pos))
             | None -> None)

        | Apply (Fun(Op(Qualified("TranslationBuiltIn","failWith"),_),_,_),
                 Record ([("1",st1), ("2",ft2)],_),_) ->
          (case simpRec(ft2,t2) of
             | Some nft2 -> simpRec(st1,simpLet nft2)
             | None -> None)

        | Apply (Fun(Op(Qualified("TranslationBuiltIn","mkFail"),_),_,_),_,_) -> 
          Some t1

        | _ -> None

    def simpSuccess t =
      case t of

        | Apply (Fun(Op(Qualified("TranslationBuiltIn","mkSuccess"),_),_,_), t1, _) -> 
          Some t1

        | Let (matches, t1, pos) ->
          (case simpSuccess t1 of
             | Some nt1 -> Some(Let(matches,nt1,pos))
             | None -> None)

        | Apply (Fun(Op(Qualified("TranslationBuiltIn","failWith"),_),_,_),
                 Record ([("1",t1),("2",t2)],_),_) ->
          simpRec (t1, t2)

        | Apply(Fun(Op(Qualified("TranslationBuiltIn","mkFail"),_),_,_),_,_) -> 
          Some t

        | _ -> None         
  in
  case t of
    | Apply (Fun(Op(Qualified("TranslationBuiltIn","failWith"),_),_,_),
	     Record ([("1",t1),("2",t2)],_),_) ->
      simpRec (t1, simpLet t2)
    | _ -> None
     
 op simpLamBody (t : MS.Term) : MS.Term =
  case t of
    | Lambda ([(pat, c, Apply(Lambda([(VarPat(v,_),_,body)],_),wVar as (Var(w,_)),_))], pos) ->
      Lambda ([(pat, c, substitute(body,[(v,wVar)]))],                                  pos)
    | _ -> t

 op simpLet (tm : MS.Term) : MS.Term =
   case tm of

     | Apply (Fun (Op(Qualified("TranslationBuiltIn","mkSuccess"),a1),t1,a2), st1,         a3) ->
       Apply (Fun (Op(Qualified("TranslationBuiltIn","mkSuccess"),a1),t1,a2), simpLet st1, a3)

     | Let ([(VarPat (id,_),e)], body, _) ->
       (case countVarRefs (body, id) of
          | 0 -> if sideEffectFree e then body else tm
          | _ -> tm)

     | _ -> tm

 op simpleSuccTerm? (tm : MS.Term) : Bool =
  case tm of
    | Apply (Fun (Op (Qualified("TranslationBuiltIn","mkSuccess"),_),_,_), st1, _) -> 
      simpleSuccTerm? st1
    | Var    _       -> true
    | Fun    _       -> true
    | Record ([], _) -> true
    | _              -> false

 %- --------------------------------------------------------------------------------
 %- checks whether Record is a Product or a user-level Record

 op [A] isShortTuple (i : Nat, row : List (Id * A)) : Bool =
  case row of
    | [] -> true
    | (lbl, r) :: row -> 
      (lbl = Nat.show i) && isShortTuple (i + 1, row)

 op [A] recordfields? (fields : List (Id * A)) : Bool =
  ~ (isShortTuple (1, fields))

 (*
  * Dropped arity raising for the first round of pattern matching compilation.
  * let term = mapTerm(arityRaising,fn x -> x,fn x -> x) term in
  * let term = mapTerm(elimPattern,fn x -> x,fn x -> x) term in
  * (%%% writeLine "Pattern eliminated";
  *  term)
  *)

 def translateMatch spc = 
   % sjw: Moved (Ref 0) in-line so it is reexecuted for each call so the counter is reinitialized for each
   % call. (This was presumably what was intended as otherwise there would be no need for mkContext
   % to be a function). This means that compiled functions will have the same generated variables
   % independent of the rest of the file.
   let 
     def mkContext funName =
       {counter    = Ref 0,
	spc        = spc,
	funName    = funName, % used when constructing error messages
	errorIndex = Ref 0,   % used to distinguish error messages
	term       = None} 
   in
     spc << {
             sorts = mapSortInfos (fn info ->
                                   let Qualified (_,id) = primarySortName info in
                                   let (old_decls, old_defs) = sortInfoDeclsAndDefs info in
                                   let new_defs =
				       map (fn dfn ->
                                            let (tvs, srt) = unpackSort dfn in
                                            let new_sort = eliminateSort (mkContext id) srt in
                                            maybePiSort (tvs, new_sort))
                                           old_defs
                                   in
                                     let new_dfn = maybeAndSort (old_decls ++ new_defs, sortAnn info.dfn) in
                                     info << {dfn = new_dfn}) 
                                  spc.sorts,
             ops = mapOpInfos (fn info ->
                               let Qualified (_,id) = primaryOpName info in
                               let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                               let new_defs = 
                                   map (fn dfn ->
					let (tvs, srt, term) = unpackFirstTerm dfn in
					let new_srt = eliminateSort (mkContext id) srt in
					let new_tm  = eliminateTerm (mkContext id) term in
					let new_tm = simpLamBody new_tm in
					maybePiTerm (tvs, SortedTerm (new_tm, new_srt, termAnn term)))
				       old_defs
			       in
                                 let new_dfn = maybeAndTerm (old_decls ++ new_defs, termAnn info.dfn) in
                                 info << {dfn = new_dfn})
			      spc.ops,
             elements = map (fn el ->
                               case el of
                                 | Property (pt, pname as Qualified(_, id), tyvars, term, a) -> 
                                   Property (pt, pname, tyvars, eliminateTerm (mkContext id) term, a)
                                 | _ -> el) 
                            spc.elements
             }

endspec

(****
 *
 * Arity raising must take place before or during pattern matching compilation
 * because that flattens the record patterns.
 *
 * def arityRaising(term:MS.Term):MS.Term = 
 *     case term
 *       of (Lambda 
 *	   [((VarPat(v1,_),pos0),(Fun(Bool true,_),_),
 *	     (Let([(pat as (RecordPat fields,_),(Var v2,_))],body),_))],_) -> 
 *	  if (v1 = v2) &&  
 *	     forall? (fn(_,(VarPat v3,_))-> ~(v1 = v3) | _ -> false) fields
 *	  then 
 *	  let letTerm:MS.Term = mkRecord(map (fn(id,(VarPat v,p))-> (id,(Var v,p))) fields) in
 *	  (Lambda [(pat,trueTerm,Match.mkLet([(mkVarPat v1,letTerm)],body))],pos0)
 *	  else term
 *	| _ -> term
 *
 *
 * (*
 *  * Computation of a decision DAG together with static checks
 *  * for exhaustive and redundant branches. 
 *  * Finally, proof-obligations for exhaustive branch coverage are generated. 
 *  *)
 *
 * (* 
 *  * Internal representation of constructors and patterns supplied
 *  * with adequate arity and span information.
 *  *)
 *
 * type con = 
 *  | CON :: {arity : Nat, span : Nat, name : String}
 *  | RELAX :: Term
 *  | QUOTIENT :: Term
 *  | CONST :: {const : const, span : Nat}
 * and const = 
 *  | NAT  :: Nat
 *  | BOOL :: Boolean
 *  | CHAR :: Char
 *  | STRING :: String
 * 
 * def printConst(c:const) = 
 *     case c
 *       of NAT n -> show n
 *        | BOOL b -> Bool.show b
 *        | CHAR ch -> Char.show ch
 *        | STRING s -> s
 * 
 * def printCon(c:con) = 
 *     case c 
 *       of CON{name,arity,span} -> name
 *        | RELAX term -> "relax("^printTerm term^")"
 *        | QUOTIENT term -> "quotient("^printTerm term^")"
 *        | CONST{const,span} -> printConst const
 * 
 * def span (c:con) = 
 *     case c
 *       of CON{span,arity,name} -> span
 *        | RELAX s -> 0 (* infinity *)
 *        | QUOTIENT _ -> 0
 *        | CONST{const,span} -> span
 * 
 * def arity (c:con) = 
 *     case c
 *       of CON{arity,span,name} -> arity
 *        | RELAX s -> 1
 *        | QUOTIENT _ -> 1
 *        | CONST _ -> 0
 * 
 * (*
 *  *  Internal simplified pattern representation 
 *  *)
 * 
 * type pattern = 
 *   | Var :: String * Sort
 *   | Con :: con * List[pattern] * Sort
 *   | Alias :: pattern * pattern
 * 
 * (*
 *  * convertPattern : SpecEnvironment * Pattern -> pattern
 *  * 
 *  * Convert MetaSlang Ast pattern into internal simplified pattern
 *  * representation.
 *  * 
 *  *)
 * 
 * def coProductLength(spc,srt) = 
 *     case unfoldBase(spc,srt)
 *       of (CoProduct fields,_) -> length fields
 *        | _ -> System.fail "Not a co-product sort"
 * 
 * def relaxTerm(srt:Sort) = 
 *     case srt
 *       of (Arrow((Subsort(_,trm),_),_),_) -> trm
 *        | _ -> trueTerm (* Should not happen *)
 *     
 * 
 * def convertPattern(spc,pat as (p,_):Pattern):pattern = 
 *     case p
 *       of VarPat var -> Var var
 *        | AliasPat(p1,p2) -> Alias(convertPattern(spc,p1),
 * 				  convertPattern(spc,p2))
 *        | QuotientPat(p,t) -> 
 * 	 Con(QUOTIENT(t),[convertPattern(spc,p)],patternSort(pat))
 *        | EmbedPat(con,Some arg,srt) ->
 * 	 Con(CON{arity = 1,name = con,span = coProductLength(spc,srt)},
 * 	    [convertPattern(spc,arg)],srt) 
 *        | EmbedPat(con,None,srt) ->
 * 	 Con(CON{arity = 0,name = con,span = coProductLength(spc,srt)},
 * 	     [],srt) 
 *        | RecordPat(fields) -> 
 * 	 Con(CON{arity = length fields,name = "",span = 1},
 * 		map (fn(id,p) -> convertPattern(spc,p)) fields,
 * 	        patternSort(pat))
 * 	 (* 
 * 	  * The empty constructor name is reserved for record
 * 	  * constructors.
 *           *)
 *        | WildPat srt -> Var("",srt)
 *        | StringPat s -> Con(CONST{const = STRING s,span = 0},[],stringSort)
 *        | BoolPat b   -> Con(CONST{const = BOOL b,span = 2},[],boolSort)
 *        | NatPat n    -> Con(CONST{const = NAT n,span = 0},[],intSort)
 *        | CharPat ch  -> Con(CONST{const = CHAR ch,span = 256},[],charSort)
 * 
 * def patternSort(pat:pattern):Sort = 
 *     case pat
 *       of Var(_,srt) -> srt
 *        | Con(_,_,srt) -> srt
 *        | Alias(p1,p2) -> patternSort p1
 * 
 * (* Term descriptions *)
 * 
 * type termd =
 *   | Pos :: con * List[termd]       (* All arguments in proper order *)
 *   | Neg :: List[con]                (* No duplicates                 *)
 * 
 *     
 * op printTermD : termd -> String
 * op printTermDs : List[termd] -> String
 * 
 * def printTermD(termd:termd) =
 *     case termd
 *       of Pos(con,termDs) ->    printCon(con)^"("^printTermDs(termDs)^")"
 *        | Neg conses ->    "Neg("^printCons conses^")"
 * and printTermDs tds = 
 *     case tds
 *       of [] -> ""
 *        | [td] -> printTermD td
 *        | (td::tds) -> printTermD td^","^printTermDs tds
 * and printCons cs = 
 *     case cs
 *       of [] -> ""
 *        | [c] -> printCon c
 *        | (c::cs) -> printCon c ^","^printCons cs
 * 
 * def Bot() = Neg [] : termd          (* The absence of information    *)
 * 
 * def bots n = tabulate(n, fn _ -> Bot())
 * 
 * (* Contexts, or inside-out partial term descriptions:
 *  * Example: The context [(c2, [a2, a1]), (c1, [b2, b1])] represents
 *  * a term description with a hole, of the form
 *  *           c1(b1, b2, c2(a1, a2, Bot, ..., Bot), Bot, ..., Bot) 
 *  * where the number of Bots is determined by the arity of c1 and c2.
 *  *) 
 * 
 * 
 * type context = List[con * Option[termd] * List[termd]]
 * 
 * def augment(context:context,dsc) = 
 *     case context
 *       of [] -> []
 *        | Cons((con,optDsc,args),rest) -> 
 * 	 cons((con,optDsc,cons(dsc,args)),rest)
 * 
 * (* Static matching *)
 * 
 * 
 * 
 * type matchresult = | Yes | No | Maybe
 * 
 * def staticmatch (pcon:con) (td:termd) : matchresult = 
 *     case (pcon,td)
 *       of (RELAX _,_)  -> Maybe
 *        | (QUOTIENT _,_) -> Maybe
 *        | (_,Pos(scon,_)) -> 
 *          if pcon = scon then Yes else No
 *        | (_,Neg nonset)  ->
 *         if exists (fn x -> x =  pcon) nonset then 
 *            No
 *         else if span pcon = 1 + length nonset then 
 *            Yes
 *         else 
 *            Maybe
 * 
 * (* Managing partial terms and contexts *)
 * 
 * def addneg (dsc:termd) (con:con) = 
 *     case dsc 
 *       of Neg nonset -> Neg(cons(con,nonset)):termd
 *        | _ -> dsc
 * 
 * op revappend : [T] List[T] * List[T] -> List[T]
 * def revappend(xs,res) = 
 *     case xs
 *       of [] -> res
 *        | x::xs -> revappend(xs,cons(x,res))
 * 
 * def builddsc(ctx,dsc0:termd,work) = 
 *     let
 * 	def loop(context:context,dsc:termd,work) = 
 * 	    case (context,work)
 * 	      of ([],[]) -> dsc
 * 	       | ((con,Some dsc,_)::rest,work) -> dsc
 * 	       | ((con,None,args)::rest,(_,_,sargs)::work) -> 
 * 	         builddsc(rest,(Pos(con, revappend(args,cons(dsc,sargs)))),work)
 * 	       |  _ -> System.fail "Match.builddsc"
 *     in
 * 	loop(ctx,dsc0,work)
 *     
 * 
 * (* Runtime data access and matching actions *)
 * 
 * type access = 
 *  | Select :: String
 *  | Project :: Nat
 *  | Restrict :: Term
 *  | Choose :: Term 
 * def selectproject(sel,i):access = 
 *     case sel
 *       of "" -> Project(i)  (* 
 * 			      The empty string is reserved for record
 * 			      constructors 
 * 			    *)
 *        | _ -> Select(sel)
 * def restrict(pred):access = Restrict pred
 * def chooseTerm(pred):access = Choose pred
 * 
 * def printAccess (access:access) = 
 *     case access
 *       of Project(i) -> 
 *          "project_"^show i
 *        | Select(sel) -> 
 *          "select_"^sel
 *        | Restrict s -> "restrict_"^printTerm s
 *        | Choose s -> "choose_"^printTerm s
 * 
 * type var = String * Sort
 * 
 * type test = 
 *  | Embedded :: String * var
 *  | Relaxed  :: Term * var
 *  | Condition :: Term
 * 
 * def testToTerm(test:test) = 
 *     case test
 *       of Embedded(embedOp,(name,srt)) -> 
 * 	 mkApply(mkEmbedded(embedOp,srt),mkVar (name,srt))
 *        | Relaxed(term,(name,srt)) -> 
 * 	 mkApply(term,mkVar(name,srt))
 *        | Condition term -> term
 * 
 * def printTest(test:test) = 
 *     (case test
 *        of Embedded(s,(var,srt)) ->  s^"?("^var^")"
 *         | Relaxed(s,(var,srt)) -> printTerm s^"?("^var^")"
 *         | Condition term -> printTerm term)
 * 
 * type decl = var * access * var
 * 
 * 
 * type dec =
 *   | Failure
 *   | Success :: Term			(* right-hand side *)
 *   | IfEq :: test * decision * decision
 *   | Let  :: List[decl] * decision 
 * and decision = Ref[{tree : dec, refs : Ref[Nat]}]
 * 
 * def shared (Ref {refs,tree}   : decision) = ! refs > 1
 * def used   (Ref {refs,tree}   : decision) = ! refs > 0
 * def incrnode (Ref {refs,tree} : decision) = refs := 1 + ! refs
 * op mkDecision : dec -> decision
 * def mkDecision t = Ref {tree = t, refs = Ref 0}:decision
 * 
 * 
 * (* Hash-consing, to get a decision dag rather than a decision tree *)
 * 
 * def insertNode(table,node,ts) =  
 *     (case HashTable.lookup(node,table)
 *        of Some n -> n
 *         | None ->
 * 	  let rnode = mkDecision node
 * 	  in 
 * 	    (
 * 	       app incrnode ts;
 * 	       HashTable.insert(node,rnode,table);
 * 	       rnode
 * 	    )
 *      )
 * 
 * op  unique : HashTable.HashTable[dec,decision] * dec -> decision
 * def unique (table,node:dec) = 
 *     (case node
 *        of IfEq(_, t1, t2) -> 
 *           if t1 = t2 then t1 else insertNode(table,node,[t1,t2])
 *         | Let([],t) -> t
 *         | Let(_,t) -> insertNode(table,node,[t])
 *         | _ -> System.fail "Match.unique")
 * 
 * def compile(table,failure,allmrules) = 
 *     let
 * 	def fail(dsc,rules) = 
 *             case rules
 * 	      of [] -> failure
 * 	       | (pat1,cond1,rhs1)::rulerest -> 
 * 	         match(pat1,"x",dsc,[],[],cond1,rhs1,rulerest)
 * 	and succeed(ctx,work,cond:Term,rhs,rules,fail) =
 * 	    case work
 * 	      of [] -> 
 * 	         (case cond
 * 	       	    of (Fun(Bool true,_),_) -> rhs
 * 		     | _ -> 
 * 		  unique
 * 		    (table,IfEq
 * 		      (Condition cond,
 * 		       rhs,
 * 		       mkDecision Failure
 * 		      )
 * 		    ))
 * 	       | work1::workrest ->
 * 	    (case work1: List[pattern] *List[String]  * List[termd]
 * 	       of 
 * 		([], [], []) -> 
 * 		succeed(ctx,workrest,cond,rhs,rules,fail)
 * 	      | ((Alias(pat1,pat2):pattern)::patrest, 
 * 		  obj1::objrest, dsc1::dscrest) ->
 * 		succeed(ctx,
 * 		cons((cons((pat1,cons(pat2,patrest))),
 * 			   cons(obj1,cons(obj1,objrest)),
 * 			   cons(dsc1,cons(dsc1,dscrest))),workrest),
 * 		cond,rhs,rules,fail)
 * 	      | (pat1::patrest, obj1::objrest, dsc1::dscrest) ->
 * 		    match(pat1,obj1,dsc1,ctx, 
 * 		    (cons((patrest, objrest, dscrest),workrest)),cond,rhs,rules)
 * 	      | ([],[],(Pos(con,_):termd)::_) -> 
 * 		    System.fail ("Too much dsc "^printCon con)
 * 	      | ([],[],(Neg(con::_):termd)::_) -> 
 * 		    System.fail ("Too much negative dsc "^printCon con)
 * 	      | ([],_,[]) -> System.fail "Too much obj"
 * 	      | (_,[],[]) -> System.fail "Too much pat"
 * 
 * 	      | _ -> System.fail "Match.succeed")
 * 	and match(pat:pattern,obj,dsc,ctx,work,cond,rhs,rules) = 
 * 	    case pat
 * 	      of Var s -> 
 * 		 let def failP() = fail(builddsc(ctx,dsc,work),rules) in
 * 		 let ctx = augment(ctx,dsc) in
 * 		     succeed(ctx,work,cond,rhs,rules,failP)
 * 		 
 * 	       | Con(pcon as CON {name,arity,span},pargs,srt) -> 
 * 		 let def getdargs(dsc:termd) = 
 * 		         case dsc
 * 			   of Neg _ -> tabulate(arity,fn _ -> Bot())
 * 		            | Pos(con,dargs) -> dargs
 * 		 in
 * 		 let def decls() = 
 * 			 tabulate(arity,fn i -> 
 * 			      let sp = selectproject(name,i+1) in
 * 			      let pat_i = nth(pargs,i) in
 * 			      let srt_i = patternSort(pat_i) in
 * 			      let s  = if name = "" 
 * 					then "project"^show i
 * 				       else "select_"^name
 * 			      in
 * 				  ((s^obj,srt_i),sp,(obj,srt))
 * 			      )
 * 		 in
 * 	         let def failP newdsc = 
 * 			 fail(builddsc(ctx,newdsc,work),rules)
 * 		 in
 * 		 let def staticfail() = failP dsc in
 * 		 let def dynamicfail() = failP (addneg dsc pcon) in
 * 		 let def staticsuccess(oargs) = 
 * 			 succeed(cons((pcon,None,[]),ctx),
 * 				 cons((pargs,oargs,getdargs dsc),work),
 * 				 cond,rhs,rules,staticfail)
 * 		 in
 * 		 let def succeedP() = 
 * 			 let decls = decls() in
 * 			 let oargs = map (fn((d,_),_,_)-> d) decls in 
 * 			 let dec = staticsuccess(oargs) in
 * 			     unique(table,Let(decls,dec))
 * 		 in
 * 		 let test:test = Embedded(name,(obj,srt)) in
 * 		 (case staticmatch pcon dsc
 * 		    of Yes   -> staticsuccess
 * 		           (tabulate(arity,
 * 				fn i-> printAccess
 * 					(selectproject(name,i+1))))
 * 		     | No    -> staticfail() 
 * 		     | Maybe -> 
 * 		       unique(table,IfEq(test, 
 * 				       succeedP (),
 * 				       dynamicfail()))
 * 		 )
 * 
 * 		   
 * 	       | Con(pcon as RELAX term,pargs,srt) ->
 * 		 let acc  = restrict(term) in 
 * 		 let oarg = "relax_"^obj in 
 * 		 let srt0 = termSort term in
 * 		 let decls = [((oarg,srt0),acc,(obj,srt))] in 
 * 		 let test:test = Relaxed(term,(obj,srt)) in 
 * 		 let def dynamicfail() = 
 * 			 fail(builddsc(ctx,dsc,work),rules)  in 
 * 		 let succeed = 
 * 			 unique
 * 			   (table,Let
 * 			    (decls,
 * 			     succeed(cons((pcon,Some dsc,[]),ctx),
 * 				     cons((pargs,[oarg],
 * 				      [Bot()]),work),
 * 				     cond,rhs,rules,dynamicfail)))
 * 		 in
 * 		     unique 
 * 		       (table,IfEq(test,  succeed,  dynamicfail()) )
 * 	    | _ -> System.fail "Match case not covered"
 * 		 
 *     in
 * 	fail(Bot(),allmrules)
 *    
 * 
 * def mkTest(p,l:Term,r:Term):Term = 
 *     case (l,r)
 *       of ((Fun(Bool true,_),_), (Fun(Bool true,_),_)) -> r
 *        | ((Fun(Bool false,_),_),(Fun(Bool false,_),_)) -> r
 *        | ((Fun(Bool true,_),_), (Fun(Bool false,_),_)) -> testToTerm p
 *        | _ -> mkIfThenElse(testToTerm p,l,r)
 * 
 * def mkDecl(v1,access:access,v2) = 
 *     case access
 *       of Select embedOp -> (mkVarPat v1,mkSelectTerm(embedOp,mkVar v2))
 *        | Project n -> (mkVarPat v1,mkProjectTerm(context.spc,show n,mkVar v2))
 *        | Restrict query -> 
 * 	 (mkVarPat v1,mkRestrict{term = mkVar v2,pred = query})
 *        | Choose equiv -> 
 * 	 (mkVarPat v1,mkChoose(mkVar v2,equiv))
 * 
 * (* Generate proof obligation for exhaustive match branching *)
 * def checkExhaustive(dag as Ref {tree,refs}:decision):Term = 
 *     (case tree
 *       of Failure -> mkFalse()
 *        | Success _ -> trueTerm
 *        | IfEq(test,l,r) -> 
 * 	 let l = checkExhaustive(l) in 
 * 	 let r = checkExhaustive(r) in
 * 	 mkTest(test,l,r)
 * 	 
 *        | Let(decls,d) -> 
 * 	 let d = checkExhaustive(d) in
 * 	     (case d
 * 	       of (Fun(Bool _,_),_) -> d
 * 		| _ -> mkLet(map mkDecl decls,d)
 * 	     ))
 * 
 * type MatchResult = | Redundant | NonExhaustive :: Term | Ok  
 * 
 *     
 * def checkMatch (spc,rules: Match): MatchResult = 
 *     let	failure = mkDecision Failure    in
 *     let	table = HashTable.initialize(fn (x,y) -> x = y,20)    in
 *     let	rules = map 
 * 		(fn (pat,cond,rhs)->
 * 		    (convertPattern(spc,pat),
 * 		     cond,
 * 		     mkDecision (Success rhs))
 * 		) rules
 *     in
 *     let	dag = compile(table,failure,rules)  in
 *     (case find (fn (_,_, rhs) -> ~ (used rhs)) rules
 *        of Some (_,_,Ref{tree = Success s,refs}:decision) -> Redundant 
 *         | _ -> 
 *          if used failure
 * 	    then NonExhaustive(checkExhaustive(dag))
 * 	 else Ok)   
 * 
 ****)
