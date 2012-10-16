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
		Subtype:    relax
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

  def match_type srt = srt % mkBase (Qualified("TranslationBuiltIn","Match"), [srt])

  def mkBreak    srt = mkOp (Qualified("TranslationBuiltIn","mkBreak"), match_type srt)

  def isBreak (term : MSTerm) = 
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

  op failWith (context : Context) (t1 : MSTerm) (t2 : MSTerm) : MSTerm =
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
  
  type Rule  = List MSPattern * MSTerm * MSTerm
  type Rules = List Rule
  
  type Context = {counter    : Ref Nat,
		  spc        : Spec,
		  funName    : String,
		  errorIndex : Ref Nat,
		  term       : Option MSTerm}

  def storeTerm (tm, ctx) =
    ctx << {term = Some tm}

%  op  mkProjectTerm : Spec * Id * MSTerm -> MSTerm
%  def mkProjectTerm = SpecEnvironment.mkProjectTerm
%  op  mkRestrict :    Spec * {pred:MSTerm,term: MSTerm} -> MSTerm
%  def mkRestrict = SpecEnvironment.mkRestrict
  
  op match : Context * List MSTerm * Rules * MSTerm * MSTerm -> MSTerm

  (* The following invariant holds of the patterns:
     - for a call to match(vars,rules,default):
	each list of patterns in the rules has the same length and typeing 
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

  def substPat(e,pat:MSPattern,t) = 
      if isTrue(e) then e else 
      case pat
	of WildPat _ -> e
         | VarPat _ -> mkLet([(pat,t)],e)
	 | _ -> e (* Should not happen *)
      

(* 
   We generate tester functions for the various constructor formats.
 *)

  def embedded (constructorName : String) term = 
    mkApply (mkEmbedded (constructorName, termType term),
             term)


  def relaxed predicate term = 
    mkApply (predicate, term)
 
  def equalToConstant (srt, constantTerm : MSTerm) term =
    mkEquality (srt, constantTerm, term)

  def mkLet (lets : List (MSPattern * MSTerm), term) = 
    case lets of
      | [] -> term : MSTerm
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
                  | Alias      MSPattern * MSPattern
                  | Relax      MSPattern * MSTerm 
                  | Quotient   MSPattern * TypeName
                  | Restricted MSPattern * MSTerm 

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

  def sameConstructor spc (pat1 : MSPattern, pat2 : MSPattern) = 
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

  type DestructedRule = MSTerm * List MSTerm * List (MSPattern * MSTerm) * MSPattern * Rules

  op partitionConstructors : Context * MSTerm * Rules -> List DestructedRule

  op freshVar (context : Context, srt : MSType) : Var =
   let num = ! context.counter + 1 in
   (context.counter := num;
    ("pV" ^ (Nat.show num), srt))

  op freshVars (num : Nat, context : Context, pat : MSPattern) : List (String * Var) =
   case num of
     | 0 -> []
     | 1 -> [("", freshVar (context, patternType pat))]
     | _ ->
       case pat of
         | RecordPat(fields,_) -> 
           map (fn (l, p) -> (l, freshVar (context, patternType p)))
               fields
         | _ -> System.fail "Record pattern expected"

  (* 
   *  Generates the query term used to identify variable being an instance
   *  of the pattern 
   *)

  op queryPat (pattern : MSPattern) : MSTerm -> MSTerm = 
   case pattern of
     | EmbedPat  (e,_,_, _) -> embedded e
     | NatPat    (n,     _) -> equalToConstant (natType,    mkNat    n)
     | CharPat   (c,     _) -> equalToConstant (charType,   mkChar   c)
     | BoolPat   (b,     _) -> equalToConstant (boolType,   mkBool   b)
     | StringPat (s,     _) -> equalToConstant (stringType, mkString s)
     | RecordPat _          -> (fn _ -> trueTerm)
     | _                    -> (fn _ -> trueTerm)
              

  op coproductFields (spc: Spec, srt: MSType) : List (Id * Option MSType) = 
   let srt = unfoldBase (spc, srt) in
   case srt of
     | CoProduct (fields, _) -> fields
     | Subtype   (tau, _, _) -> coproductFields (spc, tau)
     | Base (Qualified ("List", "List"), [x], _) -> 
       [("Nil",  None), 
        ("Cons", Some (Product ([("1", x), ("2", srt)], 
                                typeAnn srt)))]
     | _ -> System.fail ("CoProduct type expected, but got " ^ printType srt)

  def partitionConstructors (context, t, rules) =
    let
      def patDecompose (pattern : MSPattern) : List (MSPattern * MSTerm) = 
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
            let newVars       = map (fn (p, _) -> freshVar (context, patternType p)) 
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
	       
  op abstract (vs: List (String * Var), tm : MSTerm, srt) : MSTerm = 
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
      | Relax      (pat, pred)     -> matchSubtype    (context, pred,     vars, rules, default, break)
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

  def matchSubtype (context, pred, tm::terms, rules, default, break) =
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
        let rules = map (fn ((QuotientPat (p, pred, _)) :: pats, cond, e) ->
                           (p::pats, cond, e))
                        rules 
        in
        failWith context
                 (match (context, t1::terms, rules, break, break))
                 default 	
      | _ -> fail ("Internal confusion in matchQuotient: expected " ^ printType q ^ " to name a quotient type")


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

 def splitPattern (arity, pat : MSPattern) :List MSPattern =
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

 def flattenLetDecl ((pat : MSPattern, term : MSTerm), (context, decls)) =
   case (pat, term) of
     | (WildPat (srt,_), Var _)        -> (context, decls)
     | (WildPat (srt,_), Record([],_)) -> (context, decls)
     | (WildPat (srt,_), term)         -> (context, Cons ((mkVarPat (freshVar (context, patternType pat)), term), 
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

 op eliminatePattern: Context -> MSPattern -> MSPattern 
 op eliminateTerm   : Context -> MSTerm    -> MSTerm
 op eliminateType   : Context -> MSType    -> MSType

 def eliminatePattern context pat = 
   case pat of

     | AliasPat (p1,                          p2,                          a) -> 
       AliasPat (eliminatePattern context p1, eliminatePattern context p2, a)

     | VarPat ((n, s),                       a) -> 
       VarPat ((n, eliminateType context s), a)

     | EmbedPat (i, Some p,                            s,                       a) ->
       EmbedPat (i, Some (eliminatePattern context p), eliminateType context s, a)

     | EmbedPat (i, None, s,                       a) ->
       EmbedPat (i, None, eliminateType context s, a)

     | RecordPat (fields,                                                   a) -> 
       RecordPat (map (fn (i, p)-> (i, eliminatePattern context p)) fields, a)

     | WildPat   (s, a) -> VarPat (freshVar (context, eliminateType context s), a)
     | StringPat (s, a) -> StringPat (s, a)
     | BoolPat   (b, a) -> BoolPat   (b, a)
     | CharPat   (c, a) -> CharPat   (c, a)
     | NatPat    (n, a) -> NatPat    (n, a)

     | QuotientPat  (p,                          qid, a) ->
       QuotientPat  (eliminatePattern context p, qid, a)

     | RestrictedPat (p,                          tm,                       a) ->
       RestrictedPat (eliminatePattern context p, eliminateTerm context tm, a)

     | TypedPat (p,                          ty,                       a) ->
       TypedPat (eliminatePattern context p, eliminateType context ty, a)

 def eliminateType context srt =
   case srt of

     | Arrow (s1,                       s2,                       a) -> 
       Arrow (eliminateType context s1, eliminateType context s2, a)

     | Product (fields,                                                 a) -> 
       Product (map (fn (i, s) -> (i, eliminateType context s)) fields, a)

     | CoProduct (fields, a) -> 
       CoProduct (map (fn (i, x) -> 
                         (i,
                          case x of
                            | Some s -> Some (eliminateType context s)
                            | _ -> None))
                      fields,
                  a)

     | Quotient (s,                       tm,                       a) -> 
       Quotient (eliminateType context s, eliminateTerm context tm, a)

     | Subtype (s,                       tm, a) -> 
       % Subtype predicates aren't used in code generation (??), so omit eliminateTerm context tm,  ????
       Subtype (eliminateType context s, tm, a) 

     | Base (qid, types,                             a) -> 
       Base (qid, map (eliminateType context) types, a)

     | Boolean _ -> srt
     | TyVar   _ -> srt
     | Any     _ -> srt
     | And (srts,     a) -> And (map (eliminateType context) srts, a)
     | Pi  (tvs, srt, a) -> Pi  (tvs, eliminateType context srt,   a)

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
           let term : MSTerm = 
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

 op alwaysCheckRestrictedPatInLambda?: Bool = false

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
	 let bdyType           = inferType (context.spc, bdy)                    in
	 let vs                = freshVars (arity, context, pat)                 in
	 %%%	 let  _ = writeLine "Elimination from lambda: rules "            in
	 let (rules, default)  = makeDefault (context, bdyType, rules, vs, term) in
	 let rules = map (fn (p, c, t) -> 
                            (splitPattern(arity,p), c, mkSuccess (bdyType, t))) 
                         rules 
         in
	 let vars = map (fn (_, v) -> mkVar v) vs                                            in
	 let trm  = match (storeTerm (term, context), vars, rules, default, mkBreak bdyType) in
	 let trm  = abstract (vs, trm, bdyType)                                              in
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
         let vs = map (fn pat -> freshVar (context, patternType pat)) pats in
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
	Bind (b, map (fn(n,s)-> (n,eliminateType context s)) vars, eliminateTerm context tm, a)

      | The ((id, srt),                       tm,                       a) -> 
	The ((id, eliminateType context srt), eliminateTerm context tm, a)

      | LetRec (decls, body, a) -> 
	LetRec (map (fn ((n, s), t)->
                       ((n, eliminateType context s),
                        eliminateTerm context t)) 
                    decls,
                eliminateTerm context body,
                a)

      | Var ((n, s),                       a) -> 
        Var ((n, eliminateType context s), a)

      | Fun (f, s,                       a) -> 
        Fun (f, eliminateType context s, a)

      | IfThenElse (s1, s2, s3, a) -> 
        IfThenElse (eliminateTerm context s1,
                    eliminateTerm context s2,
                    eliminateTerm context s3,
                    a)

      | Seq (terms,                             a) -> 
        Seq (map (eliminateTerm context) terms, a)

      | And (tm                       :: r_tms, a) -> 
        And (eliminateTerm context tm :: r_tms, a)

      | TypedTerm (tm,                       ty,                       a) ->
        TypedTerm (eliminateTerm context tm, eliminateType context ty, a)

      | tm -> tm

 op simplifyPatternMatchResult (t : MSTerm) : Option MSTerm =
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
     
 op simpLamBody (t : MSTerm) : MSTerm =
  case t of
    | Lambda ([(pat, c, Apply(Lambda([(VarPat(v,_),_,body)],_),wVar as (Var(w,_)),_))], pos) ->
      Lambda ([(pat, c, substitute(body,[(v,wVar)]))],                                  pos)
    | _ -> t

 op simpLet (tm : MSTerm) : MSTerm =
   case tm of

     | Apply (Fun (Op(Qualified("TranslationBuiltIn","mkSuccess"),a1),t1,a2), st1,         a3) ->
       Apply (Fun (Op(Qualified("TranslationBuiltIn","mkSuccess"),a1),t1,a2), simpLet st1, a3)

     | Let ([(VarPat (id,_),e)], body, _) ->
       (case countVarRefs (body, id) of
          | 0 -> if sideEffectFree e then body else tm
          | _ -> tm)

     | _ -> tm

 op simpleSuccTerm? (tm : MSTerm) : Bool =
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
             types = mapTypeInfos (fn info ->
                                   let Qualified (_,id) = primaryTypeName info in
                                   let (old_decls, old_defs) = typeInfoDeclsAndDefs info in
                                   let new_defs =
				       map (fn dfn ->
                                            let (tvs, srt) = unpackType dfn in
                                            let new_type = eliminateType (mkContext id) srt in
                                            maybePiType (tvs, new_type))
                                           old_defs
                                   in
                                     let new_dfn = maybeAndType (old_decls ++ new_defs, typeAnn info.dfn) in
                                     info << {dfn = new_dfn}) 
                                  spc.types,
             ops = mapOpInfos (fn info ->
                               let Qualified (_,id) = primaryOpName info in
                               let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                               let new_defs = 
                                   map (fn dfn ->
					let (tvs, srt, term) = unpackFirstTerm dfn in
					let new_srt = eliminateType (mkContext id) srt in
					let new_tm  = eliminateTerm (mkContext id) term in
					let new_tm = simpLamBody new_tm in
					maybePiTerm (tvs, TypedTerm (new_tm, new_srt, termAnn term)))
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

end-spec
