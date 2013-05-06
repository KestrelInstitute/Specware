% Synchronized with version 1.3 of SW4/Languages/MetaSlang/Transformations/Match.sl

(*
 * Pattern matching compiler for Meta-Slang.
 *
 * Matches of the form
 * 
 *      pattern_1 where condition_1 -> body_1
 *    | pattern_2 where condition_2 -> body_2
 *    | ..
 *    | pattern_n where condition_n -> body_n
 *
 * are translated to expressions without patterns, using If-Then-Else expressions instead.
 *
 * The pattern matching compiler should:
 *   
 * 1. Generate the If-Then-Else expressions as described above with minimal branching.
 *     References
 *       Phil's chapter in Peyton Jones' book
 *       The pattern matching compilers in HOL
 *       The matching compiler in Moscow ML (does use sharing, but branches).
 *
 * 2. Handle patterns from:
 *     Coproducts: embed
 *     Products:   tuple
 *     Subtype:    relax
 *     Quotient:   quotient
 *     Natural, String, character constants.
 *     Variables.
 *
 *   There is a question what to do with patterns from non-free constructors.
 *   Free constructors in Slang may be translated into recursive co-products in Meta-Slang.
 *
 * 3. Generate error messages on non-exhaustive and redundant matches when these can be detected statically.
 *
 * 4. Generate proof-obligations for exhaustive pattern matching when these cannot be detected statically.
 *
 *
 * The pattern matching compiler generates expressions of the form:
 *
 *   match-term ::= TranslationBuiltIn.block block-term
 *  
 *   BLOCK-TERM ::= if TERM then BLOCK-TERM else BREAK
 *                | if TERM then BLOCK-TERM else SUCCESS
 *                | if TERM then BLOCK-TERM else FAIL
 *                | let x = TERM in BLOCK-TERM
 *                | FAIL
 *                | SUCCESS
 *                | BREAK
 *                | TranslationBuiltIn.failWith (BLOCK-TERM, BLOCK-TERM)
 *
 *   BREAK      ::= TranslationBuiltIn.mkBreak
 *   SUCCESS    ::= TranslationBuiltIn.mkSuccess TERM
 *)

PatternMatch qualifying spec
 import ArityNormalize
 import Simplify
   
 type Rules = List Rule                         % NOTE: not the same as MSRules or Match
 type Rule  = List MSPattern * MSTerm * MSTerm  % Note: not the same as MSRule, has list of patterns

 op match_type (typ : MSType) : MSType = 
  typ 

 op mkBreak (t : MSType) : MSTerm = 
  mkOp (Qualified ("TranslationBuiltIn", "mkBreak"), match_type t)

 op isBreak (trm : MSTerm) : Bool = 
  case trm of
    | Fun (Op (Qualified ("TranslationBuiltIn", "mkBreak"), _), _, _) -> true
    | _ -> false

 op mkSuccess (typ0 : MSType, trm : MSTerm) : MSTerm = 
  let typ = mkArrow (typ0, match_type typ0) in 
  mkApply (mkOp (Qualified ("TranslationBuiltIn", "mkSuccess"), typ), 
           trm)

 op isSuccess (trm : MSTerm) : Bool = 
  case trm of
    | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkSuccess"), _), _, _), _, _) -> true
    | _ -> false

 (*
  *   The function failWith implements exception handling.
  *   It unfolds to the primitive:
  *
  *   failWith(t1,t2) = 
  *     case evaluate t1 of
  *       | Break           -> evaluate t2
  *       | Succcess result -> Success result
  *       | Fail            -> evaluate t2
  *
  *   when compiled to LISP, C, JAVA failWith unfolds to the continuations used in block statements.
  *   Break results in a break;
  *   IfThenElse(a,b,Break) translates to if(a) {b};
  *   Success(result) translates to return(result);
  *)

 op failWith (context : Context) (t1 : MSTerm) (t2 : MSTerm) : MSTerm =
  if isBreak t2 then 
    t1 
  else if isSuccess t1 then 
    let _ = warnUnreachable context in
    t1
  else
    let typ  = inferType (context.spc, t1) in
    let typ  = mkArrow (mkProduct [typ,typ], typ) in
    let trm  = mkApply (mkOp (Qualified ("TranslationBuiltIn", "failWith"), typ), 
                        mkRecord [("1",t1), ("2",t2)])
    in
    trm

 op warnUnreachable (context : Context) : () =
  writeLine ("Warning: Redundant case in " ^ context.funName ^ "\n" ^ 
               (case context.term of
                  | Some t -> printTerm t
                  | _ -> ""))
  
 type Context = {counter    : Ref Nat,
                 spc        : Spec,
                 funName    : String,
                 errorIndex : Ref Nat,
                 term       : Option MSTerm}

 op storeTerm (trm : MSTerm, ctx : Context) : Context =
  ctx << {term = Some trm}

 % op  mkProjectTerm (spc : Spec, id   : Id,     trm : MSTerm) : MSTerm = SpecEnvironment.mkProjectTerm
 % op  mkRestrict    (spc : Spec, pred : MSTerm, trm : MSTerm} : MSTerm = SpecEnvironment.mkRestrict
  
 (* 
  * The following invariant holds of the patterns:
  *  - for a call to match(vars,rules,default):
  *    each list of patterns in the rules has the same length and typeing 
  *    as the list of vars.
  *
  *  Pattern matching compilation proceeds according to the following transformation rules on the
  *  arguments of match (Wadler's chapter in Peyton Jones contains all relevant information too).
  *
  *  The empty rule:
  *
  *    There are no variables left to match with.
  *    The rules are of the form
  *
  *      []
  *      [([],p1,E1),....,([],pn,En)]
  *      default
  *
  *    return: 
  *
  *     if p1 then E1 else break() failWith 
  *     if p2 then E2 else break() failWith 
  *     if p3 then E3 else break() failWith ... failWith default.
  *
  *  When there are variables left to match with, there rules are partitioned to contain first 
  *  column elements of the same form.  These are either all variable patterns, constructor 
  *  patterns, alias patterns, relax, or quotient patterns.
  *
  *  They are processed according to the following rules:
  *
  *  - Variable rule:
  *
  *      All elements in the first column are variable patterns.
  *      We substitute each variable pattern by the first parameter
  *      variable in each of the bodies.
  *
  *  - Constructor rule:
  *
  *      All elements in the first column are constructors.
  *      Constructors with the same head symbol are grouped together (necessary only for embed patterns).
  * 
  *      Given rules:
  *
  *        v :: vars  
  *        [(CONS b1 :: patterns_1,cond1,e1),...,
  *         (CONS bn :: patterns_n,condn,en)]
  *        default
  *
  *      return:
  *
  *        if CONS?(v) then
  *           extract (CONS) (v) :: vars
  *               [(b1 :: patterns_1,cond1,e1),...,
  *                (bn :: patterns_n,condn,en)]
  *               break()
  *        else break()
  *        failWith 
  *        default
  *
  *  - Alias rule:
  *      Aliased patterns are duplicated.
  *
  *      Given:
  *
  *        v::vars
  *        [(Alias(p1,p2)::patterns,cond,e)]
  *        default
  * 
  *     return:
  *
  *       v::v::vars
  *       [(p1::p2::patterns,cond,e)]
  *       default
  *
  *  - Quotient rule:
  *
  *      given:
  *
  *       (v:Q)::vars
  *       [(QuotientPat(pat: t, Q)::patterns,cond,e)]
  *       default
  *
  *     return:
  *
  *       choose(x,v)
  *        (
  *         x::vars
  *         [(pat::patterns,cond,e)]
  *         default
  *        )
  *
  *     alternatively:
  *
  *       rep(v)::vars
  *       [(pat::patterns,cond,e)]
  *       default
  *
  *
  *     case e::es of
  *       | (quotient(Q) pattern,...) -> term
  *       | .. -> term2
  *
  *     translate to:
  *
  *       choose x from e in
  *       case x::es of
  *         | (pattern,...) -> term1
  *         | ... -> term2
  *)

 op substPat (body : MSTerm, pat : MSPattern, value : MSTerm) : MSTerm = 
  if isTrue body then 
    body
  else 
    case pat of
      | WildPat _ -> body
      | VarPat  _ -> mkLet ([(pat, value)], body)
      | _         -> body (* Should not happen *)
      
 (* 
  *  We generate tester functions for the various constructor formats.
  *)

 op embedded (constructorName : String) (trm : MSTerm) : MSTerm = 
  mkApply (mkEmbedded (constructorName, termType trm),
           trm)

 op relaxed (pred : MSTerm) (trm : MSTerm) : MSTerm =
  mkApply (pred, trm)
 
 op equalToConstant (typ, constant : MSTerm) (trm : MSTerm) : MSTerm =
  mkEquality (typ, constant, trm)

 op mkLet (bindings : MSBindings, body : MSTerm) : MSTerm = 
  case bindings of
    | [] -> body
    | _  -> MS.mkLet (bindings, body)
         
 op [a,b] partition (f : a -> b) (qs : List a) : List (List a) = 
  case qs of
    | []  -> []
    | [x] -> [[x]]
    | x :: y :: xs -> 
      let result = partition f (y::xs) in
      if f x = f y then
        tack x result
      else 
        [x] :: result
      
 op [a] tack (x : a) ((xs :: xss) : List (List a)) : List (List a) =
  (x::xs) :: xss

 type RuleType = | Var 
                 | Con 
                 | Alias      MSPattern * MSPattern
                 | Relax      MSPattern * MSTerm 
                 | Quotient   MSPattern * TypeName
                 | Restricted MSPattern * MSTerm 

 op ruleType (rule : Rule) : RuleType = 
  case rule of
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
    | _ -> (printRule rule; fail "Unrecognized ruleType!")

 op printRule (pats : MSPatterns, cond : MSTerm, body : MSTerm) : () =
  let _ = toScreen "Pattern : " in
  let _ = app (fn p -> toScreen (printPattern p ^ " ")) pats in
  let _ = writeLine "" in
  let _ = writeLine ("Condition: " ^ printTerm cond) in
  writeLine ("Body: " ^ printTerm body)

 op sameConstructor (spc : Spec) (p1 : MSPattern, p2 : MSPattern) : Bool = 
  case (p1, p2) of
    | (RecordPat _,         RecordPat _        ) -> true
    | (EmbedPat (e1,_,_,_), EmbedPat (e2,_,_,_)) -> e1 = e2
    | _ -> equivPattern? spc (p1, p2)
      
 (*
  *  op partitionConstructors : Var * Rules -> List DestructedRule
  *
  *  Given a list of rules, where the first pattern of each rule is a constructor
  *  we partition the rules into sequences of the same constructor, and for each
  *  segment of the form:
  *
  *    CONSTR pats_1, patterns_1, cond_1, body_1
  *    CONSTR pats_2, patterns_2, cond_2, body_2
  *    ...
  *    CONSTR pats_n, patterns_n, cond_n, body_n
  *
  *  we transform:
  * 
  *    pats_1, patterns_1, cond_1, body_1
  *    pats_2, patterns_2, cond_2, body_2
  *    ...
  *    pats_n, patterns_n, cond_n, body_n
  *
  *  and also return one version of:
  *
  *     vars     - a list of variables of the same type as pats_i.
  *
  *     bindings - a list of let bindings that bind vars to destructors of a variable v 
  *                that is given as argument to partitionConstructors.
  *
  *                For example, for the pattern {head:pat1, tail:pat2}, bindings = 
  *                  [(VarPat v1, Apply(Fun(Project(head),_), Var v)),
  *                   (VarPat v2, Apply(Fun(Project(tail),_), Var v))]
  *
  *                which in human terms reads as:
  *                  let v1 = v.head and v2 = v.tail in ...
  *
  *     query    - term determining if the input variable v is an instance of constructor CONSTR.
  *      
  *)

 op freshVar (context : Context, typ : MSType) : Var =
  let num = ! context.counter + 1 in
  (context.counter := num;
   ("pV" ^ (Nat.show num), typ))

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

 op coproductFields (spc: Spec, typ: MSType) : List (Id * Option MSType) = 
  let typ = unfoldBase (spc, typ) in
  case typ of
    | CoProduct (fields, _) -> fields
    | Subtype   (tau, _, _) -> coproductFields (spc, tau)
    | Base (Qualified ("List", "List"), [x], _) -> 
      [("Nil",  None), 
       ("Cons", Some (Product ([("1", x), ("2", typ)], 
                               typeAnn typ)))]
    | _ -> System.fail ("CoProduct type expected, but got " ^ printType typ)

 type DestructedRule = {query    : MSTerm,       % e.g. embed? Foo x
                        new_vars : List MSTerm,
                        bindings : MSBindings,
                        pattern  : MSPattern,
                        rules    : Rules}

 op partitionConstructors (context : Context, 
                           trm     : MSTerm, 
                           rules   : Rules) 
  : List DestructedRule =
  let
    def patDecompose (pattern : MSPattern) : MSBindings =
      case pattern of
        | RecordPat (pats,_) -> 
          map (fn (index, p) -> 
                 (p, mkProjectTerm (context.spc, index, trm))) 
              pats
        | EmbedPat (id, Some p, coproduct_type, _) -> 
          let fields = coproductFields (context.spc, coproduct_type) in
          let tm = case findLeftmost (fn (id2, _) -> id = id2) fields of
                     | Some (_, Some field_type) ->
                       mkApply ((Fun (Select id, 
                                      mkArrow (coproduct_type, field_type), 
                                      noPos)), 
                                trm)
                     | _ -> 
                       System.fail "Selection index not found in product"
          in
          [(p, tm)]
        | _ -> [] 

    def insert (rule, drules) : List DestructedRule = 
      case (rule, drules) of
        | ((pat::pats, cond, body), []) -> 
          let query         = queryPat pat trm in
          let decomposition = patDecompose pat in
          let new_vars      = map (fn (p, _) -> 
                                     freshVar (context, patternType p)) 
                                  decomposition 
          in
          let bindings      = ListPair.map (fn ((p, t), v) -> 
                                              (mkVarPat v, t))
                                           (decomposition, new_vars) 
          in
          let new_pats      = map (fn (p, _) -> p) decomposition in
          [{query    = query, 
            new_vars = map mkVar new_vars, 
            bindings = bindings,
            pattern  = pat, 
            rules    = [(new_pats ++ pats, cond, body)]}]

        | ((pat::pats, cond, body), (drule :: drules)) -> 
          let spc = context.spc in
          if sameConstructor spc (pat, drule.pattern) then
            let decomposition = patDecompose pat in
            let new_pats      = map (fn (p, _) -> p) decomposition in
            let new_rule      = (new_pats ++ pats, cond, body) in
            let new_drule     = drule << {rules = new_rule :: drule.rules} in
            new_drule :: drules
          else 
            if exists? (fn drule -> sameConstructor spc (pat, drule.pattern)) drules then
              drule :: insert (rule, drules)
            else 
              insert (rule, []) ++ (drule :: drules)
        | _ -> drules (* should not happen *)
  in
  foldr insert [] rules 
        
 op abstract (vs  : List (String * Var), 
              trm : MSTerm, 
              typ : MSType) 
  : MSTerm = 
  let possible_body = simplifyPatternMatchResult trm in
  let body          = case possible_body of
                        | Some body -> body
                        | _ -> mkApply (mkOp (Qualified ("TranslationBuiltIn", "block"),
                                              mkArrow (match_type typ, typ)), 
                                        trm)
  in
  let pat = case vs of 
              | [(_,v)] -> mkVarPat v
              | _ -> RecordPat (map (fn (index, v)-> (index, mkVarPat v)) vs, 
                                noPos)
  in
  Lambda ([(pat, trueTerm, body)], noPos)

 op match (context : Context, 
           vars    : MSTerms, 
           rules   : Rules, 
           default : MSTerm, 
           break   : MSTerm) 
  : MSTerm = 
  case vars of
    | [] -> foldr (fn ((_,cond,body), default) -> 
                     failWith context 
                              (Utilities.mkIfThenElse (cond, body, break))
                              default)
                  default
                  rules
    | _ -> 
      let rules = (partition ruleType rules) in
      foldr (matchRules (context, break, vars)) 
            default 
            rules
  
 op matchRules (context : Context, 
                break   : MSTerm, 
                vars    : MSTerms) 
               (rules   : Rules, 
                default : MSTerm) 
  : MSTerm = 
  case ruleType (head rules) of
    %% Restricted should be unnecessary because top-level Restricteds have been removed in eliminateTerm
    | Var                        -> matchVar        (context,           vars, rules, default, break)
    | Con                        -> matchCon        (context,           vars, rules, default, break)
    | Alias      (p1,  p2)       -> matchAlias      (context, p1, p2,   vars, rules, default, break)
    | Relax      (pat, pred)     -> matchSubtype    (context, pred,     vars, rules, default, break)
    | Restricted (pat, bool_exp) -> matchRestricted (context, bool_exp, vars, rules, default, break)
    | Quotient    _              -> matchQuotient   (context,           vars, rules, default, break) 
      
 op matchVar (context     : Context, 
              tm :: terms : MSTerms, 
              rules       : Rules,
              default     : MSTerm, 
              break       : MSTerm) 
  : MSTerm = 
  let rules = map (fn rule ->
                     case rule of
                       | (pat :: pats, cond, body) ->
                         (pats, 
                          substPat (cond, pat, tm),
                          substPat (body, pat, tm))
                       | _ -> 
                         System.fail "Empty list of patterns ")
                  rules
  in
  match (context, terms, rules, default, break)

 op matchCon (context : Context, 
              terms   : MSTerms, 
              rules   : Rules,
              default : MSTerm, 
              break   : MSTerm) 
  : MSTerm = 
  let tm :: terms   = terms in
  let rulePartition = partitionConstructors (context, tm, rules) in
  let rule          = foldr (fn (drule, default) ->   
                               Utilities.mkIfThenElse (drule.query, 
                                                       mkLet (drule.bindings,
                                                              match (context,
                                                                     drule.new_vars ++ terms,
                                                                     drule.rules,
                                                                     break,
                                                                     break)),
                                                       default))
                            break 
                            rulePartition
  in
  failWith context rule default

 op matchAlias (context : Context, 
                p1      : MSPattern, 
                p2      : MSPattern, 
                terms   : MSTerms, 
                rules   : Rules, 
                default : MSTerm, 
                break   : MSTerm) 
  : MSTerm = 
  let tm :: _ = terms in
  let rules   = map (fn rule ->
                       case rule of
                         | (_        :: pats, cond, e) ->
                           (p1 :: p2 :: pats, cond, e))
                    rules 
  in
  match (context, tm :: terms, rules, default, break)

 op matchSubtype (context     : Context, 
                  pred        : MSTerm,
                  tm :: terms : MSTerms, 
                  rules       : Rules, 
                  default     : MSTerm, 
                  break       : MSTerm) 
  : MSTerm = 
  let _  = inferType  (context.spc, tm) in
  let t1 = mkRestrict (context.spc, {pred = pred, term = tm}) in
  failWith context 
           (Utilities.mkIfThenElse (mkApply (pred, tm),
                                    match (context, t1::terms, rules, break, break),
                                    break))
           default 

 op matchRestricted (context   : Context, 
                     bool_expr : MSTerm,
                     terms     : MSTerms, 
                     rules     : Rules, 
                     default   : MSTerm, 
                     break     : MSTerm) 
  : MSTerm = 
  let rules  = map (fn rule ->
                      case rule of
                        | ((RestrictedPat (p,_,_))::pats, cond, e) ->
                          (p :: pats,
                           mkSimpConj [cond, bool_expr], 
                           e)
                        | _ -> rule)
                   rules
  in
  match (context, terms, rules, default, break) 

 op matchQuotient (context     : Context, 
                   tm :: terms : MSTerms, 
                   rules       : Rules, 
                   default     : MSTerm, 
                   break       : MSTerm) 
  : MSTerm =
  let q = inferType (context.spc, tm) in
  case unfoldBase (context.spc, q) of
    | Quotient (typ, pred, _) -> 
      %%
      %%    Given current implementation of choose, we compile
      %%     t1 = choose[q] t 
      %%
      let v     = ("v", typ)                                   in
      let f     = mkLambda (VarPat (v, noPos), Var (v, noPos)) in
      let t1    = mkApply  (mkChooseFun (q, typ, typ, f), tm)  in
      let rules = map (fn ((QuotientPat (p, pred, _)) :: pats, cond, e) ->
                         (p::pats, cond, e))
                      rules 
      in
      failWith context
               (match (context, t1::terms, rules, break, break))
               default  
    | _ -> 
      fail ("matchQuotient: expected " ^ printType q ^ " to name a quotient type")

 %% fn (x as pat) -> bod  -->  fn x -> let pat = x in bod
 %% Without this other normalizations such as arity normalization break
 op normalizeSimpleAlias (match : Match) : Match =
  case match of
    | [(AliasPat (VarPat (v, a1), p2, a2), cond, body)] ->
      [(VarPat (v, a1), 
        trueTerm, 
        Apply (Lambda ([(p2, cond, body)], a2), 
               Var (v, a1), 
               a2))]
    | _ -> match

 op splitPattern (arity : Nat, pat : MSPattern) : MSPatterns =
  if arity = 1 then 
    [pat] 
  else
    case pat of
      | RecordPat (fields, _) -> map (fn (_, p)-> p) fields
      | WildPat   (typ,    _) -> tabulate (arity, fn _ -> pat)
      | _ -> System.fail "splitPattern: unexpected pattern" 

 op zipFields (pattern_fields : List (Id * MSPattern), 
               term_fields    : List (Id * MSTerm))
  : MSBindings =
  case (pattern_fields, term_fields) of
    | ([], []) -> []
    | ((_, pat)::fields, (_,t)::terms) -> (pat,t) :: zipFields (fields, terms)
    | _ -> System.fail "zipFields: Uneven length of fields"

 op flattenLetDecl ((pat     : MSPattern, term  : MSTerm), 
                    (context : Context,   decls : MSBindings))
  : Context * MSBindings =
  case (pat, term) of
    | (WildPat (typ,_), Var _)        -> (context, decls)
    | (WildPat (typ,_), Record([],_)) -> (context, decls)
    | (WildPat (typ,_), term)         -> let decl = (mkVarPat (freshVar (context, patternType pat)), term) in
                                         (context, decl :: decls)

    | (RecordPat (fields, _), Record (terms, _)) ->
      foldr flattenLetDecl 
            (context,decls) 
            (zipFields (fields, terms)) 

    | (RecordPat (fields,_), term) -> 
      let v      = freshVar (context, inferType(context.spc, term)) in
      let var    = mkVar v                                          in
      let decls1 = map (fn (id, pat) -> 
                          (pat, mkProjectTerm (context.spc, id, var))) 
                       fields 
      in
      let (context, decls2) = foldr flattenLetDecl (context, decls) decls1 in
      let decl = (mkVarPat v, term) in
      (context, decl :: (decls2 ++ decls))

    | _ -> 
      (context, (pat, term) :: decls)

 op eliminatePattern (context : Context) (pat : MSPattern) : MSPattern = 
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

 op eliminateType (context : Context) (typ : MSType) : MSType =
  case typ of

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
      
    | Boolean _ -> typ
    | TyVar   _ -> typ
    | Any     _ -> typ

    | And (types,    a) -> And (map (eliminateType context) types, a)
    | Pi  (tvs, typ, a) -> Pi  (tvs, eliminateType context typ,    a)

 (* Generate the default catch all case given a set of rules *)

 op makeFail (context : Context, typ : MSType, _ : MSTerm) : MSTerm =
  let index = ! context.errorIndex + 1 in
  (context.errorIndex := index;
   let typ1 = mkArrow(typ,match_type typ) in
   let msg  = "Nonexhaustive match failure [\#" ^ (show index) ^ "] in " ^ context.funName in
   mkApply (mkOp (Qualified ("TranslationBuiltIn", "mkFail"), typ1),
            mkString msg))

 op makeDefault (context : Context, 
                 typ     : MSType, 
                 rules   : Match,
                 vs      : List (String * Var),
                 term    : MSTerm) 
  : Match * MSTerm = 
  let 
     def loop (rules, first_rules) =
       case rules of

         | [] -> 
           (reverse first_rules, makeFail (context, typ, term))

         | [(WildPat _, Fun (Bool true, _, _), body)] ->
           (reverse first_rules, mkSuccess (typ, body))

         | [(VarPat (v, _), Fun (Bool true, _, _), body)] ->
           let term =
               case vs of
                 | [(_, v)] -> Var (v, noPos)
                 | _ -> Record (map (fn(l,v)-> (l, mkVar v)) vs, 
                                noPos) 
           in
           let body = mkLet ([(VarPat (v, noPos),term)], body) in
           (reverse first_rules, mkSuccess (typ, body))

         | rule :: rules ->
           loop (rules, rule :: first_rules)
   in
   loop (rules, [])

 op wildPattern? (rule : MSRule) : Bool =
  case rule of
    | (WildPat _,     Fun (Bool true,_,_), _) -> true
    | (VarPat (v, _), Fun (Bool true,_,_), _) -> true
    | _ -> false

 op checkUnreachableCase (context : Context, term : MSTerm, rules : MSRules) : () =
  let 
    def nonfinalWildPattern? rules =
      case rules of
        | []  -> false
        | [_] -> false
        | rule :: rules ->
          wildPattern? rule || nonfinalWildPattern? rules
  in
  if nonfinalWildPattern? rules then
    writeLine ("checkUnreachableCase: Unreachable case in " ^ context.funName ^ "\n" ^ printTerm term)
  else 
    ()

 %%% The last case of a Lambda case has the obligation of always matching, so if it
 %%% is has | (such-that) clause, there is the obligation that it is true

 op alwaysCheckRestrictedPatInLambda? : Bool = false

 op eliminateTerm (context : Context) (term : MSTerm) : MSTerm =
  case term of
    | Lambda (rules,_) ->
      let rules = normalizeSimpleAlias rules in
      let arity = matchArity           rules in
      let rules = map (fn (p, c, b)-> 
                         (eliminatePattern context p,
                          eliminateTerm    context c,
                          eliminateTerm    context b)) 
                      rules 
      in
      if simpleAbstraction rules then
        let rules = map (fn (p, c, a) -> (deRestrict p, c, a)) rules in
        Lambda (rules, noPos)
      else 
        % let _ = writeLine "Elimination from lambda " in
        let _ = checkUnreachableCase (context, term, rules) in

        %% Move RestrictedPat conditions to condition
        %% Not singleton because obligation should ensure this is always true unless alwaysCheckRestrictedPatInLambda?
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
        % let _ = writeLine "Elimination from lambda: rules "                   in
        let (rules, default)  = makeDefault (context, bdyType, rules, vs, term) in
        let rules = map (fn (p, c, t) -> 
                           (splitPattern(arity,p), c, mkSuccess (bdyType, t))) 
                        rules 
        in
        let vars = map (fn (_, v) -> mkVar v) vs                                            in
        let trm  = match (storeTerm (term, context), vars, rules, default, mkBreak bdyType) in
        let trm  = abstract (vs, trm, bdyType)                                              in
        trm

    | Let (decls, body,_) -> 

     %% Treatment of let-bound patterns is optimized with respect to a number
     %% of special cases: Wildcards, trivially satisfiable patterns, Non-flattened patterns, etc.

     let decls = map (fn (p, e) -> 
                        (eliminatePattern context p,
                         eliminateTerm    context e))
                     decls
     in
     let body  = eliminateTerm context body in
     %% Translate non-recursive non-simple let patterns into application
    
     let (context, decls) = foldr flattenLetDecl (context,decls) [] in
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
       let bdyTyp = inferType (context. spc, body) in
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
                       [(pats, trueTerm, mkSuccess (bdyTyp, body))] : Rules,
                       makeFail (context, bdyTyp, term),
                       mkBreak bdyTyp) 
       in
       let tm = abstract (vars, tm, bdyTyp) in
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

    | The ((id, typ),                       tm,                       a) -> 
      The ((id, eliminateType context typ), eliminateTerm context tm, a)

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

    | _ ->
      term

 op simplifyPatternMatchResult (term : MSTerm) : Option MSTerm =
  let 

    def simpRec (t1, t2) =
      case t1 of
        | IfThenElse (p, x, y, pos) ->
          (case simpSuccess x of
             | Some simp_x ->
               (case simpRec (y, t2) of
                  | Some simp_y -> Some (IfThenElse (p, simp_x, simp_y, pos))
                  | _ -> None)
             | _ ->
               if simpleSuccTerm? t2 then
                 case simpRec (x, t2) of
                   | Some simp_x ->
                     (case simpRec (y, t2) of
                        | Some simp_y -> Some (IfThenElse (p, simp_x, simp_y, pos))
                        | _ -> None)
                   | _ -> None
               else 
                 None)

        | Fun (Op (Qualified ("TranslationBuiltIn", "mkBreak"),_),_,_) -> 
          simpSuccess t2

        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkSuccess"),_),_,_), 
                 arg,
                 _) 
          ->
          Some arg   % t2 is unreachable

        | Let (bindings, body, pos) ->
          (case simpRec (body, t2) of
             | Some simp_body -> Some (Let (bindings, simp_body, pos))
             | _ -> None)

        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"),_),_,_),
                 Record ([("1", arg), ("2", failure)], _),
                 _) 
          ->
          (case simpRec (failure, t2) of
             | Some simp_failure -> simpRec (arg, simpLet simp_failure)
             | _ -> None)

        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkFail"),_),_,_),_,_) -> 
          Some t1

        | _ -> 
          None

    def simpSuccess tm =
      case tm of

        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkSuccess"),_),_,_), t1, _) -> 
          Some t1

        | Let (bindings, body, pos) ->
          (case simpSuccess body of
             | Some simp_body -> Some (Let (bindings, simp_body, pos))
             | _ -> None)

        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"),_),_,_),
                 Record ([("1",t1), ("2",t2)],_),
                 _) 
          ->
          simpRec (t1, t2)
          
        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkFail"),_),_,_),
                 _,
                 _) 
          -> 
          Some tm

        | _ -> 
          None         
  in
  case term of

    | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"),_),_,_),
             Record ([("1",t1), ("2",t2)],_), 
             _)
      ->
      simpRec (t1, simpLet t2)

    | _ -> 
      None
     
 op simpLamBody (term : MSTerm) : MSTerm =
  case term of
    | Lambda ([(pat, c, Apply (Lambda ([(VarPat (v,_), _, body)], _), wVar as Var _, _))], pos) ->
      Lambda ([(pat, c, substitute (body, [(v, wVar)]))],                                  pos)
    | _ -> term

 op simpLet (term : MSTerm) : MSTerm =
  case term of

    | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkSuccess"),a1), t1, a2), arg,         a3) ->
      Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkSuccess"),a1), t1, a2), simpLet arg, a3)

    | Let ([(VarPat (id,_), value)], body, _) ->
      (case countVarRefs (body, id) of
         | 0 -> if sideEffectFree value then body else term
         | _ -> term)

    | _ -> term

 op simpleSuccTerm? (tm : MSTerm) : Bool =
  case tm of
    | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkSuccess"),_),_,_), arg, _) -> 
      simpleSuccTerm? arg
    | Var    _       -> true
    | Fun    _       -> true
    | Record ([], _) -> true
    | _              -> false

 %- --------------------------------------------------------------------------------
 %- checks whether Record is a Product or a user-level Record

 op [a] isShortTuple (i : Nat, row : List (Id * a)) : Bool =
  case row of
    | [] -> true
    | (lbl, r) :: row -> 
      (lbl = Nat.show i) && isShortTuple (i + 1, row)

 op [a] recordfields? (fields : List (Id * a)) : Bool =
  ~ (isShortTuple (1, fields))

 (*
  * Dropped arity raising for the first round of pattern matching compilation.
  * let term = mapTerm(arityRaising,fn x -> x,fn x -> x) term in
  * let term = mapTerm(elimPattern,fn x -> x,fn x -> x) term in
  * (%%% writeLine "Pattern eliminated";
  *  term)
  *)

 op mkSpcContext (spc: Spec) (fun_name: String): Context =
  {counter    = Ref 0,
   spc        = spc,
   funName    = fun_name, % used when constructing error messages
   errorIndex = Ref 0,    % used to distinguish error messages
   term       = None}

 op translateMatchInTerm (spc: Spec) (fun_name: String) (tm: MSTerm): MSTerm =
  simpLamBody(eliminateTerm (mkSpcContext spc fun_name) tm)

 op SpecTransform.translateMatch (spc : Spec) : Spec = 
  % sjw: Moved (Ref 0) in-line in mkSpcContext so it is reexecuted for each call so the counter is reinitialized
  % for each call. (This was presumably what was intended as otherwise there would be no need for mkContext
  % to be a function). This means that compiled functions will have the same generated variables
  % independent of the rest of the file.
  let 
    def mkContext funName = mkSpcContext spc funName 
  in
  let new_types =
      mapTypeInfos (fn info ->
                      let Qualified (_,id) = primaryTypeName info in
                      let (old_decls, old_defs) = typeInfoDeclsAndDefs info in
                      let new_defs =
                          map (fn dfn ->
                                 let (tvs, typ) = unpackType dfn in
                                 let new_type = eliminateType (mkContext id) typ in
                                 maybePiType (tvs, new_type))
                              old_defs
                      in
                      let new_dfn = maybeAndType (old_decls ++ new_defs, typeAnn info.dfn) in
                      info << {dfn = new_dfn}) 
                   spc.types
  in
  let new_ops =
      mapOpInfos (fn info ->
                    let Qualified (_,id) = primaryOpName info in
                    let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                    let new_defs = 
                        map (fn dfn ->
                               let (tvs, typ, term) = unpackFirstTerm dfn in
                               if anyTerm? term then 
                                 dfn
                               else
                                 let new_typ = eliminateType (mkContext id) typ in
                                 let new_tm  = eliminateTerm (mkContext id) term in
                                 let new_tm = simpLamBody new_tm in
                                 maybePiTerm (tvs, TypedTerm (new_tm, new_typ, termAnn term)))
                            old_defs
                    in
                    let new_dfn = maybeAndTerm (old_decls ++ new_defs, termAnn info.dfn) in
                    info << {dfn = new_dfn})
                 spc.ops
  in
  let new_elements =
      map (fn el ->
             case el of
               | Property (pt, pname as Qualified (_, id), tyvars, term, a) -> 
                 Property (pt, pname, tyvars, eliminateTerm (mkContext id) term, a)
               | _ -> el) 
          spc.elements
  in
  spc << {types    = new_types,
          ops      = new_ops, 
          elements = new_elements}

end-spec
