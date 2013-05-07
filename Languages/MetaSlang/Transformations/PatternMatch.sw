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
   
 type PMRules = List PMRule                       % NOTE: not the same as MSRules (aka Match)
 type PMRule  = List MSPattern * MSTerm * MSTerm  % Note: not the same as MSRule, has list of patterns

 type Context = {counter     : Ref Nat,        % counter for variable numbering
                 spc         : Spec,
                 error_index : Ref Nat,        % to discriminate error messages
                 op_name     : String,         % for error messages
                 lambda      : Option MSTerm}  % for error messages

 op match_type (typ : MSType) : MSType = 
  typ 

 op mkBreak (typ : MSType) : MSTerm = 
  mkOp (Qualified ("TranslationBuiltIn", "mkBreak"), match_type typ)

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
  *   failWith (body, continuation) = 
  *     case evaluate body of
  *       | Succcess result -> Success result
  *       | Break           -> evaluate continuation
  *       | Fail            -> evaluate continuation
  *
  *   when compiled to LISP, C, or JAVA, failWith unfolds to the continuations used in block statements.
  *   Break results in a break;
  *   IfThenElse (a, b, Break) translates to if (a) {b};
  *   Success (result) translates to return (result);
  *)

 op failWith (ctx : Context) (body : MSTerm) (continuation : MSTerm) : MSTerm =
  if isBreak continuation then 
    body 
  else if isSuccess body then 
    %% Warn that continuation is not a break, yet we will never reach it.
    %% TODO: what if continuation is a fail?
    let _ = warnUnreachable ctx in
    body
  else
    let typ  = inferType (ctx.spc, body) in
    let typ  = mkArrow (mkProduct [typ,typ], typ) in
    let trm  = mkApply (mkOp (Qualified ("TranslationBuiltIn", "failWith"), typ), 
                        mkRecord [("1", body), ("2", continuation)])
    in
    trm

 op storeLambda (trm : MSTerm, ctx : Context) : Context =
  %% used just to make msg in warnUnreachable
  ctx << {lambda = Some trm}

 op warnUnreachable (ctx : Context) : () =
  writeLine ("Warning: Redundant case in " ^ ctx.op_name ^ "\n" ^ 
               (case ctx.lambda of
                  | Some tm -> printTerm tm
                  | _ -> ""))
  

 % op  mkProjectTerm (spc : Spec, id   : Id,     trm : MSTerm) : MSTerm = SpecEnvironment.mkProjectTerm
 % op  mkRestrict    (spc : Spec, pred : MSTerm, trm : MSTerm} : MSTerm = SpecEnvironment.mkRestrict
  
 (* 
  * The following invariant holds of the patterns:
  *  - for a call to match (vars, pmrules, continuation):
  *    each list of patterns in the pmrules has the same length and typing 
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
  *      continuation
  *
  *    return: 
  *
  *     if p1 then E1 else break() failWith 
  *     if p2 then E2 else break() failWith 
  *     if p3 then E3 else break() failWith ... failWith continuation.
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
  *        continuation
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
  *        continuation
  *
  *  - Alias rule:
  *      Aliased patterns are duplicated.
  *
  *      Given:
  *
  *        v::vars
  *        [(Alias(p1,p2)::patterns,cond,e)]
  *        continuation
  * 
  *     return:
  *
  *       v::v::vars
  *       [(p1::p2::patterns,cond,e)]
  *       continuation
  *
  *  - Quotient rule:
  *
  *      given:
  *
  *       (v:Q)::vars
  *       [(QuotientPat(pat: t, Q)::patterns,cond,e)]
  *       continuation
  *
  *     return:
  *
  *       choose(x,v)
  *        (
  *         x::vars
  *         [(pat::patterns,cond,e)]
  *         continuation
  *        )
  *
  *     alternatively:
  *
  *       rep(v)::vars
  *       [(pat::patterns,cond,e)]
  *       continuation
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

 type PMRuleType = | Var 
                   | Con 
                   | Alias      MSPattern * MSPattern
                   | Relax      MSPattern * MSTerm 
                   | Quotient   MSPattern * TypeName
                   | Restricted MSPattern * MSTerm 

 op pmRuleType (pmrule : PMRule) : PMRuleType = 
  %% just look at first pattern
  case pmrule of
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
    | _ -> (printPMRule pmrule; fail "Unrecognized ruleType!")

 op printPMRule (pats : MSPatterns, cond : MSTerm, body : MSTerm) : () =
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
  *  op partitionConstructors : Var * MSRules -> DestructuredRules
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
  *  we transform to:
  * 
  *    pats_1, patterns_1, cond_1, body_1
  *    pats_2, patterns_2, cond_2, body_2
  *    ...
  *    pats_n, patterns_n, cond_n, body_n
  *
  *  and also return one version of:
  *
  *     query    - term determining if the input variable v is an instance of constructor CONSTR.
  *      
  *     vars     - a list of variables of the same type as pats_i.
  *
  *     bindings - a list of let bindings that bind vars to destructors of a variable v 
  *                that is given as argument to partitionConstructors.
  *
  *                For example, for the pattern {head:pat1, tail:pat2}, 
  *
  *                bindings = 
  *                  [(VarPat v1, Apply(Fun(Project(head),_), Var v)),
  *                   (VarPat v2, Apply(Fun(Project(tail),_), Var v))]
  *
  *                which in human terms reads as:
  *                  let v1 = v.head and v2 = v.tail in ...
  *
  *)

 op freshVar (ctx : Context, typ : MSType) : Var =
  let num = ! ctx.counter + 1 in
  (ctx.counter := num;
   ("pV" ^ (Nat.show num), typ))

 op freshVars (num : Nat, ctx : Context, pat : MSPattern) : List (String * Var) =
  case num of
    | 0 -> []
    | 1 -> [("", freshVar (ctx, patternType pat))]
    | _ ->
      case pat of
        | RecordPat(fields,_) -> 
          map (fn (l, p) -> (l, freshVar (ctx, patternType p)))
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

 type DestructuredRules = List DestructuredRule
 type DestructuredRule  = {query    : MSTerm,       % e.g. embed? Foo x -- tests to see if argument matches constructor
                           new_vars : MSTerms,      % vars that will be bound to args in term, e.g `x' and `y' in  `Foo (x,y)'
                           bindings : MSBindings,   % each binding associates a var with an extractor from the term
                           pattern  : MSPattern,    % original pattern
                           pmrules  : PMRules}

 op partitionConstructors (ctx     : Context, 
                           trm     : MSTerm, 
                           pmrules : PMRules) 
  : DestructuredRules =
  let
    def patDecompose (pattern : MSPattern) : MSBindings =
      case pattern of

        | RecordPat (pats,_) -> 
          %% list of patterns with projections
          map (fn (index, p) -> 
                 (p, mkProjectTerm (ctx.spc, index, trm))) 
              pats

        | EmbedPat (id, Some p, coproduct_type, _) -> 
          %% singleton list of a pattern with a selection 
          let fields = coproductFields (ctx.spc, coproduct_type) in
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

    def insert (pmrule, drules) : DestructuredRules = 
      case (pmrule, drules) of

        | ((pat::pats, cond, body), []) -> 
          %% create new drule:

          let query                = queryPat pat trm in
          let pats_with_extractors = patDecompose pat in 

          %% pats_with_extractors is either:
          %%   a list of patterns, each paired with a corresponding projections, or
          %%   a singleton list of one pattern paired with a selection operation.

          %% new_vs will be used for vars that bind to args in constructor term
          %% bindings will extract values for vars from constructor term
          let new_vs     = map (fn (pat, _) -> 
                                  freshVar (ctx, patternType pat)) 
                               pats_with_extractors 
          in
          let bindings   = map (fn (v, (_, extractor)) -> 
                                  (mkVarPat v, extractor))
                               (new_vs, pats_with_extractors)
          in

          %% new_pats will decribe how to destructure vars
          %% new_vars are terms corresponding to new_pats
          let new_pats   = map (fn (pat, _) -> pat) pats_with_extractors in
          let new_vars   = map mkVar new_vs                              in
          let new_pmrule = (new_pats ++ pats, cond, body)                in

          let new_drule  = {query    = query, 
                            new_vars = new_vars,
                            bindings = bindings,
                            pattern  = pat, 
                            pmrules  = [new_pmrule]}
          in 
          [new_drule]

        | ((pat::pats, cond, body), (drule :: drules)) -> 
          let spc = ctx.spc in
          if sameConstructor spc (pat, drule.pattern) then
            %% add pattern to existing drule for same constructor
            let pats_with_extractors = patDecompose pat in 
            let new_pats             = map (fn (pat, _) -> pat) pats_with_extractors in
            let new_pmrule           = (new_pats ++ pats, cond, body) in
            let revised_drule        = drule << {pmrules = new_pmrule :: drule.pmrules} in
            revised_drule :: drules
          else 
            %% TODO: wierdly ineffecient way to amend an element in a list
            %% repeats exists? test for every tail of list
            if exists? (fn drule -> sameConstructor spc (pat, drule.pattern)) drules then
              %% walk past non-matching drule on way to a matching one (that we know exists)
              drule :: insert (pmrule, drules)
            else 
              %% otherwise create new drule
              insert (pmrule, []) ++ (drule :: drules)

        | _ -> drules (* should not happen *)
  in
  foldr insert [] pmrules 
        
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

 op match (ctx          : Context, 
           vars         : MSTerms, 
           pmrules      : PMRules, 
           continuation : MSTerm, 
           break        : MSTerm) 
  : MSTerm = 
  case vars of
    | [] -> foldr (fn ((_,cond,body), continuation) -> 
                     %% this may optimize IfThenElse based on actual terms:
                     let body = Utilities.mkIfThenElse (cond, body, break) in
                     failWith ctx body continuation)
                  continuation
                  pmrules
    | _ -> 
      let pmrules = partition pmRuleType pmrules in
      foldr (matchPMRules (ctx, break, vars)) 
            continuation 
            pmrules
  
 op matchPMRules (ctx          : Context, 
                  break        : MSTerm, 
                  vars         : MSTerms) 
                 (pmrules      : PMRules, 
                  continuation : MSTerm) 
  : MSTerm = 
  case pmRuleType (head pmrules) of
    | Var                        -> matchVar        (ctx,           vars, pmrules, continuation, break)
    | Con                        -> matchCon        (ctx,           vars, pmrules, continuation, break)
    | Alias      (p1,  p2)       -> matchAlias      (ctx, p1, p2,   vars, pmrules, continuation, break)
    | Relax      (pat, pred)     -> matchSubtype    (ctx, pred,     vars, pmrules, continuation, break)
    | Quotient    _              -> matchQuotient   (ctx,           vars, pmrules, continuation, break) 
    %% Restricted should be unnecessary because top-level Restricteds have been removed in eliminateTerm
    | Restricted (pat, bool_exp) -> matchRestricted (ctx, bool_exp, vars, pmrules, continuation, break)
      
 op matchVar (ctx          : Context, 
              tm :: terms  : MSTerms, 
              pmrules      : PMRules,
              continuation : MSTerm, 
              break        : MSTerm) 
  : MSTerm = 
  let pmrules = map (fn pmrule ->
                       case pmrule of
                         | (pat :: pats, cond, body) ->
                           (pats, 
                            substPat (cond, pat, tm),
                            substPat (body, pat, tm))
                         | _ -> 
                           System.fail "Empty list of patterns ")
                    pmrules
  in
  match (ctx, terms, pmrules, continuation, break)

 op matchCon (ctx          : Context, 
              terms        : MSTerms, 
              pmrules      : PMRules,
              continuation : MSTerm, 
              break        : MSTerm) 
  : MSTerm = 
  let tm :: terms     = terms in  % use tm in Let binding, terms in Let body
  let pmRulePartition = partitionConstructors (ctx, tm, pmrules) in
  let body            = foldr (fn (drule, continuation) ->   
                                 %% this may optimize IfThenElse based on actual terms:
                                 Utilities.mkIfThenElse (drule.query, 
                                                         mkLet (drule.bindings,
                                                                match (ctx,
                                                                       drule.new_vars ++ terms,
                                                                       drule.pmrules,
                                                                       break,
                                                                       break)),
                                                         continuation))
                              break 
                              pmRulePartition
  in
  failWith ctx body continuation

 op matchAlias (ctx          : Context, 
                p1           : MSPattern, 
                p2           : MSPattern, 
                terms        : MSTerms, 
                pmrules      : PMRules, 
                continuation : MSTerm, 
                break        : MSTerm) 
  : MSTerm = 
  let tm :: _ = terms in
  let pmrules = map (fn pmrule ->
                       case pmrule of
                         | (_        :: pats, cond, e) ->
                           (p1 :: p2 :: pats, cond, e))
                    pmrules 
  in
  %% replicate tm
  match (ctx, tm :: terms, pmrules, continuation, break)

 op matchSubtype (ctx          : Context, 
                  pred         : MSTerm,
                  tm :: terms  : MSTerms, 
                  pmrules      : PMRules, 
                  continuation : MSTerm, 
                  break        : MSTerm) 
  : MSTerm = 
  let _    = inferType  (ctx.spc, tm) in
  let t1   = mkRestrict (ctx.spc, {pred = pred, term = tm}) in
  %% this may optimize IfThenElse based on actual terms:
  let body = Utilities.mkIfThenElse (mkApply (pred, tm),
                                     match (ctx, t1::terms, pmrules, break, break),
                                     break)
  in
  failWith ctx body continuation 

 op matchRestricted (ctx          : Context, 
                     bool_expr    : MSTerm,
                     terms        : MSTerms, 
                     pmrules      : PMRules, 
                     continuation : MSTerm, 
                     break        : MSTerm) 
  : MSTerm = 
  let pmrules = map (fn pmrule ->
                      case pmrule of
                        | ((RestrictedPat (p,_,_))::pats, cond, e) ->
                          (p :: pats,
                           mkSimpConj [cond, bool_expr], 
                           e)
                        | _ -> pmrule)
                    pmrules
  in
  match (ctx, terms, pmrules, continuation, break) 

 op matchQuotient (ctx          : Context, 
                   tm :: terms  : MSTerms, 
                   pmrules      : PMRules, 
                   continuation : MSTerm, 
                   break        : MSTerm) 
  : MSTerm =
  let q = inferType (ctx.spc, tm) in
  case unfoldBase (ctx.spc, q) of
    | Quotient (typ, pred, _) -> 
      %%
      %%    Given current implementation of choose, we compile
      %%     t1 = choose[q] t 
      %%
      let v       = ("v", typ)                                   in
      let f       = mkLambda (VarPat (v, noPos), Var (v, noPos)) in
      let t1      = mkApply  (mkChooseFun (q, typ, typ, f), tm)  in
      let pmrules = map (fn ((QuotientPat (p, pred, _)) :: pats, cond, e) ->
                           (p::pats, cond, e))
                        pmrules 
      in
      let body    = match (ctx, t1::terms, pmrules, break, break) in
      failWith ctx body continuation  
    | _ -> 
      fail ("matchQuotient: expected " ^ printType q ^ " to name a quotient type")

 %% fn (x as pat) -> bod  -->  fn x -> let pat = x in bod
 %% Without this other normalizations such as arity normalization break
 op normalizeSimpleAlias (msrules : MSRules) : MSRules =
  case msrules of
    | [(AliasPat (VarPat (v, a1), p2, a2), cond, body)] ->
      [(VarPat (v, a1), 
        trueTerm, 
        Apply (Lambda ([(p2, cond, body)], a2), 
               Var (v, a1), 
               a2))]
    | _ -> msrules

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

 op flattenLetBinding (binding as (pat : MSPattern, term  : MSTerm), 
                       (ctx : Context,   bindings : MSBindings))
  : Context * MSBindings =
  case (pat, term) of
    | (WildPat (typ,_), Var _)        -> (ctx, bindings)
    | (WildPat (typ,_), Record([],_)) -> (ctx, bindings)
    | (WildPat (typ,_), term)         -> let new_pat = mkVarPat (freshVar (ctx, patternType pat)) in
                                         let new_binding = (new_pat, term) in
                                         (ctx, new_binding :: bindings)

    | (RecordPat (fields, _), Record (terms, _)) ->
      foldr flattenLetBinding 
            (ctx, bindings) 
            (zipFields (fields, terms)) 

    | (RecordPat (fields,_), term) -> 
      let v            = freshVar (ctx, inferType (ctx.spc, term)) in
      let var          = mkVar v                                   in
      let new_bindings = map (fn (id, pat) -> 
                                (pat, mkProjectTerm (ctx.spc, id, var))) 
                             fields 
      in
      let (ctx, new_bindings) = foldr flattenLetBinding (ctx, bindings) new_bindings in
      let new_binding = (mkVarPat v, term) in
      %% TODO:  just new_bindings ??
      (ctx, new_binding :: (new_bindings ++ bindings))

    | _ -> 
      (ctx, binding :: bindings)

 op eliminatePattern (ctx : Context) (pat : MSPattern) : MSPattern = 
  case pat of

    | AliasPat (                     p1,                      p2, a) -> 
      AliasPat (eliminatePattern ctx p1, eliminatePattern ctx p2, a)

    | VarPat ((n,                   s), a) -> 
      VarPat ((n, eliminateType ctx s), a)
      
    | EmbedPat (i, Some                       p ,                   s, a) ->
      EmbedPat (i, Some (eliminatePattern ctx p), eliminateType ctx s, a)
      
    | EmbedPat (i, None,                   s, a) ->
      EmbedPat (i, None, eliminateType ctx s, a)
      
    | RecordPat (                                              fields, a) -> 
      RecordPat (map (fn (i, p)-> (i, eliminatePattern ctx p)) fields, a)
      
    | WildPat   (s, a) -> VarPat (freshVar (ctx, eliminateType ctx s), a)
    | StringPat (s, a) -> StringPat (s, a)
    | BoolPat   (b, a) -> BoolPat   (b, a)
    | CharPat   (c, a) -> CharPat   (c, a)
    | NatPat    (n, a) -> NatPat    (n, a)
      
    | QuotientPat  (                     p, qid, a) ->
      QuotientPat  (eliminatePattern ctx p, qid, a)
      
    | RestrictedPat (                     p,                   tm, a) ->
      RestrictedPat (eliminatePattern ctx p, eliminateTerm ctx tm, a)
      
    | TypedPat (                     p,                   ty, a) ->
      TypedPat (eliminatePattern ctx p, eliminateType ctx ty, a)

 op eliminateType (ctx : Context) (typ : MSType) : MSType =
  case typ of

    | Arrow (                  s1,                   s2, a) -> 
      Arrow (eliminateType ctx s1, eliminateType ctx s2, a)
      
    | Product (                                            fields, a) -> 
      Product (map (fn (i, s) -> (i, eliminateType ctx s)) fields, a)
      
    | CoProduct (fields, a) -> 
      CoProduct (map (fn (i, x) -> 
                        (i,
                         case x of
                           | Some s -> Some (eliminateType ctx s)
                           | _ -> None))
                   fields,
                 a)
      
    | Quotient (                  s,                   tm, a) -> 
      Quotient (eliminateType ctx s, eliminateTerm ctx tm, a)
      
    | Subtype (                  s, tm, a) -> 
      % Subtype predicates aren't used in code generation (??), so omit eliminateTerm ctx tm,  ????
      Subtype (eliminateType ctx s, tm, a) 
      
    | Base (qid,                         types, a) -> 
      Base (qid, map (eliminateType ctx) types, a)
      
    | Boolean _ -> typ
    | TyVar   _ -> typ
    | Any     _ -> typ

    | And (                        types, a) -> 
      And (map (eliminateType ctx) types, a)

    | Pi (tvs,                   typ, a) -> 
      Pi (tvs, eliminateType ctx typ, a)

 op makeFail (ctx : Context, typ : MSType, _ : MSTerm) : MSTerm =
  %% Generate the continuation catch all case given a set of pattern matching rules.
  let index = ! ctx.error_index + 1 in
  (ctx.error_index := index;
   let typ1 = mkArrow(typ,match_type typ) in
   let msg  = "Nonexhaustive match failure [\#" ^ (show index) ^ "] in " ^ ctx.op_name in
   mkApply (mkOp (Qualified ("TranslationBuiltIn", "mkFail"), typ1),
            mkString msg))

 op makeContinuation (ctx     : Context, 
                      typ     : MSType, 
                      msrules : MSRules,
                      vs      : List (String * Var),
                      term    : MSTerm) 
  : MSRules * MSTerm = 
  let 
     def loop (msrules, first_msrules) =
       case msrules of

         | [] -> 
           (reverse first_msrules, makeFail (ctx, typ, term))

         | [(WildPat _, Fun (Bool true, _, _), body)] ->
           (reverse first_msrules, mkSuccess (typ, body))

         | [(VarPat (v, _), Fun (Bool true, _, _), body)] ->
           let term =
               case vs of
                 | [(_, v)] -> Var (v, noPos)
                 | _ -> Record (map (fn(l,v)-> (l, mkVar v)) vs, 
                                noPos) 
           in
           let body = mkLet ([(VarPat (v, noPos), term)], body) in
           (reverse first_msrules, mkSuccess (typ, body))

         | msrule :: msrules ->
           loop (msrules, msrule :: first_msrules)
   in
   loop (msrules, [])

 op wildPattern? (msrule : MSRule) : Bool =
  case msrule of
    | (WildPat _,     Fun (Bool true,_,_), _) -> true
    | (VarPat (v, _), Fun (Bool true,_,_), _) -> true
    | _ -> false

 op checkUnreachableCase (ctx : Context, term : MSTerm, msrules : MSRules) : () =
  let 
    def nonfinalWildPattern? msrules =
      case msrules of
        | []  -> false
        | [_] -> false
        | msrule :: msrules ->
          wildPattern? msrule || nonfinalWildPattern? msrules
  in
  if nonfinalWildPattern? msrules then
    writeLine ("checkUnreachableCase: Unreachable case in " ^ ctx.op_name ^ "\n" ^ printTerm term)
  else 
    ()

 %%% The last case of a Lambda case has the obligation of always matching, so if it
 %%% is has | (such-that) clause, there is the obligation that it is true

 op alwaysCheckRestrictedPatInLambda? : Bool = false

 op eliminateTerm (ctx : Context) (term : MSTerm) : MSTerm =
  case term of
    | Lambda (msrules,_) ->
      let msrules = normalizeSimpleAlias msrules in
      let msrules = map (fn (p, c, b)-> 
                         (eliminatePattern ctx p,
                          eliminateTerm    ctx c,
                          eliminateTerm    ctx b)) 
                        msrules 
      in
      let arity   = matchArity msrules in
      if simpleAbstraction msrules then
        let msrules = map (fn (pat, cond, body) -> (deRestrict pat, cond, body)) msrules in
        Lambda (msrules, noPos)
      else 
        % let _ = writeLine "Elimination from lambda " in
        let _ = checkUnreachableCase (ctx, term, msrules) in

        %% TODO: This is the only code in Specware that uses Lambda condition field
        %%       Change to use RestrictedPat ?
        %% Move RestrictedPat conditions to condition
        %% Unless alwaysCheckRestrictedPatInLambda? is true, don't add condition,
        %%  because singleton has obligation to always be true.

        let msrules =
            case msrules of

              | [(RestrictedPat (pat, rcond, _), cond, body)] | ~ alwaysCheckRestrictedPatInLambda? ->
                [(pat, cond, body)]

              | _ -> map (fn msrule ->
                            case msrule of 
                              | (RestrictedPat (pat, rcond, _), cond,                     body) ->
                                (pat,                           mkSimpConj [rcond, cond], body)
                              | _ -> msrule)
                         msrules
        in         
        let (pat, cond, body)       = head msrules                                                     in
        let body_type               = inferType (ctx.spc, body)                                        in
        let indices_and_vs          = freshVars (arity, ctx, pat)                                      in
        let (msrules, continuation) = makeContinuation (ctx, body_type, msrules, indices_and_vs, term) in
        let pmrules                 = map (fn (pat, cond, body) -> 
                                             (splitPattern (arity, pat), 
                                              cond, 
                                              mkSuccess (body_type, body))) 
                                          msrules 
        in
        let vars = map (fn (_, v) -> mkVar v) indices_and_vs                   in
        let ctx  = storeLambda (term, ctx)                                     in
        let trm  = match (ctx, vars, pmrules, continuation, mkBreak body_type) in
        let trm  = abstract (indices_and_vs, trm, body_type)                   in
        trm

    | Let (bindings, body,_) -> 

     %% Treatment of let-bound patterns is optimized with respect to a number
     %% of special cases: Wildcards, trivially satisfiable patterns, Non-flattened patterns, etc.

     let bindings = map (fn (pat, exp) -> 
                        (eliminatePattern ctx pat,
                         eliminateTerm    ctx exp))
                     bindings
     in
     let body  = eliminateTerm ctx body in
     %% Translate non-recursive non-simple let patterns into application
    
     let (ctx, bindings) = foldr flattenLetBinding (ctx,bindings) [] in
     if forall? (fn (pat, _)-> simplePattern pat) bindings then
       mkLet (bindings, body)
     else 
       % let _ = writeLine "Let pattern elimination " in
       let (pats, terms) = unzip bindings in
       let trm = 
           case terms of
             | [tm]  -> tm
             | terms -> mkTuple terms
       in
       let body_type = inferType (ctx. spc, body)                           in
       let vs        = map (fn pat -> freshVar (ctx, patternType pat)) pats in
       let (indices_and_vs,_) = 
           foldl (fn ((vars, num), v) -> 
                    let new_var = (Nat.show num, v) in
                    (new_var :: vars, num + 1))
                 ([],1) 
                 vs
       in
       let tm = match (ctx,
                       map mkVar vs,
                       [(pats, trueTerm, mkSuccess (body_type, body))] : PMRules,
                       makeFail (ctx, body_type, term),
                       mkBreak body_type) 
       in
       let tm = abstract (indices_and_vs, tm, body_type) in
       mkApply (tm,trm)

    %% case e of p -> body --> let p = e in body

    | Apply (Lambda ([(p, Fun (Bool true,_,_), body)],_), e, pos) ->
      eliminateTerm ctx (Let ([(p,e)], body, pos))

    | Apply (                  t1,                   t2, a) -> 
      Apply (eliminateTerm ctx t1, eliminateTerm ctx t2, a)

    | Record (                                              fields, a) ->
      Record (map (fn (id, t) -> (id, eliminateTerm ctx t)) fields, a)

    | Bind (b,                                         vars,                   tm, a) -> 
      Bind (b, map (fn(n,s)-> (n,eliminateType ctx s)) vars, eliminateTerm ctx tm, a)

    | The ((id,                   typ),                   tm, a) -> 
      The ((id, eliminateType ctx typ), eliminateTerm ctx tm, a)

    | LetRec (bindings, body, a) -> 
      LetRec (map (fn ((v, typ), value)->
                     ((v, eliminateType ctx typ),
                      eliminateTerm ctx value)) 
                  bindings,
              eliminateTerm ctx body,
              a)

    | Var ((n,                   s), a) -> 
      Var ((n, eliminateType ctx s), a)

    | Fun (f,                   s, a) -> 
      Fun (f, eliminateType ctx s, a)

    | IfThenElse (s1, s2, s3, a) -> 
      %% this may optimize IfThenElse based on actual terms:
      Utilities.mkIfThenElse (eliminateTerm ctx s1,
                              eliminateTerm ctx s2,
                              eliminateTerm ctx s3)

    | Seq (                        tms, a) -> 
      Seq (map (eliminateTerm ctx) tms, a)

    | And (                  tm :: r_tms, a) -> 
      And (eliminateTerm ctx tm :: r_tms, a)

    | TypedTerm (                  tm,                   ty, a) ->
      TypedTerm (eliminateTerm ctx tm, eliminateType ctx ty, a)

    | _ ->
      term

 op simplifyPatternMatchResult (term : MSTerm) : Option MSTerm =
  let 

    def simpRec (body, continuation) =
      case body of
        | IfThenElse (p, t1, t2, pos) ->
          (case simpSuccess t1 of
             | Some simp_t1 ->
               (case simpRec (t2, continuation) of
                  | Some simp_t2 -> 
                    %% this may optimize IfThenElse based on actual terms:
                    Some (Utilities.mkIfThenElse (p, simp_t1, simp_t2))
                  | _ -> None)
             | _ ->
               if simpleSuccTerm? continuation then
                 case simpRec (t1, continuation) of
                   | Some simp_t1 ->
                     (case simpRec (t2, continuation) of
                        | Some simp_t2 -> 
                          %% this may optimize IfThenElse based on actual terms:
                          Some (Utilities.mkIfThenElse (p, simp_t1, simp_t2))
                        | _ -> None)
                   | _ -> None
               else 
                 None)

        | Fun (Op (Qualified ("TranslationBuiltIn", "mkBreak"),_),_,_) -> 
          simpSuccess continuation

        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkSuccess"),_),_,_), 
                 arg,
                 _) 
          ->
          Some arg   % continuation is unreachable

        | Let (bindings, let_body, pos) ->
          (case simpRec (let_body, continuation) of
             | Some simp_body -> Some (Let (bindings, simp_body, pos))
             | _ -> None)

        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"),_),_,_),
                 Record ([("1", inner_body), ("2", inner_continuation)], _),
                 _) 
          ->
          (case simpRec (inner_continuation, continuation) of
             | Some simp_continuation -> simpRec (inner_body, simpLet simp_continuation)
             | _ -> None)

        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkFail"),_),_,_),_,_) -> 
          Some body

        | _ -> 
          None

    def simpSuccess tm =
      case tm of

        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkSuccess"),_),_,_), tm, _) -> 
          Some tm

        | Let (bindings, body, pos) ->
          (case simpSuccess body of
             | Some simp_body -> Some (Let (bindings, simp_body, pos))
             | _ -> None)

        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"),_),_,_),
                 Record ([("1", body), ("2", continuation)],_),
                 _) 
          ->
          simpRec (body, continuation)
          
        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkFail"),_),_,_), _, _)  ->
          Some tm

        | _ -> 
          None         
  in
  case term of

    | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"),_),_,_),
             Record ([("1", body), ("2", continuation)],_), 
             _)
      ->
      simpRec (body, simpLet continuation)

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

 op mkSpcContext (spc : Spec) (op_name : String) : Context =
  {counter     = Ref 0,
   spc         = spc,
   error_index = Ref 0,   % to distinguish error messages
   op_name     = op_name, % for error messages
   lambda      = None}    % for error messages

 op translateMatchInTerm (spc: Spec) (op_name: String) (tm: MSTerm): MSTerm =
  simpLamBody(eliminateTerm (mkSpcContext spc op_name) tm)

 op SpecTransform.translateMatch (spc : Spec) : Spec = 
  % sjw: Moved (Ref 0) in-line in mkSpcContext so it is reexecuted for each call so the counter is reinitialized
  % for each call. (This was presumably what was intended as otherwise there would be no need for mkContext
  % to be a function). This means that compiled functions will have the same generated variables
  % independent of the rest of the file.
  let 
    def mkContext op_name = mkSpcContext spc op_name
  in
  let new_types =
      mapTypeInfos (fn info ->
                      let Qualified (_,id)      = primaryTypeName      info in
                      let (old_decls, old_defs) = typeInfoDeclsAndDefs info in
                      let new_defs =
                          map (fn dfn ->
                                 let (tvs, typ) = unpackType dfn                   in
                                 let new_type   = eliminateType (mkContext id) typ in
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
