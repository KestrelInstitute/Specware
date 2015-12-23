(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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
 *       Phil Wadler's chapter in Peyton Jones' book
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
 * Note: 
 *
 * This pattern matcher now uses a revised version of Wadler's algorithm, no longer producing forms 
 * containing non-standard forms such as TranslationBuiltIn,mkBreak, since these non-standard forms 
 * complicate further reasoning and transformations within Specware, and also are not easily modeled 
 * in languages such as C which lack a "try/catch" feature.
 *
 * Instead, this pattern matching compiler generates intermediate forms for TranslationBuiltIn,mkBreak
 * just as Wadler does, but then removes them when the nearest containing failWith is processed, 
 * converting breaks into calls to a local continuation function which ecapsulates the "fail" clause 
 * given to failWith.
 *
 *
 * Thie pattern matcher also produces calls to TranslationBuiltIn,mkFail for "fall-through" cases, 
 * and these may persist into the result.
 *)

PatternMatch qualifying spec
 import /Languages/MetaSlang/Transformations/Simplify
 import /Languages/MetaSlang/CodeGen/Generic/ArityNormalize

 type PMRules = List PMRule                    % NOTE: not the same as MSRules (aka Match)
 type PMRule  = MSPatterns * MSTerm * MSTerm   % Note: not the same as MSRule, has list of patterns

 type Context = {counter     : Ref Nat,        % counter for variable numbering
                 spc         : Spec,
                 error_index : Ref Nat,        % to distinguish error messages
                 name        : QualifiedId,    % for error messages -- name of parent op or type
                 lambda      : Option MSTerm,  % for error messages
                 c?          : Bool}

 op mkSpcContext (spc : Spec) (name : QualifiedId) (c? : Bool) : Context =
  {counter     = Ref 0,
   spc         = spc,
   error_index = Ref 0,   % to distinguish error messages
   name        = name,    % for error messages
   lambda      = None,    % for error messages
   c?          = c?}

 op mkBreak (typ : MSType) : MSTerm = 
  mkOp (Qualified ("TranslationBuiltIn", "mkBreak"), typ)

 op isBreak? (trm : MSTerm) : Bool = 
  case trm of
    | Fun (Op (Qualified ("TranslationBuiltIn", "mkBreak"), _), _, _) -> true
    | _ -> false

 op mkFail_q    : Qualifier = "TranslationBuiltIn"  
 op mkFail_id   : Id        = "mkFail"              
 op mkFail_name : OpName    = Qualified (mkFail_q, mkFail_id) 

 op mkFail (ctx : Context, typ : MSType, tm : MSTerm) : MSTerm =
  %% Generate the continuation catch all case given a set of pattern matching rules.
  let index = ! ctx.error_index + 1 in
  (ctx.error_index := index;
   let typ1 = mkArrow (typ, typ) in
   let line_num = begLineNum(termAnn tm) in
   % let _ = if line_num = 0 then writeLine("no annotation: "^printTerm tm) else () in
   % let _ = writeLine("mkfail called with\n"^printTerm tm) in
   let msg  = "ERROR: Nonexhaustive match failure [\#"
             ^ (show index) ^ (if line_num = 0 then "" else " line: "^show(line_num))
             ^ "] in " ^ (printQualifiedId ctx.name)
             ^ "~%~s" in
   mkApply (mkOp (mkFail_name, typ1),
            mkTuple[mkString msg, tm]))

 op isFail? (trm : MSTerm) : Bool = 
  case trm of
    | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkFail"), _), _, _),  _, _) -> true
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

 op emptyPat : MSPattern = mkTuplePat []

 op storeLambda (trm : MSTerm, ctx : Context) : Context =
  %% used just to make msg in warnUnreachable
  ctx << {lambda = Some trm}

 op failWith (ctx : Context) (body : MSTerm) (continuation : MSTerm) : MSTerm =
  let
    def tinyTerm? tm =
      case tm of
        | Var _ -> true
        | Fun _ -> ~ (isBreak? tm)
        | TypedTerm (tm, _, _) -> tinyTerm? tm
        | _ -> false

    def smallArg? tm =
      case tm of
        | Var _ -> true
        | Fun _ -> ~ (isBreak? tm)
        | Record (fields, _) -> forall? (fn (_, tm) -> tinyTerm? tm) fields
        | TypedTerm (tm, _, _) -> smallArg? tm
        | _ -> false

    def smallTerm? tm =
      %% true for terms such as 'nil', 'foo (1,x,bar)', '(a,b,c)' etc.
      %% perhaps could use a more explicit size calculation, but this
      %% is just a heuristic and should avoid the exponential explosion
      %% that could happen when continuations recusively each contain
      %% multiple continuations.
      case tm of
        | Var _ -> true
        | Fun _ -> ~ (isBreak? tm)
        | Record (fields, _) -> forall? (fn (_, tm) -> tinyTerm? tm) fields
        | Apply (Fun (RecordMerge, _, _), Record ([(_,x), (_,y)], _), _) -> tinyTerm? x && smallArg? y
        | Apply (f, arg, _) -> tinyTerm? f && smallArg? arg
        | TypedTerm (tm, _, _) -> smallTerm? tm
        | _ -> false


    def simplifyIfResultIsSmall tm =
      %% The motivation for calling simplify is to allow forms such as
      %% 'let x = y in false' to be recognized as small terms (e.g. 'false') 
      %% and thus avoid producing silly local functions such as
      %% 'def pv7 () = false'.
      %%
      %% But simplify can turn a case into a form such as 'let (x, y) = ...',
      %% and this is problematic since we're supposedly past the point at 
      %% which such complex let's are transformed into cases.
      %% 
      %% Fortunately, we can avoid this problem by simply ignoring any 
      %% simplications that don't succeed in producing a small term.
      let new = simplify ctx.spc tm in
      if smallTerm? new then
        new
      else
        tm

    def possibleVariableCapture? continuation body =

      %% We must not sustitute the continuation term for any break's found 
      %% in the body if that body binds free vars found in the continuation.

      %% This is a conservative test to avoid that situation -- it will 
      %% return true for the problematic situtations, but (rarely) might
      %% also return true for some that would not be problematic.
      
      let free_vars  = freeVars continuation          in
      let free_names = map (fn (v, _) -> v) free_vars in
      existsSubTerm (fn tm ->
                       case tm of

                         | Let (bindings, _, _) -> 
                           exists? (fn (pat, _) -> 
                                      case pat of
                                        | VarPat ((v, _), _) -> v in? free_names
                                        | _ -> false)
                                   bindings

                        | LetRec (bindings, _, _) -> 
                          exists? (fn ((v, _), _) -> v in? free_names)
                                  bindings

                        | _ -> false)
      
                    body

  in
  if isBreak? continuation then 
    body 
  else
    let break_count = 
        foldSubTerms (fn (tm, n) ->
                        if isBreak? tm then
                          n + 1
                        else 
                          n)
                     0 
                     body
    in
    case break_count of

      | 0 -> 
        let continuation = simplifyIfResultIsSmall continuation in
        if isFail? continuation then
          body
        else
          let _ = writeLine ("\nWarning: Redundant case in " ^ (printQualifiedId ctx.name) ^ " :\n\n" ^ 
                               (printTerm continuation) ^ "\n\n  within\n\n" ^
                               (case ctx.lambda of
                                  | Some tm -> printTerm tm
                                  | _ -> "") ^ "\n")
          in
          body

      | 1 -> 
        %% Substitute continuation used once
        mapSubTerms (fn tm -> 
                       if isBreak? tm then
                         continuation
                       else 
                         tm)
                    body
      | _ -> 
        let continuation = simplifyIfResultIsSmall continuation in
        if isBreak? continuation then 
          body 
        else
          %% If the continuation is small and there is no chance of a variable capture, 
          %% directly substitute continuation for each break in body.
          if (smallTerm? continuation) && ~ (possibleVariableCapture? continuation body) then
            mapSubTerms (fn tm -> 
                           if isBreak? tm then
                             continuation
                           else
                             tm)
                        body
          else

            %% For whatever reason, we have decided here to not use direct substitution
            %% of continuation for each break in body.

            %% So make a local function to encapsulate the continuation:

            let result_type      = inferType (ctx.spc, body)                    in
            let continue_fn_type = mkArrow (mkProduct [], result_type)          in
            let continue_fn_var  = freshVar (ctx, continue_fn_type)             in
            let continue_fn_def  = mkLambda (emptyPat, continuation)            in

            %% Then substitute a call to that local function for each break in body:

            let call_continue_fn = mkApply (mkVar continue_fn_var, mkRecord []) in
            let new_body = 
                mapSubTerms (fn tm -> 
                               if isBreak? tm then
                                 call_continue_fn
                               else
                                 tm)
                            body
            in
            mkLetRec ([(continue_fn_var, continue_fn_def)],
                      new_body)

            
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

 type DestructuringRules = List DestructuringRule
 type DestructuringRule  = {query    : MSTerm,       % e.g. embed? Foo x -- tests to see if argument matches constructor
                            new_vars : MSTerms,      % vars that will be bound to args in term, e.g `x' and `y' in  `Foo (x,y)'
                            bindings : MSBindings,   % each binding associates a var with an extractor from the term
                            pattern  : MSPattern,    % original pattern
                            pmrules  : PMRules}

 op substPat (body : MSTerm, pat : MSPattern, value : MSTerm) : MSTerm = 
  case body of
    | Fun (Bool true, _, _) ->
      body
    | _ ->
      case pat of
        | WildPat _ -> body
        | VarPat  _ -> mkLet ([(pat, value)], body)
        | _         -> body (* Should not happen *)
      
 (* 
  *  We generate tester functions for the various constructor formats.
  *)

 op embedded (constructorName : QualifiedId) (trm : MSTerm) : MSTerm = 
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
    | ((QuotientPat   (pat, qid, _,    _))::_, _, _) -> Quotient   (pat, qid)
    | ((RestrictedPat (pat, bool_expr, _))::_, _, _) -> Restricted (pat, bool_expr)
    | _ -> (printPMRule pmrule; fail "Unrecognized ruleType!")

(*
 op myshow? : Bool = false

 op printDRules (msg : String) (drules : DestructuringRules) : () = 
  if myshow? then
    let _ = writeLine msg in
    let _ = writeLine "  =========" in
    let _ = app (fn dr -> printDRule "" dr) drules in
    let _ = writeLine "  =========" in
    ()
  else
    ()

 op printDRule (msg : String) (drule : DestructuringRule) : () = 
  if myshow? then
    let _ = writeLine msg in
    let _ = writeLine "  ----------------------------------------" in
    let _ = writeLine ("  query    = " ^ printTerm drule.query) in
    let _ = writeLine ("  new_vars = " ^ foldl (fn (s, v) -> s ^ ", " ^ printTerm v) "" drule.new_vars) in
    let _ = writeLine ("  bindings = " ^ foldl (fn (s, (p, b)) -> s ^ ", " ^ printPattern p ^ " = " ^ printTerm b) "" drule.bindings) in
    let _ = writeLine ("  pattern  = " ^ printPattern drule.pattern) in
    let _ = printPMRules "  pmrules  =" drule.pmrules in 
    let _ = writeLine "  ----------------------------------------" in
    ()
  else
    ()

 op printPMRules (msg : String) (pmrules : PMRules) : () = 
  if myshow? then
    let _ = writeLine msg in
    let _ = writeLine "  -------" in
    let _ = app printPMRule pmrules in
    let _ = writeLine "  -------" in
    ()
  else
    ()
*)

 op printPMRule (pats : MSPatterns, cond : MSTerm, body : MSTerm) : () =
  let _ = toScreen "  Pattern   : " in
  let _ = app (fn p -> toScreen (printPattern p ^ " ")) pats in
  let _ = writeLine "" in
  let _ = writeLine ("  Condition : " ^ printTerm cond) in
  let _ = writeLine ("  Body      : " ^ printTerm body) in
  let _ = writeLine ("  -------") in
  ()

 op sameConstructor (spc : Spec) (p1 : MSPattern, p2 : MSPattern) : Bool = 
  case (p1, p2) of
    | (RecordPat _,         RecordPat _        ) -> true
    | (EmbedPat (e1,_,_,_), EmbedPat (e2,_,_,_)) -> e1 = e2
    | _ -> equivPattern? spc (p1, p2)
      
 (*
  *  op partitionConstructors : Var * MSRules -> DestructuringRules
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

 op freshVar (ctx : Context, typ : MSType) : MSVar =
  let num = ! ctx.counter + 1 in
  (ctx.counter := num;
   ("pV" ^ (Nat.show num), typ))

 op freshVars (num : Nat, ctx : Context, pat : MSPattern) : List (String * MSVar) =
  case num of
    | 0 -> []
    | 1 -> [("", freshVar (ctx, patternType pat))]
    | _ ->
      case pat of
        | RecordPat (fields,_) -> 
          map (fn (index, pat) -> (index, freshVar (ctx, patternType pat)))
              fields
        | _ -> System.fail "Record pattern expected"

 (* 
  *  Generates the query term used to identify variable being an instance
  *  of the pattern 
  *)

 op queryPat (pattern : MSPattern) (spc: Spec): MSTerm -> MSTerm = 
  case pattern of
    | EmbedPat  (qid,o_p,ty, _) ->
      if constructorOp? spc qid
           || some? o_p                 % Not sure what to do in this case!!
        then embedded qid
        else equalToConstant(ty, mkOp(qid, ty))
    | NatPat    (n,     _) -> equalToConstant (natType,    mkNat    n)
    | CharPat   (c,     _) -> equalToConstant (charType,   mkChar   c)
    | BoolPat   (b,     _) -> equalToConstant (boolType,   mkBool   b)
    | StringPat (s,     _) -> equalToConstant (stringType, mkString s)
    | RecordPat _          -> (fn _ -> trueTerm)
    | _                    -> (fn _ -> trueTerm)

 op coproductFields (spc: Spec, typ: MSType) : List (QualifiedId * Option MSType) = 
  let typ = unfoldBase (spc, typ) in
  case typ of
    | CoProduct (fields, _) -> fields
    | Subtype   (tau, _, _) -> coproductFields (spc, tau)
    | Base (Qualified ("List", "List"), [x], _) -> 
      [(Qualified("List", "Nil"),  None), 
       (Qualified("List", "Cons"), Some (Product ([("1", x), ("2", typ)], 
                                                  typeAnn typ)))]
    | _ -> System.fail ("CoProduct type expected, but got " ^ printType typ)

 op partitionConstructors (ctx     : Context, 
                           trm     : MSTerm, 
                           pmrules : PMRules) 
  : DestructuringRules =
  let
    def patDecompose (pattern : MSPattern) : MSBindings =
      case pattern of

        | RecordPat (fields,_) -> 
          %% Given a record pattern,
          %%  produce a list of pairs of inner field patterns with field acccess functions.
          map (fn (index, pat) -> 
                 (pat, mkProjectTerm (ctx.spc, index, trm))) 
              fields

        | EmbedPat (qid as Qualified(_, id), Some pat, coproduct_type, _) -> 
          %% Given a constructor with a patterned argument,
          %%  produce a singleton list pairing that inner argument pattern with a selection function 
          %%  that assumes the constructor is present in the term surrounding it.
          %% E.g. given Foo (x, y) the pattern will be (x, y) and the extractor will be select[Foo]
          let fields = coproductFields (ctx.spc, coproduct_type) in
          let tm = case findLeftmost (fn (qid2  as Qualified(_, id2), _) -> id = id2) fields of
                     | Some (_, Some field_type) ->
                       mkApply ((Fun (Select qid, 
                                      mkArrow (coproduct_type, field_type), 
                                      noPos)), 
                                trm)
                     | _ -> 
                       System.fail "Selection index not found in product"
          in
          [(pat, tm)]

        | _ -> 
          %% Given a VarPat of a constant pattern (e.g, a constructor with no argument), 
          %%  produce an empty list of no inner patterns to match.
          [] 

    def insert (pmrule, drules) : DestructuringRules = 
      case (pmrule, drules) of

        | ((pat :: pats, cond, body), []) -> 
          %% create new drule:

          let query                = queryPat pat ctx.spc trm in
          let pats_with_extractors = patDecompose pat in 

          %% pats_with_extractors is a list of patterns paired with extraction functions:
          %%   a list of patterns, each paired with a corresponding projection   -- exploded record pattern
          %%   a singleton list of one pattern paired with a selection operation -- exploded embed pattern
          %%   the empty list                                                    -- constant pattern (e.g. Nil or None)

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

          %% new_pats will decribe how to destructure vars within head pattern
          %% e.g., given pattern Foo (x, y, z), new_pats will be [(x, y, z)]
          %% new_vars are useable terms corresponding to those new_pats
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

        | ((pat :: pats, cond, body), (drule :: drules)) -> 
          let spc = ctx.spc in
          if sameConstructor spc (pat, drule.pattern) then
            %% add pattern to existing drule for same constructor
            let pats_with_extractors = patDecompose pat                                 in 
            let new_pats             = map (fn (pat, _) -> pat) pats_with_extractors    in
            let new_pmrule           = (new_pats ++ pats, cond, body)                   in
            let revised_drule        = drule << {pmrules = new_pmrule :: drule.pmrules} in
            let new_drules           = revised_drule :: drules                          in
            new_drules
          else 
            %% TODO: wierdly ineffecient way to amend an element in a list
            %% repeats exists? test for every tail of list
            if exists? (fn drule -> sameConstructor spc (pat, drule.pattern)) drules then
              %% walk past non-matching drule on way to a matching one (that we know exists)
              let new_drules = drule :: insert (pmrule, drules) in
              new_drules
            else 
              %% otherwise create new drule
              let new_drules = insert (pmrule, []) in
              let new_drules = new_drules ++ (drule :: drules) in
              new_drules

        | _ -> drules (* should not happen *)
  in
  foldr insert [] pmrules 
        
 op abstract (vs   : List (String * MSVar), 
              body : MSTerm, 
              typ  : MSType) 
  : MSTerm = 
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
    | [] -> 
      foldr (fn ((_,cond,body), continuation) -> 
               %% this may optimize IfThenElse based on actual terms:
               let body = Utilities.mkIfThenElse (cond, body, break) in
               failWith ctx body continuation)
            continuation
            pmrules
    | _ -> 
      let pmruless = partition pmRuleType pmrules in
      foldr (matchPMRules (ctx, break, vars)) 
            continuation 
            pmruless

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
              vars         : MSTerms, 
              pmrules      : PMRules,
              continuation : MSTerm, 
              break        : MSTerm) 
  : MSTerm = 

  %% this effectively turns something like
  %%
  %%   let (x : Nat, y : Nat) = complex_tm in
  %%   ...
  %%
  %% into something like
  %%
  %%   let (z : Nat * Nat) = complex_tm in
  %%   let x = z.1 in
  %%   let y = z.2 in 
  %%   ...
  %%
  %% var is a variable (z) bound to the structured argument (a record, etc.)
  %% partitionConstructors produces local variables (x,y), each paired with 
  %% an extraction function on the var (z)

  let var :: vars         = vars in  % use var in Let binding, vars in Let body
  let destructuring_rules = partitionConstructors (ctx, var, pmrules) in
  let body                = foldr (fn (drule, continuation) ->   
                                     %% this may optimize IfThenElse based on actual vars:
                                     Utilities.mkIfThenElse (drule.query, 
                                                             mkLet (drule.bindings,
                                                                    match (ctx,
                                                                           drule.new_vars ++ vars,
                                                                           drule.pmrules,
                                                                           break,
                                                                           break)),
                                                             continuation))
                                  break 
                                  destructuring_rules
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
                        | ((RestrictedPat (pat,_,_)) :: pats, cond, body) ->
                          (pat :: pats,
                           mkSimpConj [cond, bool_expr], 
                           body)
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
      let pmrules = map (fn ((QuotientPat (pat, pred, _, _)) :: pats, cond, body) ->
                           (pat :: pats, cond, body))
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
      | RecordPat (fields, _) -> map (fn (_, pat) -> pat) fields
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
      let var          = mkAVar(v, termAnn term)                      in
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
      
    | QuotientPat  (                     p, qid, tys, a) ->
      QuotientPat  (eliminatePattern ctx p, qid, tys, a)
      
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

 op makeContinuation (ctx     : Context, 
                      typ     : MSType, 
                      msrules : MSRules,
                      vs      : List (String * MSVar),
                      term    : MSTerm) 
  : MSRules * MSTerm = 
  let
     def termFrom_vs(vs) =
       case vs of
         | [(_, v)] -> mkAVar (v, termAnn term)
         | _ -> Record (map (fn (index, v) -> (index, mkVar v)) vs, 
                        noPos) 
     def loop (msrules, first_msrules) =
       case msrules of

         | [] -> 
           (reverse first_msrules, mkFail (ctx, typ, termFrom_vs vs))

         | [(WildPat _, Fun (Bool true, _, _), body)] ->
           (reverse first_msrules, body)

         | [(VarPat (v, _), Fun (Bool true, _, _), body)] ->
           let body = mkLet ([(VarPat (v, noPos), termFrom_vs vs)], body) in
           (reverse first_msrules, body)

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
    writeLine ("checkUnreachableCase: Unreachable case in " ^ 
                 (printQualifiedId ctx.name) ^ "\n" ^ 
                 printTerm term)
  else 
    ()

 %%% The last case of a Lambda case has the obligation of always matching, so if it
 %%% is has | (such-that) clause, there is the obligation that it is true

 op alwaysCheckRestrictedPatInLambda? : Bool = false

op almostSimplePattern? (pattern : MSPattern) : Bool = 
 case pattern of
   | VarPat _ -> true
   | RestrictedPat (p, _, _) -> simplePattern? p
   | RecordPat (fields, _) -> forall? (fn (_, p) -> simplePattern? p) fields 
   | _ -> false
 
op mkAVar(v: MSVar, p: Position): MSTerm =
  Var(v, p)

 op eliminateTerm (ctx : Context) (term : MSTerm) : MSTerm =
  case term of
    | Lambda (msrules,_) ->
      let msrules = normalizeSimpleAlias msrules in
      let msrules = map (fn (pat, cond, body)-> 
                         (eliminatePattern ctx pat,
                          eliminateTerm    ctx cond,
                          eliminateTerm    ctx body)) 
                        msrules 
      in
      let arity   = matchArity msrules in
      if simpleAbstraction? msrules then
        let msrules = map (fn (pat, cond, body) -> (deRestrict pat, cond, body)) msrules in
        Lambda (msrules, noPos)
      else 
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
                                              body))
                                          msrules 
        in
        let vars = map (fn (_, v) -> mkAVar(v, termAnn term)) indices_and_vs                   in
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
     if (if ctx.c? then 
             % let _ = writeLine("forall c? : " ^ show ctx.c?) in
             forall? (fn (pat, _)-> almostSimplePattern? pat) bindings
           else
             forall? (fn (pat, _)-> simplePattern? pat) bindings)
       then
         mkLet (bindings, body)
     else 
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
       let pmrules = [(pats, trueTerm, body)] in
       let body = match (ctx,
                         map mkVar vs,
                         pmrules,
                         mkFail (ctx, body_type, trm),
                         mkBreak body_type) 
       in
       let pat = case indices_and_vs of 
                   | [(_,v)] -> mkVarPat v
                   | _ -> RecordPat (map (fn (index, v)-> 
                                            (index, mkVarPat v)) 
                                         indices_and_vs, 
                                     noPos)
       in
       Let ([(pat, trm)], body, noPos)

    | Apply (Lambda ([(pat, Fun (Bool true,_,_), body)],_), arg, pos) ->
      %% case arg of pat -> body --> let pat = arg in body
      eliminateTerm ctx (Let ([(pat, arg)], body, pos))

    | Apply (f, arg, pos) ->
      let f   = eliminateTerm ctx f   in
      let arg = eliminateTerm ctx arg in
      (case f of
         | Lambda ([(pat, Fun (Bool true,_,_), body)],_) ->
           %% case arg of pat -> body --> let pat = arg in body
           eliminateTerm ctx (Let ([(pat, arg)], body, pos))
         | _ ->
           Apply (f, arg, pos))

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

 op betaReduceLambdaBody (term : MSTerm) : MSTerm =
  case term of
    | Lambda ([(pat, c,  Apply (Lambda ([(VarPat (v,_), _, body)], _), wVar as Var _, _))],  pos) ->
      Lambda ([(pat, c,  substitute (body, [(v, wVar)]))],                                   pos)
    | _ -> term

 op translateMatchInTerm (spc : Spec) (name : QualifiedId) (term : MSTerm): MSTerm =
  betaReduceLambdaBody (eliminateTerm (mkSpcContext spc name false) term)

 op SpecTransform.translateMatch (spc : Spec, c? : Bool) : Spec = 
  % sjw: Moved (Ref 0) in-line in mkSpcContext so it is reexecuted for each call so the counter is reinitialized
  % for each call. (This was presumably what was intended as otherwise there would be no need for mkContext
  % to be a function). This means that compiled functions will have the same generated variables
  % independent of the rest of the file.
  % let _ = writeLine("c? : " ^ show c?) in
  let 
    def mkContext name = mkSpcContext spc name c?
  in
  let new_types =
      mapTypeInfos (fn info ->
                      let type_name             = primaryTypeName      info in
                      let (old_decls, old_defs) = typeInfoDeclsAndDefs info in
                      let new_defs =
                          map (fn dfn ->
                                 let (tvs, typ) = unpackType dfn                          in
                                 let new_type   = eliminateType (mkContext type_name) typ in
                                 maybePiType (tvs, new_type))
                              old_defs
                      in
                      let new_dfn = maybeAndType (old_decls ++ new_defs, typeAnn info.dfn) in
                      info << {dfn = new_dfn}) 
                   spc.types
  in
  let new_ops =
      mapOpInfos (fn info ->
                    let op_name               = primaryOpName      info in
                    let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                    let new_defs = 
                        map (fn dfn ->
                               let (tvs, typ, term) = unpackFirstTerm dfn in
                               if anyTerm? term then 
                                 dfn
                               else
                                 let new_typ = eliminateType (mkContext op_name) typ in
                                 let new_tm  = eliminateTerm (mkContext op_name) term in
                                 let new_tm = betaReduceLambdaBody new_tm in
                                 maybePiTerm (tvs, TypedTerm (new_tm, new_typ, termAnn term)))
                            old_defs
                    in
                    let new_dfn = maybeAndTerm (old_decls ++ new_defs, termAnn info.dfn) in
                    info << {dfn = new_dfn})
                 spc.ops
  in
  let mkfail_info = 
      let string_ref = Base (mkQualifiedId ("String", "String"), [], noPos) in
      let tv         = "a"                                                  in
      let dfn        = Pi ([tv], 
                           TypedTerm (Any noPos, 
                                      Arrow (string_ref, TyVar (tv, noPos), noPos),
                                      noPos),
                           noPos) 
      in
      {names           = [mkFail_name], 
       fixity          = Nonfix,
       dfn             = dfn,
       fullyQualified? = true} 
  in
  let new_ops = insertAQualifierMap (new_ops, mkFail_q, mkFail_id, mkfail_info) in
  let new_elements =
      map (fn el ->
             case el of
               | Property (pt, pname, tyvars,                                 term, a) -> 
                 Property (pt, pname, tyvars, eliminateTerm (mkContext pname) term, a)
               | _ -> el) 
          spc.elements
  in
  let mkfail_op_decl = Op (mkFail_name, false, noPos)  in
  let new_elements   = mkfail_op_decl |> new_elements in
  spc << {types    = new_types,
          ops      = new_ops, 
          elements = new_elements}

end-spec
