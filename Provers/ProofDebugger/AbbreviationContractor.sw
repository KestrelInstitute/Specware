(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ProofDebugger qualifying
spec

  % API private default

  import ExtendedTypesAndExpressions

  (* This spec defines ops to "reverse" the abbreviation expansions defined in
  the proof checker. The ops defined in this spec map types and expressions of
  (meta) types Type and Expression to extended types and expressions of (meta)
  types ExtType and ExtExpression, attempting to replace the types and
  expressions that result from epanding abbreviations with the abbreviations
  themselves, which are first-class extended types and expressions.

  Suppose that we start with an extended type or expression that only contains
  user fields and variables (i.e. no prod fields or abbr variables). Suppose
  that we expand all its abbreviations, obtaining a non-extended type or
  expression (this process is not explicitly defined in this or other specs,
  but could be defined). Then, the ops defined in this spec can almost exactly
  reconstruct the starting extended type or expression. The reason is that the
  (only) type abbreviation expansion contains prod fields and that most
  expression abbreviation expansions contain abbr variables, whose presence
  indicates that a type or expression containing abbr variables is the result
  of expanding an abbreviation and has not been directly provided by the
  user. The cases in which the reconstruction may not be perfect are pointed
  out later in this spec; as we will see, those cases are rather unimportant
  from a practical point of view.

  As mentioned in spec ExtendedTypesAndExpressions, the reason to not use
  extended types and expressions directly in the proof checker is to keep the
  proof checker smaller and simpler. The abbreviation contraction ops defined
  in this spec serve to print out types and expressions in a more readable
  manner for the user. However, the correctness of the proof checker itself
  does not depend on the ops defined in this spec. *)

  (* First of all, we define (mutually recursive) ops to embed non-extended
  types and expressions into extended types and expressions. This is the first
  step in our abbreviation contraction process; the rest operates entirely
  within extended types and expressions. *)

  op embedExtType : Type       -> ExtType
  op embedExtExpr : Expression -> ExtExpression

  def embedExtType = fn
    | BOOL          -> BOOL
    | VAR tv        -> VAR tv
    | TYPE(tn,tS)   -> TYPE (tn, map embedExtType tS)
    | ARROW(t1,t2)  -> ARROW (embedExtType t1, embedExtType t2)
    | RECORD(fS,tS) -> RECORD (fS, map embedExtType tS)
    | RESTR(t,r)    -> RESTR (embedExtType t, embedExtExpr r)

  def embedExtExpr = fn
    | VAR v        -> VAR v
    | OPI(o,tS)    -> OPI (o, map embedExtType tS)
    | APPLY(e1,e2) -> APPLY (embedExtExpr e1, embedExtExpr e2)
    | FN(v,t,e)    -> FN (v, embedExtType t, embedExtExpr e)
    | EQ(e1,e2)    -> EQ (embedExtExpr e1, embedExtExpr e2)
    | IF(e0,e1,e2) -> IF (embedExtExpr e0, embedExtExpr e1, embedExtExpr e2)
    | IOTA t       -> IOTA (embedExtType t)
    | PROJECT(t,f) -> PROJECT (embedExtType t, f)

  (* There is only one type abbreviation, the one for product types. The
  following ops reconstruct product types, by replacing record types whose
  fields are prod fields with product types. The ops are recursively applied
  to types and expressions in a bottom-up fashion. *)

  op contractProductsInType : ExtType       -> ExtType
  op contractProductsInExpr : ExtExpression -> ExtExpression

  def contractProductsInType = fn
    | TYPE(tn,tS)   -> TYPE (tn, map contractProductsInType tS)
    | ARROW(t1,t2)  -> ARROW (contractProductsInType t1,
                              contractProductsInType t2)
    | RECORD(fS,tS) -> let tS1 = map contractProductsInType tS in
                       if fS = firstNProductFields (length tS) then
                         PRODUCT tS1
                       else RECORD (fS, tS1)
    | RESTR(t,r)    -> RESTR (contractProductsInType t,
                              contractProductsInExpr r)
    | t             -> t

  def contractProductsInExpr = fn
    | OPI(o,tS)    -> OPI (o, map contractProductsInType tS)
    | APPLY(e1,e2) -> APPLY (contractProductsInExpr e1,
                             contractProductsInExpr e2)
    | FN(v,t,e)    -> FN (v, contractProductsInType t,
                             contractProductsInExpr e)
    | EQ(e1,e2)    -> EQ (contractProductsInExpr e1,
                          contractProductsInExpr e2)
    | IF(e0,e1,e2) -> IF (contractProductsInExpr e0,
                          contractProductsInExpr e1,
                          contractProductsInExpr e2)
    | IOTA t       -> IOTA (contractProductsInType t)
    | PROJECT(t,f) -> PROJECT (contractProductsInType t, f)
    | e            -> e

  (* Since there are many expression abbreviations, we define generic ops to
  contract expression abbreviations in types, expressions, and also binding
  branches.

  These ops are parameterized over a function over expressions, meant to
  capture the contraction of an abbreviation. The type Contraction defined
  below contains all possible functions between expressions, not just
  contractions. However, only contractions will be used in this spec.

  The three ops defined below process a type, expression, or binding branch by
  first recursively processing its constituent types, expressions, and binding
  branches and then, in the case of an expression, by applying the contraction
  to the expression. The contractions defined in this spec are such that they
  leave the expression unchanged if it is not recognized as the expansion of
  some abbreviation. *)

  type Contraction = ExtExpression -> ExtExpression

  op contractType   : Contraction -> ExtType          -> ExtType
  op contractExpr   : Contraction -> ExtExpression    -> ExtExpression
  op contractBranch : Contraction -> ExtBindingBranch -> ExtBindingBranch

  def contractType contr t =
    let contrType = contractType contr in  % these make the rest of the
    let contrExpr = contractExpr contr in  % op's def more readable
    % recursively process constituent types and expressions:
    case t of
    | BOOL          -> BOOL
    | VAR tv        -> VAR tv
    | TYPE(tn,tS)   -> TYPE (tn, map contrType tS)
    | ARROW(t1,t2)  -> ARROW (contrType t1, contrType t2)
    | RECORD(fS,tS) -> RECORD (fS, map contrType tS)
    | RESTR(t,r)    -> RESTR (contrType t, contrExpr r)
    | PRODUCT tS    -> PRODUCT (map contrType tS)

  def contractExpr contr e =
    let contrType = contractType contr in  % these make the rest of the
    let contrExpr = contractExpr contr in  % op's def more readable
    % recursively process constitent types, expressions, and binding branches:
    let e:ExtExpression = case e of
    | VAR v          -> VAR v
    | OPI(o,tS)      -> OPI (o, map contrType tS)
    | APPLY(e1,e2)   -> APPLY (contrExpr e1, contrExpr e2)
    | FN(v,t,e)      -> FN (v, contrType t, contrExpr e)
    | EQ(e1,e2)      -> EQ (contrExpr e1, contrExpr e2)
    | IF(e0,e1,e2)   -> IF (contrExpr e0, contrExpr e1, contrExpr e2)
    | IOTA t         -> IOTA (contrType t)
    | PROJECT(t,f)   -> PROJECT (contrType t, f)
    | TRUE           -> TRUE
    | FALSE          -> FALSE
    | NOT            -> NOT
    | NEG e          -> NEG (contrExpr e)
    | AND    (e1,e2) -> AND     (contrExpr e1, contrExpr e2)
    | OR     (e1,e2) -> OR      (contrExpr e1, contrExpr e2)
    | IMPLIES(e1,e2) -> IMPLIES (contrExpr e1, contrExpr e2)
    | IFF            -> IFF
    | EQV    (e1,e2) -> EQV     (contrExpr e1, contrExpr e2)
    | NEQ    (e1,e2) -> NEQ     (contrExpr e1, contrExpr e2)
    | THE(v,t,e)     -> THE (v, contrType t, contrExpr e)
    | FAq t          -> FAq  (contrType t)
    | FA(v,t,e)      -> FA   (v, contrType t, contrExpr e)
    | FAA(vS,tS,e)   -> FAA  (vS, map contrType tS, contrExpr e)
    | EXq t          -> EXq  (contrType t)
    | EX(v,t,e)      -> EX   (v, contrType t, contrExpr e)
    | EXX(vS,tS,e)   -> EXX  (vS, map contrType tS, contrExpr e)
    | EX1q t         -> EX1q (contrType t)
    | EX1(v,t,e)     -> EX1  (v, contrType t, contrExpr e)
    | DOT(e,t,f)     -> DOT (contrExpr e, contrType t, f)
    | RECC(fS,tS)    -> RECC (fS, map contrType tS)
    | REC(fS,tS,eS)  -> REC  (fS, map contrType tS, map contrExpr eS)
    | TUPLE(tS,eS)   -> TUPLE (map contrType tS, map contrExpr eS)
    | RECUPDATER(fS,tS,fS1,tS1,fS2,tS2) ->
      RECUPDATER
        (fS,  map contrType tS, fS1, map contrType tS1, fS2, map contrType tS2)
    | RECUPDATE(fS,tS,fS1,tS1,fS2,tS2,e1,e2) ->
      RECUPDATE
        (fS,  map contrType tS, fS1, map contrType tS1, fS2, map contrType tS2,
         contrExpr e1, contrExpr e2)
    | COND(t,brS)            -> COND (contrType t,
                                            map (contractBranch contr) brS)
    | CASE(t,t1,e,brS)       -> CASE (contrType t,
                                            contrType t1,
                                            contrExpr e,
                                            map (contractBranch contr) brS)
    | LET(t,t1,vS,tS,p,e,e1) -> LET (contrType t, contrType t1, vS,
                                           map contrType tS, contrExpr p,
                                           contrExpr e, contrExpr e1)
    | LETSIMP(t1,v,t,e,e1)   -> LETSIMP (t1, v, contrType t,
                                               contrExpr e, contrExpr e1)
    | LETDEF(t,vS,tS,eS,e)   -> LETDEF (contrType t, vS, map contrType tS,
                                              map contrExpr eS, contrExpr e)
    % apply contraction:
    in contr e

  def contractBranch contr (vS,tS,e1,e2) =
    % recursively process constituent types and expressions:
    (vS, map (contractType contr) tS,
     contractExpr contr e1, contractExpr contr e2)

  (* We define one contraction for each expression abbreviation. The
  definitions are derived by "reversing" the abbreviation definitions in the
  proof checker. The contractions are mostly straightforward, but some
  specific comments are given for some of them.

  Each contraction assumes that the previous contractions have already been
  applied. So, for instance, the contraction of FALSE can assume that TRUE has
  already been contracted.

  As mentioned earlier, our contraction process can almost always reconstruct
  an (extended) expression that does not contain abbr variables, after all
  abbreviations have been expanded. The exceptions are due to the
  abbreviations that do not involve abbr variables. One such example is the
  expansion of NEG(e) into APPLY(NOT,e). Our contraction process always
  contracts APPLY(NOT,e) into NEG(e), even if the starting point, before
  expanding abbreviations, was APPLY(NOT,e). Another example if the expansion
  of AND(e1,e2) into IF(e1,e2,FALSE).

  This is not a big problem in practice, because the purpose of the
  contraction process is just to support more readable printing of types and
  expressions. From this perspective, NEG(e) and APPLY(NOT,e) are equivalent,
  and would probably be printed as the exact same strings anyhow. The case of
  AND(e1,e2) vs. IF(e1,e2,FALSE) is a little more significant, but it should
  be relatively rare for users to explicitly write IF(e1,e2,FALSE). *)

  op contractTrue : Contraction
  def contractTrue e =
    let x:Variable = abbr 0 in
    if e = EQ (FN (x, BOOL, VAR x), FN (x, BOOL, VAR x))
    then TRUE else e

  op contractFalse : Contraction
  def contractFalse e =
    let x:Variable = abbr 0 in
    if e = EQ (FN (x, BOOL, VAR x), FN (x, BOOL, TRUE))
    then FALSE else e

  op contractNot : Contraction
  def contractNot e =
    let x:Variable = abbr 0 in
    if e = FN (x, BOOL, IF (VAR x, FALSE, TRUE))
    then NOT else e

  op contractNegation : Contraction
  def contractNegation = fn
    | APPLY (NOT, e0) -> NEG e0
    | e -> e

  op contractConjunction : Contraction
  def contractConjunction = fn
    | IF (e1, e2, FALSE) -> AND (e1, e2)
    | e -> e

  op contractDisjunction : Contraction
  def contractDisjunction = fn
    | IF (e1, TRUE, e2) -> OR (e1, e2)
    | e -> e

  op contractImplication : Contraction
  def contractImplication = fn
    | IF (e1, e2, TRUE) -> IMPLIES (e1, e2)
    | e -> e

  op contractIff : Contraction
  def contractIff e =
    let x:Variable = abbr 0 in
    let y:Variable = abbr 1 in
    if e = FN (x, BOOL, FN (y, BOOL, EQ (VAR x, VAR y)))
    then IFF else e

  op contractEquivalence : Contraction
  def contractEquivalence = fn
    | APPLY (APPLY (IFF, e1), e2) -> EQV (e1, e2)
    | e -> e

  op contractNonEquality : Contraction
  def contractNonEquality = fn
    | NEG (EQ (e1, e2)) -> NEQ (e1, e2)
    | e -> e

  op contractDescription : Contraction
  def contractDescription = fn
    | e as APPLY (IOTA t, FN (v, mustBe_t, e0)) ->
      if mustBe_t = t then THE (v, t, e0)
      else e
    | e -> e

  op contractUniversalQuantifier : Contraction
  def  contractUniversalQuantifier = fn
    | e as FN (abbr 0,
               ARROW (t, BOOL),
               EQ (VAR (abbr 0), FN (abbr 1, mustBe_t, TRUE))) ->
      if mustBe_t = t then FAq t
      else e
    | e -> e

  op contractUniversalQuantification : Contraction
  def contractUniversalQuantification = fn
    | e as APPLY (FAq t, FN (v, mustBe_t, e0)) ->
      if mustBe_t = t then FA (v, t, e0)
      else e
    | e -> e

  op contractMultiUniversalQuantification : Contraction
  (* One might expect this op to be defined recursively, collecting all nested
  FA's (if any) and merging them into one FAA (if there are at least 2
  FA's). However, this op is used by op contractExpr, which already
  recursively processes subexpressions. So, this op can expect nested FA's to
  have been already contracted into an FAA. *)
  def contractMultiUniversalQuantification = fn
    | FA (v1, t1, FA (v2, t2, e)) ->
      FAA (single v1 <| v2, single t1 <| t2, e)
    | FA (v, t, FAA (vS, tS, e)) ->
      FAA (v |> vS, t |> tS, e)
    | e -> e

  op contractExistentialQuantifier : Contraction
  def  contractExistentialQuantifier = fn
    | e as FN (abbr 0,
               ARROW (t, BOOL),
               NEG (FA (abbr 1, mustBe_t,
                    NEG (APPLY (VAR (abbr 0), VAR (abbr 1)))))) ->
      if mustBe_t = t then EXq t
      else e
    | e -> e

  op contractExistentialQuantification : Contraction
  def contractExistentialQuantification = fn
    | e as APPLY (EXq t, FN (v, mustBe_t, e0)) ->
      if mustBe_t = t then EX (v, t, e0)
      else e
    | e -> e

  op contractMultiExistentialQuantification : Contraction
  % a comment similar to op contractMultiUniversalQuantification applies here
  def contractMultiExistentialQuantification = fn
    | EX (v1, t1, EX (v2, t2, e)) ->
      EXX (single v1 <| v2, single t1 <| t2, e)
    | EX (v, t, EXX (vS, tS, e)) ->
      EXX (v |> vS, t |> tS, e)
    | e -> e

  op contractUniqueExistentialQuantifier : Contraction
  def  contractUniqueExistentialQuantifier = fn
    | e as FN (abbr 0,
               ARROW (t, BOOL),
               EX (abbr 1, mustBe_t,
                   AND (APPLY (VAR (abbr 0), VAR (abbr 1)),
                        FA (abbr 2, mustAlsoBe_t,
                            IMPLIES (APPLY (VAR (abbr 0), VAR (abbr 2)),
                                     EQ (VAR (abbr 2), VAR (abbr 1))))))) ->
      if mustBe_t = t && mustAlsoBe_t = t then EX1q t
      else e
    | e -> e

  op contractUniqueExistentialQuantification : Contraction
  def contractUniqueExistentialQuantification = fn
    | e as APPLY (EX1q t, FN (v, mustBe_t, e0)) ->
      if mustBe_t = t then EX1 (v, t, e0)
      else e
    | e -> e

  op contractDottedProjection : Contraction
  def contractDottedProjection = fn
    | APPLY (PROJECT (t, f), e) -> DOT (e, t, f)
    | e -> e

  op contractRecordConstructor : Contraction
  def contractRecordConstructor e =
    (* A record constructor consists of n >= 0 nested abstractions, whose
    bound variables are (abbr 0) to (abbr (n-1)). The following function
    traverses the abstractions, checking that the bound variables are the
    expected ones and collecting the types of the bound variables along the
    way. The traversal stops when a non-abstraction or an abstraction with the
    wrong bound variables is found, returning the types collected along the
    way as well as the body of the last traversed abstraction. *)
    let def processAbstractions (outTS:ExtTypes,   % accumulator
                                 abbVarIndex:Nat,  % current abbr variable index
                                 e:ExtExpression)  % current expression
                               : ExtTypes *        % collected types
                                 ExtExpression =   % body of last FN
      case e of
        | FN (abbr mustBe_abbVarIndex, t, e0) ->
          if mustBe_abbVarIndex = abbVarIndex then
            processAbstractions (outTS <| t, abbVarIndex + 1, e0)
          else (outTS, e)
        | _ ->  (outTS, e)
    in
    let def ANDn (eS:ExtExpressions) : ExtExpression =
      if eS = empty then TRUE
      else if ofLength? 1 eS then theElement eS
      else  AND (head eS, ANDn (tail eS))
    in
    % traverse nested abstractions:
    let (tS, body) = processAbstractions (empty, 0, e) in
    let n = length tS in
    % check whether the body is the expected one:
    case body of
      | THE (abbr mustBe_n, RECORD (fS, mustBe_tS), descBody) ->
        if mustBe_n = n && mustBe_tS = tS then
          let eS:ExtExpressions =
              list (fn(i:Nat) ->
                if i < n then
                  Some (EQ (DOT (VAR (abbr n), RECORD (fS,tS), fS@i),
                            VAR (abbr i)))
                else None) in
          if descBody = ANDn eS then
            RECC (fS, tS)
          else e
        else e
      % since when we attempt this contraction we have already contracted
      % product types, we must explicitly deal with product types here:
      | THE (abbr mustBe_n, PRODUCT mustBe_tS, descBody) ->
        if mustBe_n = n && mustBe_tS = tS then
          let eS:ExtExpressions =
              list (fn(i:Nat) ->
                if i < n then
                  Some (EQ (DOT (VAR (abbr n),
                                       PRODUCT tS,
                                       prod (i+1)),
                            VAR (abbr i)))
                else None) in
          if descBody = ANDn eS then
            RECC (firstNProductFields (length tS), tS)
          else e
        else e
      | _ -> e

  op contractRecord : Contraction
  def contractRecord e =
    (* A record consists of n >= 0 nested applications of a record constructor
    to n arguments. There are n+1 expressions that comprise the nested
    applications (the record constructor plus the n arguments for the
    components). The following function transforms nested applications
    consisting of one or more expressions into the sequence of those
    expressions (a nested application of one expression is just that one
    expression). *)
    let def processApplications (outES:ExtExpressions,  % accumulator
                                 e:ExtExpression)       % current expression
                                : ExtExpressions =      % constituents of the
      case e of                                         % nested applications
        | APPLY (fun, arg) -> processApplications (arg |> outES, fun)
          % we are decomposing APPLY(...APPLY(APPLY(e0,e1),e2)...,en)
        | _ -> e |> outES
    in
    % gather constituents of nested applications:
    let eS = processApplications (empty, e) in
    % check whether first constituent is a record constructor:
    case head eS of  % result of function processApplications is never empty
      | RECC (fS, tS) ->
        (* Remember that we process expressions bottom-up, processing
        subexpressions before their containing expressions. Without the test
        in the following if-then-else, applying processApplications to the
        record constructor alone (which is processed its application to the
        expression for the first record component) would yield a singleton
        sequence consisting of the record constructor, and we would return REC
        (fS, tS, empty), which is not what we want. The test of the if delays
        the contraction until we are processing the right (outermost)
        application. *)
        if length (tail eS) = length fS then
          REC (fS, tS, tail eS)
        else e
      | _ -> e

  op contractTuple : Contraction
  def contractTuple = fn
    | e as REC (fS, tS, eS) ->
      if fS = firstNProductFields (length fS)
      then TUPLE (tS, eS) else e
    | e -> e

  op contractRecordUpdater : Contraction
  def contractRecordUpdater = fn
    | e as FN (abbr 0, RECORD (fS_fS1, tS_tS1),
           FN (abbr 1, RECORD (fS_fS2, tS_tS2),
           REC (fS_fS1_fS2, tS_tS1_tS2, eS))) ->
      let fS = longestCommonPrefix (fS_fS1, fS_fS2) in
      let n = length fS in
      let fS1 = removePrefix (fS_fS1, n) in
      let fS2 = removePrefix (fS_fS2, n) in
      let n1 = length fS1 in
      let n2 = length fS2 in
      let t1 = RECORD (fS_fS1, tS_tS1) in
      let t2 = RECORD (fS_fS2, tS_tS2) in
      let tS = longestCommonPrefix (tS_tS1, tS_tS2) in
      let tS1 = removePrefix (tS_tS1, length tS) in
      let tS2 = removePrefix (tS_tS2, length tS) in
      if eS = list (fn(i:Nat) ->
                if i < n then
                  Some (DOT (VAR (abbr 1), t2, fS@i))
                else if i < n+n1 then
                  Some (DOT (VAR (abbr 0), t1, fS1@(i-n)))
                else if i < n+n1+n2 then
                  Some (DOT (VAR (abbr 1), t2, fS2@(i-n-n1)))
                else None) &&
         fS_fS1_fS2 = fS ++ fS1 ++ fS2 &&
         tS_tS1_tS2 = tS ++ tS1 ++ tS2 then
        RECUPDATER (fS, tS, fS1, tS1, fS2, tS2)
      else e
    | e -> e

  op contractRecordUpdate : Contraction
  def contractRecordUpdate = fn
    | APPLY (APPLY (RECUPDATER (fS, tS, fS1, tS1, fS2, tS2), e1), e2) ->
      RECUPDATE (fS, tS, fS1, tS1, fS2, tS2, e1, e2)
    | e -> e

  op contractBindingConditional : Contraction
  def contractBindingConditional e =
    (* Any expression can be reduced to an EXX expression. This is witnessed
    by the following function, which returns the constituents of the EXX that
    the expression is reduced to. *)
    let def viewAsEXX (e:ExtExpression) : Variables * ExtTypes * ExtExpression =
      case e of
        % no change if already EXX:
        | EXX (vS, tS, e) -> (vS, tS, e)
        % singleton EXX if EX:
        | EX (v, t, e) -> (single v, single t, e)
        % empty EXX if other expression:
        | e -> (empty, empty, e)
    in
    (* The following function checks whether an expression has the form of a
    branch result expression of a binding conditional, i.e. THE (x, t, EXX
    (vS, tS, b &&& VAR x == e)), where x is abbr i for some i (we do not check
    the exact value of i, which will always be correct if we contract
    expressions obtained by expanding user-provided expressions that do not
    contain abbr variables). If the check succeeds, the function returns t,
    vS, tS, b, and e. An Option type is used to model failure. *)
    let def processBranchResult (e:ExtExpression)
                                : Option (ExtType * Variables * ExtTypes *
                                          ExtExpression * ExtExpression) =
      case e of
        | THE (abbr i, t, body) ->
          (case viewAsEXX body of
            | (vS, tS, AND (b, EQ (VAR (abbr mustBe_i), e0))) ->
              if mustBe_i = i then Some (t, vS, tS, b, e0)
              else None
            | _ -> None)
        | _ -> None
    in
    (* Recall that, as remarked in the comment in the definition of op
    contractMultiUniversalQuantification, ops contractType and contractExpr
    already perform recursion. So, when traversing the nested IF's that
    comprise a COND, we can expect the else branch of each IF to have been
    already contracted into a COND. *)
    case e of
      | IF (ifTest, ifThen, COND (t, brS)) ->
        (case processBranchResult ifThen of
          | Some (mustBe_t, vS, tS, b, e0) ->
            let (mustBe_vS, mustBe_tS, mustBe_b) = viewAsEXX ifTest in 
            if mustBe_vS = vS && mustBe_tS = tS &&
               mustBe_b = b && mustBe_t = t then
              COND (t, (vS, tS, b, e0) |> brS)
            else e
          | None -> e)
      | _ ->
        (case processBranchResult e of
          | Some (t, vS, tS, b, e0) -> COND (t, single (vS, tS, b, e0))
          | None -> e)

  op contractCaseFromCond : Contraction
  def contractCaseFromCond e =
    (* The following function performs the inverse transformation on binding
    branches of the transformation operated in the definition of the CASE
    abbreviation in the proof checker. We define it on sequences of binding
    branches, as opposed to single binding branches, because this inverse
    transformation may fail (if the binding branch does not have the expected
    form); failure is modeled via Option. *)
    let def transformBranches
            (outBrS: ExtBindingBranches,  % accumulator
             inBrS : ExtBindingBranches,  % branches to transform
             eS    : ExtExpressions)      % target expressions found in branches
            : Option (ExtBindingBranches  % transformed branches
                    * ExtExpressions) =   % target expressions found in branches
      if empty? inBrS then Some (outBrS, eS)
      else
        case head inBrS of
          | (vS, tS, EQ (e, p), r) ->
            (* We need to check that no free variable of e is bound in the
            binding branch. Without this check, we could end up contracting
            COND's whose condition happens to be an equality into a CASE, even
            if the left-hand side happens to contain variables among vS, which
            would yield a non-equivalent expression. *)
            if toSet vS /\ exprFreeVars e = empty then
              transformBranches (outBrS <| (vS, tS, p, r), tail inBrS, eS <| e)
            else None
          | _ -> None
    in
    case e of
      | COND (t1, brS) ->
        (case transformBranches (empty, brS, empty) of
          | Some (brS, eS) ->
            if allEqualElements? eS && nonEmpty? eS then
              (* Note that we cannot determine the first type t for CASE from
              the expansion to COND (it can only be determined from the
              expansion to nested CASE's, cf. LD). We arbitrarily pick type
              BOOL, assuming that the type will not be printed anyhow. *)
              CASE (BOOL, t1, head eS (* = any element of eS *), brS)
            else e
          | None -> e)
      | e -> e

  op contractCaseFromNestedCases : Contraction
  def contractCaseFromNestedCases e =
    case e of
      | CASE (BOOL, t1, e0, brS) ->
              % previous op assigns BOOL as target type to CASE
        if ofLength? 1 brS then
          let (vS, tS, p, r) = theElement brS in
          if ofLength? 1 vS && ofLength? 1 tS then
            let v = theElement vS in
            let t = theElement tS in
            case (v, p, r) of
              | (abbr _, VAR mustBe_v,  % we do not check the indices of abbr
                 CASE (BOOL, mustBe_t1, VAR mustAlsoBe_v, brS)) ->
                       % previous op assigns BOOL as target type to CASE
                if mustBe_v = v && mustAlsoBe_v = v && mustBe_t1 = t1 then
                  CASE (t, t1, e0, brS)
                              % we restore the correct target type t
                else e
              | _ -> e
          else e
        else e
      | e -> e

  op contractNonRecursiveLet : Contraction
  def contractNonRecursiveLet = fn
    | e as CASE (t, t1, e0, brS) ->
      if ofLength? 1 brS then
        let (vS, tS, p, e1) = theElement brS in
        LET (t, t1, vS, tS, p, e0, e1)
      else e
    | e -> e

  op contractSimpleLet : Contraction
  def contractSimpleLet = fn
    | e as LET (t, t1, vS, mustBe_single_t, mustBe_VAR_v, e0, e1) ->
      if ofLength? 1 vS && mustBe_VAR_v = VAR (theElement vS) &&
         mustBe_single_t = single t then
        LETSIMP (t1, theElement vS, t, e0, e1)
      else e
    | e -> e

  op contractRecursiveLet : Contraction
  def contractRecursiveLet = fn
    | e as LET (PRODUCT tS, t,
                vS, mustBe_tS,
                mustBe_tupleVS,
                COND (PRODUCT mustAlsoBe_tS, brS), e0) ->
      if mustBe_tS = tS &&
         mustAlsoBe_tS = tS &&
         mustBe_tupleVS = TUPLE (tS, map VAR vS) &&
         ofLength? 1 brS then
        let (mustBe_vS,
             mustBe_tS,
             mustBe_tupleVS_eq_tupleES,
             mustBe_tupleVS) = theElement brS in
          case mustBe_tupleVS_eq_tupleES of
            | EQ (mustAlsoBe_tupleVS, TUPLE (mustAlsoBe_tS, eS)) ->
              if mustBe_vS = vS &&
                 mustBe_tS = tS &&
                 mustAlsoBe_tS = tS &&
                 mustBe_tupleVS = TUPLE (tS, map VAR vS) &&
                 mustAlsoBe_tupleVS = TUPLE (tS, map VAR vS) then
                LETDEF (t, vS, tS, eS, e0)
              else e
            | _ -> e
      else e
    | e -> e

  (* The following two ops contract all abbreviations in types and
  expressions. (The contractions appear in reversed order because prefix
  function application takes place right-to-left. *)

  % API public
  op contractTypeAll : Type -> ExtType
  def contractTypeAll t =
    (contractType contractRecursiveLet
    (contractType contractSimpleLet
    (contractType contractNonRecursiveLet
    (contractType contractCaseFromNestedCases
    (contractType contractCaseFromCond
    (contractType contractBindingConditional
    (contractType contractRecordUpdate
    (contractType contractRecordUpdater
    (contractType contractTuple
    (contractType contractRecord
    (contractType contractRecordConstructor
    (contractType contractDottedProjection
    (contractType contractUniqueExistentialQuantification
    (contractType contractUniqueExistentialQuantifier
    (contractType contractMultiExistentialQuantification
    (contractType contractExistentialQuantification
    (contractType contractExistentialQuantifier
    (contractType contractMultiUniversalQuantification
    (contractType contractUniversalQuantification
    (contractType contractUniversalQuantifier
    (contractType contractDescription
    (contractType contractNonEquality
    (contractType contractEquivalence
    (contractType contractIff
    (contractType contractImplication
    (contractType contractDisjunction
    (contractType contractConjunction
    (contractType contractNegation
    (contractType contractNot
    (contractType contractFalse
    (contractType contractTrue
    (contractProductsInType
    (embedExtType t)))))))))))))))))))))))))))))))))

  % API public
  op contractExprAll : Expression -> ExtExpression
  def contractExprAll e =
    (contractExpr contractRecursiveLet
    (contractExpr contractSimpleLet
    (contractExpr contractNonRecursiveLet
    (contractExpr contractCaseFromNestedCases
    (contractExpr contractCaseFromCond
    (contractExpr contractBindingConditional
    (contractExpr contractRecordUpdate
    (contractExpr contractRecordUpdater
    (contractExpr contractTuple
    (contractExpr contractRecord
    (contractExpr contractRecordConstructor
    (contractExpr contractDottedProjection
    (contractExpr contractUniqueExistentialQuantification
    (contractExpr contractUniqueExistentialQuantifier
    (contractExpr contractMultiExistentialQuantification
    (contractExpr contractExistentialQuantification
    (contractExpr contractExistentialQuantifier
    (contractExpr contractMultiUniversalQuantification
    (contractExpr contractUniversalQuantification
    (contractExpr contractUniversalQuantifier
    (contractExpr contractDescription
    (contractExpr contractNonEquality
    (contractExpr contractEquivalence
    (contractExpr contractIff
    (contractExpr contractImplication
    (contractExpr contractDisjunction
    (contractExpr contractConjunction
    (contractExpr contractNegation
    (contractExpr contractNot
    (contractExpr contractFalse
    (contractExpr contractTrue
    (contractProductsInExpr
    (embedExtExpr e)))))))))))))))))))))))))))))))))

endspec
