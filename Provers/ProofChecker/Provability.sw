spec

  import SyntacticOperations

  (* It is convenient to define a type for rules as syntactic entities, so
  that we can more easily refer to them. The names of the rules are similar to
  those used in LD but they are a bit more explicit.

  Note that there are more rules here than in LD, because here we model
  explicitly various types, expressions, and patterns that in LD are simply
  viewed as abbreviations. Nonetheless, we exploit the fact that certain
  expressions can be seen as abbreviations of others by reifying the
  abbreviations as equations in inference rules. *)

  type InferenceRule =
    % well-formed context:
    | cxEmpty
    | cxTypeDecl
    | cxOpDecl
    | cxTypeDef
    | cxOpDef
    | cxAxiom
    | cxTypeVarDecl
    | cxVarDecl
    % well-formed spec:
    | spe
    % well-formed type:
    | tyBoolean
    | tyVariable
    | tyArrow
    | tySum
    | tyInstance
    | tyRecord
    | tyProduct
    | tySub
    | tyQuot
    % type equivalence:
    | tyEqDef
    | tyEqReflexive
    | tyEqSymmetric
    | tyEqTransitive
    | tyEqSubstitution
    | tyEqSumOrder
    | tyEqRecordOrder
    | tyEqProductOrder
    | tyEqSubPredicate
    | tyEqQuotientPredicate
    % well-typed expression:
    | exVariable
    | exTrue
    | exFalse
    | exRecordProjection
    | exTupleProjection
    | exRelaxator
    | exQuotienter
    | exNegation
    | exApplication
    | exEquation
    | exInequation
    | exRecordUpdate
    | exRestriction
    | exChoice
    | exConjunction
    | exDisjunction
    | exImplication
    | exEquivalence
    | exRecord
    | exTuple
    | exAbstraction
    | exUniversal
    | exExistential
    | exExistential1
    | exIfThenElse
    | exOpInstance
    | exEmbedder
    | exCase
    | exRecursiveLet
    | exNonRecursiveLet
    | exEquivalentTypes
    | exAlphaAbstraction
    | exAlphaUniversal
    | exAlphaExistential
    | exAlphaExistential1
    | exAlphaCase
    | exAlphaRecursiveLet
    | exAlphaNonRecursiveLet
    % well-typed pattern:
    | paVariable
    | paEmbedding
    | paRecord
    | paTuple
    | paAlias
    | paEquivalentTypes
    % theorem:
    | thAxiom
    | thOpDef
    | thSubstitution
    | thTypeSubstitution
    | thBoolean
    | thCongruence
    | thExtensionality
    | thAbstraction
    | thIfThenElse
    | thRecord
    | thTuple
    | thRecordProjection
    | thTupleProjection
    | thRecordUpdate1
    | thRecordUpdate2
    | thEmbedderSurjective
    | thEmbeddersDistinct
    | thEmbedderInjective
    | thRelaxatorSatisfiesPredicate
    | thRelaxatorInjective
    | thRelexatorSurjective
    | thRestriction
    | thQuotienterSurjective
    | thQuotienterConstancy
    | thChoice
    | thCase
    | thRecursiveLet
    | thAbbrevTrue
    | thAbbrevFalse
    | thAbbrevNegation
    | thAbbrevInequation
    | thAbbrevConjunction
    | thAbbrevDisjunction
    | thAbbrevImplication
    | thAbbrevEquivalence
    | thAbbrevUniversal
    | thAbbrevExistential
    | thAbbrevExistential1
    | thAbbrevNonRecursiveLet

  (* The goal is to define a predicate `provable?' on judgements. This
  predicate is the minimum one satisfying all the inference rules. So, we
  define an auxiliary predicate `satisfiesInferenceRule?' that says whether a
  predicate on judgements satisfies a given rule. *)

  op satisfiesInferenceRule? : Predicate Judgement -> InferenceRule -> Boolean
  def satisfiesRule? pj = fn
    % well-formed context:
    | cxEmpty ->
      pj (wellFormedContext empty)
    | cxTypeDecl ->
      (fa (cx:Context, tn:TypeName, n:Nat)
         pj (wellFormedContext cx)
      && ~(tn in? contextTypes cx)
      => pj (wellFormedContext (cx <| typeDeclaration (tn, n))))
    | cxOpDecl ->
      (fa (cx:Context, o:Operation, tvS:TypeVariables, t:Type)
         pj (wellFormedContext cx)
      && ~(o in? contextOps cx)
      && pj (wellFormedType (cx ++ multiTypeVarDecls tvS, t))
      => pj (wellFormedContext (cx <| opDeclaration (o, tvS, t))))
    | cxTypeDef ->
      (fa (cx:Context, tn:TypeName, n:Nat, tvS:TypeVariables, t:Type)
         pj (wellFormedContext cx)
      && typeDeclaration (tn, n) in? cx
      && ~(contextDefinesType? (cx, tn))
      && pj (wellFormedType (cx ++ multiTypeVarDecls tvS, t))
      && length tvS = n
      => pj (wellFormedContext (cx <| typeDefinition (tn, tvS, t))))
    | cxOpDef ->
      (fa (cx:Context, o:Operation, tvS:TypeVariables, t:Type,
           tvS1:TypeVariables, v:Variable, e:Expression,
           tsbs:TypeSubstitution, esbs:ExpressionSubstitution)
         noRepetitions? tvS
      && length tvS = length tvS1
      && tsbs = FMap.fromSequences (tvS, map (TVAR, tvS1))
      && esbs = FMap.singleton (v, OP o (map (TVAR, tvS1)))
      && pj (wellFormedContext cx)
      && opDeclaration (o, tvS, t) in? cx
      && ~(contextDefinesOp? (cx, o))
      && pj (theore (cx ++ multiTypeVarDecls tvS1,
                     EX1 (v, typeSubstInType tsbs t)
                         (OPmt o == e)))
      && ~(o in? exprOps e)
      => pj (wellFormedContext (cx <| opDefinition (tvS1, o, e))))
    | cxAxiom ->
      (fa (cx:Context, tvS:TypeVariables, e:Expression)
         pj (wellFormedContext cx)
      && pj (wellTypedExpr (cx ++ multiTypeVarDecls tvS, e, BOOL))
      => pj (wellFormedContext (cx <| axio (tvS, e))))
    | cxTypeVarDecl ->
      (fa (cx:Context, tv:TypeVariable)
         pj (wellFormedContext cx)
      && ~(tv in? contextTypeVars cx)
      => pj (wellFormedContext (cx <| tVarDeclaration tv)))
    | cxVarDecl ->
      (fa (cx:Context, v:Variable, t:Type)
         pj (wellFormedContext cx)
      && ~(v in? contextVars cx)
      && pj (wellFormedType (cx, t))
      => pj (wellFormedContext (cx <| varDeclaration (v, t))))
    % well-formed spec:
    | spe ->
      (fa (sp:Spec)
         pj (wellFormedContext sp)
      => pj (wellFormedSpec sp))
    % well-formed type:
    | tyBoolean ->
      (fa (cx:Context)
         pj (wellFormedContext cx)
      => pj (wellFormedType (cx, BOOL)))
    | tyVariable ->
      (fa (cx:Context, tv:TypeVariable)
         pj (wellFormedContext cx)
      && tv in? contextTypeVars cx
      => pj (wellFormedType (cx, TVAR tv)))
    | tyArrow ->
      (fa (cx:Context, t1:Type, t2:Type)
         pj (wellFormedType (cx, t1))
      && pj (wellFormedType (cx, t2))
      => pj (wellFormedType (cx, t1 --> t2)))
    | tySum ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s)
         noRepetitions? cS
      && length cS = length t?S
      && length cS > 0
      && (fa(i:Nat) i < length cS =>
            (case t?S elem i of
               | Some t -> pj (wellFormedType (cx, t))
               | None   -> true))
      => pj (wellFormedType (cx, SUM cS t?S)))
    | tyInstance ->
      (fa (cx:Context, tn:TypeName, n:Nat, tS:Types)
         pj (wellFormedContext cx)
      && typeDeclaration (tn, n) in? cx
      && length tS = n
      && (fa(i:Nat) i < n =>
            pj (wellFormedType (cx, tS elem i)))
      => pj (wellFormedType (cx, TYPE tn tS)))
    | tyRecord ->
      (fa (cx:Context, fS:Fields, tS:Types)
         pj (wellFormedContext cx)
      && noRepetitions? fS
      && length fS = length tS
      && (fa(i:Nat) i < length fS =>
            pj (wellFormedType (cx, tS elem i)))
      => pj (wellFormedType (cx, TRECORD fS tS)))
    | tyProduct ->
      (fa (cx:Context, tS:Types)
         length tS >= 2
      && (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS elem i)))
      => pj (wellFormedType (cx, PRODUCT tS)))
    | tySub ->
      (fa (cx:Context, r:Expression, t:Type)
         pj (wellTypedExpr (cx, r, t --> BOOL))
      && exprFreeVars r = empty
      => pj (wellFormedType (cx, t \\ r)))
    | tyQuot ->
      (fa (cx:Context, q:Expression, v:Variable, v1:Variable, v2:Variable, t:Type)
         pj (theore (cx, FA (v,t) (q __ PAIR (EVAR v) (EVAR v))))
      && pj (theore (cx, FAA (seq2 ((v,t), (v1,t)))
                             ((q __ PAIR (EVAR v) (EVAR v1))
                              ==>
                              (q __ PAIR (EVAR v1) (EVAR v)))))
      && pj (theore (cx, FAA (seq3 ((v,t), (v1,t), (v2,t)))
                             ((q __ PAIR (EVAR v)  (EVAR v1))
                              &&&
                              (q __ PAIR (EVAR v1) (EVAR v2))
                              ==>
                              (q __ PAIR (EVAR v)  (EVAR v2)))))
      && v ~= v1 && v1 ~= v2 && v ~= v2
      && exprFreeVars q = empty
      => pj (wellFormedType (cx, t // q)))
(*
    % type equivalence:
    | tyEqDef
    | tyEqReflexive
    | tyEqSymmetric
    | tyEqTransitive
    | tyEqSubstitution
    | tyEqSumOrder
    | tyEqRecordOrder
    | tyEqProductOrder
    | tyEqSubPredicate
    | tyEqQuotientPredicate
    % well-typed expression:
    | exVariable
    | exTrue
    | exFalse
    | exRecordProjection
    | exTupleProjection
    | exRelaxator
    | exQuotienter
    | exNegation
    | exApplication
    | exEquation
    | exInequation
    | exRecordUpdate
    | exRestriction
    | exChoice
    | exConjunction
    | exDisjunction
    | exImplication
    | exEquivalence
    | exRecord
    | exTuple
    | exAbstraction
    | exUniversal
    | exExistential
    | exExistential1
    | exIfThenElse
    | exOpInstance
    | exEmbedder
    | exCase
    | exRecursiveLet
    | exNonRecursiveLet
    | exEquivalentTypes
    | exAlphaAbstraction
    | exAlphaUniversal
    | exAlphaExistential
    | exAlphaExistential1
    | exAlphaCase
    | exAlphaRecursiveLet
    | exAlphaNonRecursiveLet
    % well-typed pattern:
    | paVariable
    | paEmbedding
    | paRecord
    | paTuple
    | paAlias
    | paEquivalentTypes
    % theorem:
    | thAxiom
    | thOpDef
    | thSubstitution
    | thTypeSubstitution
    | thBoolean
    | thCongruence
    | thExtensionality
    | thAbstraction
    | thIfThenElse
    | thRecord
    | thTuple
    | thRecordProjection
    | thTupleProjection
    | thRecordUpdate1
    | thRecordUpdate2
    | thEmbedderSurjective
    | thEmbeddersDistinct
    | thEmbedderInjective
    | thRelaxatorSatisfiesPredicate
    | thRelaxatorInjective
    | thRelexatorSurjective
    | thRestriction
    | thQuotienterSurjective
    | thQuotienterConstancy
    | thChoice
    | thCase
    | thRecursiveLet
    | thAbbrevTrue
    | thAbbrevFalse
    | thAbbrevNegation
    | thAbbrevInequation
    | thAbbrevConjunction
    | thAbbrevDisjunction
    | thAbbrevImplication
    | thAbbrevEquivalence
    | thAbbrevUniversal
    | thAbbrevExistential
    | thAbbrevExistential1
    | thAbbrevNonRecursiveLet
*)

  op provable? : Predicate Judgement
  def provable? = min (fn provable? ->
    (fa(ir:InferenceRule) satisfiesRule? provable? ir))

  type ProvableJudgement = (Judgement | provable?)

endspec
