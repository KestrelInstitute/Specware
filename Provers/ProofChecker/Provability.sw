spec

  import SyntacticOperations

  (* It is convenient to define a type for rules as syntactic entities, so
  that we can more easily refer to them. The names of the rules are similar to
  those used in LD but they are a bit more explicit.

  Note that there are more rules here than in LD, because here we model
  explicitly various types, expressions, and patterns that in LD are simply
  viewed as abbreviations. Nonetheless, we exploit the fact that certain
  expressions can be seen as abbreviations of others in certain inference
  rules. *)

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
    | exEmbedder0
    | exEmbedder1
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

    %%%%%%%%%% well-formed context:
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

    %%%%%%%%%% well-formed spec:
    | spe ->
      (fa (sp:Spec)
         pj (wellFormedContext sp)
      => pj (wellFormedSpec sp))

    %%%%%%%%%% well-formed type:
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
         (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS elem i)))
      => pj (wellFormedType (cx, PRODUCT tS)))
    | tySub ->
      (fa (cx:Context, r:Expression, t:Type)
         pj (wellTypedExpr (cx, r, t --> BOOL))
      && exprFreeVars r = empty
      => pj (wellFormedType (cx, t \\ r)))
    | tyQuot ->
      (fa (cx:Context, q:Expression, v:Variable, v1:Variable, v2:Variable, t:Type)
         pj (theore (cx, FA (v,t) (q __ PAIR (VAR v) (VAR v))))
      && pj (theore (cx, FAA (seq2 ((v,t), (v1,t)))
                             (q __ PAIR (VAR v) (VAR v1)
                              ==>
                              q __ PAIR (VAR v1) (VAR v))))
      && pj (theore (cx, FAA (seq3 ((v,t), (v1,t), (v2,t)))
                             (q __ PAIR (VAR v)  (VAR v1)
                              &&&
                              q __ PAIR (VAR v1) (VAR v2)
                              ==>
                              q __ PAIR (VAR v)  (VAR v2))))
      && v ~= v1 && v1 ~= v2 && v ~= v2
      && exprFreeVars q = empty
      => pj (wellFormedType (cx, t // q)))

    %%%%%%%%%% type equivalence:
    | tyEqDef ->
      (fa (cx:Context, tn:TypeName, tvS:TypeVariables, t:Type,
           tS:Types, tsbs:TypeSubstitution)
         noRepetitions? tvS
      && length tvS = length tS
      && tsbs = FMap.fromSequences (tvS, tS)
      && pj (wellFormedContext cx)
      && typeDefinition (tn, tvS, t) in? cx
      && (fa(i:Nat) i < length tvS =>
            pj (wellFormedType (cx, tS elem i)))
      => pj (typeEquivalence (cx, TYPE tn tS, typeSubstInType tsbs t)))
    | tyEqReflexive ->
      (fa (cx:Context, t:Type)
         pj (wellFormedType (cx, t))
      => pj (typeEquivalence (cx, t, t)))
    | tyEqSymmetric ->
      (fa (cx:Context, t1:Type, t2:Type)
         pj (typeEquivalence (cx, t1, t2))
      => pj (typeEquivalence (cx, t2, t1)))
    | tyEqTransitive ->
      (fa (cx:Context, t1:Type, t2:Type, t3:Type)
         pj (typeEquivalence (cx, t1, t2))
      && pj (typeEquivalence (cx, t2, t3))
      => pj (typeEquivalence (cx, t1, t3)))
    | tyEqSubstitution ->
      (fa (cx:Context, t:Type, t1:Type, t2:Type, newT:Type, pos:Position)
         pj (wellFormedType (cx, t))
      && pj (typeEquivalence (cx, t1, t2))
      && typeSubstInTypeAt (t, t1, t2, pos, newT)
      => pj (typeEquivalence (cx, t, newT)))
    | tyEqSumOrder ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, prm:Permutation)
         length cS = length t?S
      && permutationForLength? (prm, length cS)
      && pj (wellFormedType (cx, SUM cS t?S))
      => pj (typeEquivalence (cx, SUM cS t?S,
                                  SUM (permute(cS,prm)) (permute(t?S,prm)))))
    | tyEqRecordOrder ->
      (fa (cx:Context, fS:Fields, tS:Types, prm:Permutation)
         length fS = length tS
      && permutationForLength? (prm, length fS)
      && pj (wellFormedType (cx, TRECORD fS tS))
      => pj (typeEquivalence (cx, TRECORD fS tS,
                                  TRECORD (permute(fS,prm)) (permute(tS,prm)))))
    | tyEqProductOrder ->
      (fa (cx:Context, tS:Types, prm:Permutation)
         permutationForLength? (prm, length tS)
      && pj (wellFormedType (cx, PRODUCT tS))
      => pj (typeEquivalence (cx, PRODUCT tS, PRODUCT (permute(tS,prm)))))
    | tyEqSubPredicate ->
      (fa (cx:Context, t:Type, r:Expression, r1:Expression)
         pj (wellFormedType (cx, t \\ r))
      && pj (wellFormedType (cx, t \\ r1))
      && pj (theore (cx, r == r1))
      => pj (typeEquivalence (cx, t \\ r, t \\ r1)))
    | tyEqQuotientPredicate ->
      (fa (cx:Context, t:Type, q:Expression, q1:Expression)
         pj (wellFormedType (cx, t // q))
      && pj (wellFormedType (cx, t // q1))
      && pj (theore (cx, q == q1))
      => pj (typeEquivalence (cx, t // q, t // q1)))

    %%%%%%%%%% well-typed expression:
    | exVariable ->
      (fa (cx:Context, v:Variable, t:Type)
         pj (wellFormedContext cx)
      && varDeclaration (v, t) in? cx
      => pj (wellTypedExpr (cx, VAR v, t)))
    | exTrue ->
      (fa (cx:Context)
         pj (wellFormedContext cx)
      => pj (wellTypedExpr (cx, TRUE, BOOL)))
    | exFalse ->
      (fa (cx:Context)
         pj (wellFormedContext cx)
      => pj (wellTypedExpr (cx, FALSE, BOOL)))
    | exRecordProjection ->
      (fa (cx:Context, e:Expression, fS:Fields, tS:Types, i:Nat)
         i < length fS
      && i < length tS
      && pj (wellTypedExpr (cx, e, TRECORD fS tS))
      => pj (wellTypedExpr (cx, e DOTr (fS elem i), tS elem i)))
    | exTupleProjection ->
      (fa (cx:Context, e:Expression, tS:Types, i:PosNat)
         i <= length tS
      && pj (wellTypedExpr (cx, e, PRODUCT tS))
      => pj (wellTypedExpr (cx, e DOTt i, tS elem (i-1))))
    | exRelaxator ->
      (fa (cx:Context, t:Type, r:Expression)
         pj (wellFormedType (cx, t \\ r))
      => pj (wellTypedExpr (cx, RELAX r, (t \\ r) --> t)))
    | exQuotienter ->
      (fa (cx:Context, t:Type, q:Expression)
         pj (wellFormedType (cx, t // q))
      => pj (wellTypedExpr (cx, QUOTIENT q, t --> (t // q))))
    | exNegation ->
      (fa (cx:Context, e:Expression)
         pj (wellTypedExpr (cx, e, BOOL))
      => pj (wellTypedExpr (cx, ~~ e, BOOL)))
    | exApplication ->
      (fa (cx:Context, e1:Expression, e2:Expression, t1:Type, t2:Type)
         pj (wellTypedExpr (cx, e1, t1 --> t2))
      && pj (wellTypedExpr (cx, e2, t1))
      => pj (wellTypedExpr (cx, e1 __ e2, t2)))
    | exEquation ->
      (fa (cx:Context, e1:Expression, e2:Expression, t:Type)
         pj (wellTypedExpr (cx, e1, t))
      && pj (wellTypedExpr (cx, e2, t))
      => pj (wellTypedExpr (cx, e1 == e2, BOOL)))
    | exInequation ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 == e2, BOOL))
      => pj (wellTypedExpr (cx, e1 =/= e2, BOOL)))
    | exRecordUpdate ->
      (fa (cx:Context, e1:Expression, e2:Expression,
           fS:Fields, fS1:Fields, fS2:Fields, tS:Types, tS1:Types, tS2:Types)
         length fS = length tS
      && pj (wellTypedExpr (cx, e1, TRECORD (fS ++ fS1) (tS ++ tS1)))
      && pj (wellTypedExpr (cx, e2, TRECORD (fS ++ fS2) (tS ++ tS2)))
      && toSet fS1 /\ toSet fS2 = empty
      => pj (wellTypedExpr (cx,
                            e1 <<< e2,
                            TRECORD (fS ++ fS1 ++ fS2) (tS ++ tS1 ++ tS2))))
    | exRestriction ->
      (fa (cx:Context, t:Type, r:Expression, e:Expression)
         pj (wellFormedType (cx, t \\ r))
      && pj (wellTypedExpr (cx, e, t))
      && pj (theore (cx, r __ e))
      => pj (wellTypedExpr (cx, RESTRICT r e, t \\ r)))
    | exChoice ->
      (fa (cx:Context, t:Type, q:Expression, e:Expression, t1:Type,
           v:Variable, v1:Variable)
         pj (wellFormedType (cx, t // q))
      && pj (wellTypedExpr (cx, e, t --> t1))
      && pj (theore (cx, FAA (seq2 ((v,t), (v1, t)))
                             (q __ PAIR (VAR v) (VAR v1)
                              ==>
                              e __ (VAR v) == e __ (VAR v1))))
      && v ~= v1
      && ~(v in? exprFreeVars e) && ~(v1 in? exprFreeVars e)
      => pj (wellTypedExpr (cx, CHOOSE q e, (t // q) --> t1)))
    | exConjunction ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, IF e1 e2 FALSE, BOOL))
      => pj (wellTypedExpr (cx, e1 &&& e2, BOOL)))
    | exDisjunction ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, IF e1 TRUE e2, BOOL))
      => pj (wellTypedExpr (cx, e1 ||| e2, BOOL)))
    | exImplication ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, IF e1 e2 TRUE, BOOL))
      => pj (wellTypedExpr (cx, e1 ==> e2, BOOL)))
    | exEquivalence ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1, BOOL))
      && pj (wellTypedExpr (cx, e2, BOOL))
      => pj (wellTypedExpr (cx, e1 <==> e2, BOOL)))
    | exRecord ->
      (fa (cx:Context, fS:Fields, tS:Types, eS:Expressions)
         length tS = length eS
      && pj (wellFormedType (cx, TRECORD fS tS))
      && (fa(i:Nat) i < length eS =>
            pj (wellTypedExpr (cx, eS elem i, tS elem i)))
      => pj (wellTypedExpr (cx, RECORD fS eS, TRECORD fS tS)))
    | exTuple ->
      (fa (cx:Context, tS:Types, eS:Expressions)
         length tS = length eS
      && pj (wellFormedType (cx, PRODUCT tS))
      && (fa(i:Nat) i < length eS =>
            pj (wellTypedExpr (cx, eS elem i, tS elem i)))
      => pj (wellTypedExpr (cx, TUPLE eS, PRODUCT tS)))
    | exAbstraction ->
      (fa (cx:Context, vS:Variables, tS:Types, bvS:BoundVars,
           e:Expression, t:Type)
         length vS = length tS
      && bvS = zip (vS, tS)
      && pj (wellTypedExpr (cx ++ multiVarDecls bvS, e, t))
      => pj (wellTypedExpr (cx, FNN bvS e, PRODUCT tS --> t)))
    | exUniversal ->
      (fa (cx:Context, bvS:BoundVars, e:Expression)
         pj (wellTypedExpr (cx, FNN bvS e == FNN bvS TRUE, BOOL))
      => pj (wellTypedExpr (cx, FAA bvS e, BOOL)))
    | exExistential ->
      (fa (cx:Context, bvS:BoundVars, e:Expression)
         pj (wellTypedExpr (cx, FAA bvS e, BOOL))
      => pj (wellTypedExpr (cx, EXX bvS e, BOOL)))
    | exExistential1 ->
      (fa (cx:Context, bvS:BoundVars, e:Expression)
         pj (wellTypedExpr (cx, EXX bvS e, BOOL))
      => pj (wellTypedExpr (cx, EXX1 bvS e, BOOL)))
    | exIfThenElse ->
      (fa (cx:Context, e0:Expression, e1:Expression, e2:Expression, t:Type)
         pj (wellTypedExpr (cx, e0, BOOL))
      && pj (wellTypedExpr (cx <| axio (empty, e0), e1, t))
      && pj (wellTypedExpr (cx <| axio (empty, ~~ e0), e2, t))
      => pj (wellTypedExpr (cx, IF e0 e1 e2, t)))
    | exOpInstance ->
      (fa (cx:Context, o:Operation, tvS:TypeVariables, t:Type, tS:Types,
           tsbs:TypeSubstitution)
         noRepetitions? tvS
      && length tvS = length tS
      && tsbs = FMap.fromSequences (tvS, tS)
      && pj (wellFormedContext cx)
      && opDeclaration (o, tvS, t) in? cx
      && (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS elem i)))
      => pj (wellTypedExpr (cx, OP o tS, typeSubstInType tsbs t)))
    | exEmbedder0 ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, i:Nat)
         i < length cS
      && i < length t?S
      && t?S elem i = None
      && pj (wellFormedType (cx, SUM cS t?S))
      => pj (wellTypedExpr (cx, EMBED (SUM cS t?S) (cS elem i), SUM cS t?S)))
    | exEmbedder0 ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, i:Nat, t:Type)
         i < length cS
      && i < length t?S
      && t?S elem i = Some t
      && pj (wellFormedType (cx, SUM cS t?S))
      => pj (wellTypedExpr (cx,
                            EMBED (SUM cS t?S) (cS elem i),
                            t --> (SUM cS t?S))))
    | exCase ->
      (fa (cx:Context, e:Expression, n:Nat, pS:Patterns, eS:Expressions,
           t:Type, t1:Type, caseMatches:Expressions,
           posCxS:FSeq Context, negCxS:FSeq Context)
         length pS = n
      && length eS = n
      && length caseMatches = n
      && length posCxS = n
      && length negCxS = n
      && pj (wellTypedExpr (cx, e, t))
      && (fa(i:Nat) i < n =>
            pj (wellTypedPatt (cx, pS elem i, t)))
      && (fa(i:Nat) i < n =>
            caseMatches elem i =
            EXX (pattBoundVars (pS elem i))
                (pattAssumptions (pS elem i, e)))
      && pj (theore (cx, disjoinAll caseMatches))
      && (fa(i:Nat) i < n =>
            posCxS elem i =
            multiVarDecls (pattBoundVars (pS elem i))
              <| axio (empty, pattAssumptions (pS elem i, e)))
      && (fa(i:Nat) i < n =>
            (let conjuncts:Expressions = the (fn conjuncts ->
                 length conjuncts = i &&
                 (fa(j:Nat) j < i =>
                    conjuncts elem j = ~~ (caseMatches elem j))) in
             negCxS elem i =
             singleton (axio (empty, conjoinAll conjuncts))))
      && (fa(i:Nat) i < n =>
            pj (wellTypedExpr (cx ++ (negCxS elem i) ++ (posCxS elem i),
                               eS elem i,
                               t1)))
      => pj (wellTypedExpr (cx, CASE e (zip (pS, eS)), t1)))
    | exRecursiveLet ->
      (* Since here we have defined unique existentials (`EXX1') to bind
      multiple variables, the expression of the rule here is actually simpler
      than in LD, where unique existentials can only bind one variable. *)
      (fa (cx:Context, vS:Variables, tS:Types, bvS:BoundVars,
           eS:Expressions, n:Nat, e:Expression, t:Type)
         length vS = n
      && length tS = n
      && length eS = n
      && bvS = zip (vS, tS)
      && pj (theore (cx, EXX1 bvS (TUPLE (map (VAR, vS)) == TUPLE eS)))
      && pj (wellTypedExpr (cx ++ multiVarDecls bvS, e, t))
      => pj (wellTypedExpr (cx, LETDEF bvS eS e, t)))
    | exNonRecursiveLet ->
      (fa (cx:Context, p:Pattern, e:Expression, e1:Expression, t:Type)
         pj (wellTypedExpr (cx, CASE e (zip (singleton p, singleton e1)), t))
      => pj (wellTypedExpr (cx, LET p e e1, t)))
    | exEquivalentTypes ->
      (fa (cx:Context, e:Expression, t:Type, t1:Type)
         pj (wellTypedExpr (cx, e, t))
      && pj (typeEquivalence (cx, t, t1))
      => pj (wellTypedExpr (cx, e, t1)))
    | exAlphaAbstraction ->
      (fa (cx:Context, tS:Types, e:Expression, t:Type, i:Nat,
           oldVi:Variable, newVi:Variable, oldVS:Variables, newVS:Variables,
           oldBvS:BoundVars, newBvS:BoundVars, esbs:ExpressionSubstitution)
         length oldVS = length tS
      && oldBvS = zip (oldVS, tS)
      && i < length oldVS
      && oldVi = oldVS elem i
      && esbs = FMap.singleton (oldVi, VAR newVi)
      && pj (wellTypedExpr (cx, FNN oldBvS e, t))
      && ~(newVi in? exprFreeVars e \/ captVars oldVi e)
      && newVS = update (oldVS, i, newVi)
      && newBvS = zip (newVS, tS)
      => pj (wellTypedExpr (cx, FNN newBvS (exprSubst esbs e), t)))
    | exAlphaCase ->
      (fa (cx:Context, e:Expression, t:Type, i:Nat,
           oldPS:Patterns, newPS:Patterns, oldPi:Pattern, newPi:Pattern,
           oldV:Variable, newV:Variable, oldES:Expressions,
           newES:Expressions, oldEi:Expression, newEi:Expression,
           esbs:ExpressionSubstitution)
         esbs = FMap.singleton (oldV, VAR newV)
      && length oldPS = length oldES
      && i < length oldPS
      && oldPi = oldPS elem i
      && oldEi = oldES elem i
      && pj (wellTypedExpr (cx, CASE e (zip (oldPS, oldES)), t))
      && oldV in? pattVars oldPi
      && ~(newV in? pattVars oldPi \/ exprFreeVars oldEi \/ captVars oldV oldEi)
      && newPi = pattSubst (oldV, newV) oldPi
      && newPS = update (oldPS, i, newPi)
      && newEi = exprSubst esbs oldEi
      && newES = update (oldES, i, newEi)
      => pj (wellTypedExpr (cx, CASE e (zip (newPS, newES)), t)))
    | exAlphaRecursiveLet ->
      (fa (cx:Context, tS:Types, i:Nat, esbs:ExpressionSubstitution, t:Type,
           oldVi:Variable, newVi:Variable, oldVS:Variables, newVS:Variables,
           oldBvS:BoundVars, newBvS:BoundVars, oldE:Expression, newE:Expression,
           oldES:Expressions, newES:Expressions)
         esbs = FMap.singleton (oldVi, VAR newVi)
      && length oldVS = length tS
      && oldBvS = zip (oldVS, tS)
      && length oldBvS = length oldES
      && i < length oldVS
      && oldVi = oldVS elem i
      && pj (wellTypedExpr (cx, LETDEF oldBvS oldES oldE, t))
      && ~(newVi in? toSet oldVS \/ captVars oldVi oldE \/
                     unionAll (map (exprFreeVars, oldES)) \/
                     unionAll (map (captVars oldVi, oldES)))
      && newVS = update (oldVS, i, newVi)
      && newBvS = zip (newVS, tS)
      && newES = map (exprSubst esbs, oldES)
      && newE = exprSubst esbs oldE
      => pj (wellTypedExpr (cx, LETDEF newBvS newES newE, t)))

    %%%%%%%%%% well-typed pattern:
    | paVariable ->
      (fa (cx:Context, t:Type, v:Variable)
         pj (wellFormedType (cx, t))
      && ~(v in? contextVars cx)
      => pj (wellTypedPatt (cx, PVAR (v, t), t)))
    | paEmbedding0 ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, i:Nat)
         i < length cS
      && i < length t?S
      && t?S elem i = None
      && pj (wellFormedType (cx, SUM cS t?S))
      => pj (wellTypedPatt (cx, PEMBED0 (SUM cS t?S) (cS elem i), SUM cS t?S)))
    | paEmbedding1 ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, p:Pattern, t:Type, i:Nat)
         i < length cS
      && i < length t?S
      && t?S elem i = Some t
      && pj (wellFormedType (cx, SUM cS t?S))
      && pj (wellTypedPatt (cx, p, t))
      => pj (wellTypedPatt (cx, PEMBED (SUM cS t?S) (cS elem i) p, SUM cS t?S)))
    | paRecord ->
      (fa (cx:Context, fS:Fields, tS:Types, pS:Patterns)
         length pS = length tS
      && pj (wellFormedType (cx, TRECORD fS tS))
      && (fa(i:Nat) i < length pS =>
            pj (wellTypedPatt (cx, pS elem i, tS elem i)))
      && (fa(i:Nat,j:Nat) i < length pS && j < length pS && i ~= j =>
            pattVars (pS elem i) /\ pattVars (pS elem j) = empty)
      => pj (wellTypedPatt (cx, PRECORD fS pS, TRECORD fS tS)))
    | paTuple ->
      (fa (cx:Context, tS:Types, pS:Patterns)
         pj (wellFormedType (cx, PRODUCT tS))
      && (fa(i:Nat) i < length pS =>
            pj (wellTypedPatt (cx, pS elem i, tS elem i)))
      && (fa(i:Nat,j:Nat) i < length pS && j < length pS && i ~= j =>
            pattVars (pS elem i) /\ pattVars (pS elem j) = empty)
      => pj (wellTypedPatt (cx, PTUPLE pS, PRODUCT tS)))
    | paAlias ->
      (fa (cx:Context, v:Variable, t:Type, p:Pattern)
         pj (wellTypedPatt (cx, p, t))
      && ~(v in? contextVars cx \/ pattVars p)
      => pj (wellTypedPatt (cx, (v, t) AS p, t)))
    | paEquivalentTypes ->
      (fa (cx:Context, p:Pattern, t:Type, t1:Type)
         pj (wellTypedPatt (cx, p, t))
      && pj (typeEquivalence (cx, t, t1))
      => pj (wellTypedPatt (cx, p, t1)))

    %%%%%%%%%% theorem:
    | thAxiom ->
      (fa (cx:Context, tvS:TypeVariables, e:Expression, tS:Types,
           tsbs:TypeSubstitution)
         noRepetitions? tvS
      && length tvS = length tS
      && tsbs = FMap.fromSequences (tvS, tS)
      && pj (wellFormedContext cx)
      && axio (tvS, e) in? cx
      && (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS elem i)))
      => pj (theore (cx, typeSubstInExpr tsbs e)))
    | thOpDef ->
      (fa (cx:Context, tvS:TypeVariables, o:Operation, e:Expression, tS:Types,
           tsbs:TypeSubstitution)
         noRepetitions? tvS
      && length tvS = length tS
      && tsbs = FMap.fromSequences (tvS, tS)
      && pj (wellFormedContext cx)
      && opDefinition (tvS, o, e) in? cx
      && (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS elem i)))
      => pj (theore (cx, OP o tS == typeSubstInExpr tsbs e)))
    | thSubstitution ->
      (fa (cx:Context, oldE:Expression, e1:Expression, e2:Expression,
           newE:Expression, pos:Position)
         pj (theore (cx, oldE))
      && pj (theore (cx, e1 == e2))
      && exprSubstAt (oldE, e1, e2, pos, newE)
      && exprSubstAtOK? (oldE, e1, e2, pos)
      => pj (theore (cx, newE)))
    | thTypeSubstitution ->
      (fa (cx:Context, oldE:Expression, t1:Type, t2:Type, pos:Position,
           newE:Expression)
         pj (theore (cx, oldE))
      && pj (typeEquivalence (cx, t1, t2))
      && typeSubstInExprAt (oldE, t1, t2, pos, newE)
      => pj (theore (cx, newE)))
    | thBoolean ->
      (fa (cx:Context, e:Expression, v:Variable)
         pj (wellTypedExpr (cx, e, BOOL --> BOOL))
      && ~(v in? exprFreeVars e)
      => pj (theore (cx, e __ TRUE &&& e __ FALSE <==> FA (v, BOOL) e __ VAR v)))
    | thCongruence ->
      (fa (cx:Context, e1:Expression, e2:Expression, e:Expression,
           t:Type, t1:Type)
         pj (wellTypedExpr (cx, e1, t))
      && pj (wellTypedExpr (cx, e2, t))
      && pj (wellTypedExpr (cx, e, t --> t1))
      => pj (theore (cx, e1 == e2 ==> e __ e1 == e __ e2)))
    | thExtensionality ->
      (fa (cx:Context, e1:Expression, e2:Expression, t:Type, t1:Type, v:Variable)
         pj (wellTypedExpr (cx, e1, t --> t1))
      && pj (wellTypedExpr (cx, e2, t --> t1))
      && ~(v in? exprFreeVars e1 \/ exprFreeVars e2)
      => (pj (theore (cx, e1 == e2 <==>
                          FA (v, BOOL) e1 __ VAR v == e2 __ VAR v))))
    | thAbstraction ->
      (fa (cx:Context, vS:Variables, tS:Types, bvS:BoundVars, e:Expression,
           eS:Expressions, t:Type, esbs:ExpressionSubstitution)
         noRepetitions? vS
      && length vS = length eS
      && esbs = FMap.fromSequences (vS, eS)
      && length vS = length tS
      && bvS = zip (vS, tS)
      && pj (wellTypedExpr (cx, (FNN bvS e) __ (TUPLE eS), t))
      && exprSubstOK? (e, esbs)
      => pj (theore (cx, ((FNN bvS e) __ (TUPLE eS)) == exprSubst esbs e)))
    | thIfThenElse ->
      (fa (cx:Context, e0:Expression, e1:Expression, e2:Expression,
           e3:Expression, t:Type)
         pj (wellTypedExpr (cx, IF e0 e1 e2, t))
      && pj (theore (cx <| axio (empty,   e0), e1 == e3))
      && pj (theore (cx <| axio (empty, ~~e0), e2 == e3))
      => pj (theore (cx, IF e0 e1 e2 == e3)))
    | thRecord ->
      (fa (cx:Context, fS:Fields, tS:Types, v:Variable, vS:Variables)
         noRepetitions? (v |> vS)
      && length vS = length tS
      && pj (wellFormedType (cx, TRECORD fS tS))
      => pj (theore (cx, FA (v, TRECORD fS tS)
                            (EXX1 (zip (vS, tS))
                                  (VAR v == RECORD fS (map (VAR, vS)))))))
    | thTuple ->
      (fa (cx:Context, tS:Types, v:Variable, vS:Variables)
         noRepetitions? (v |> vS)
      && length vS = length tS
      && pj (wellFormedType (cx, PRODUCT tS))
      => pj (theore (cx, FA (v, PRODUCT tS)
                            (EXX1 (zip (vS, tS))
                                  (VAR v == TUPLE (map (VAR, vS)))))))
    | thRecordProjection ->
      (fa (cx:Context, fS:Fields, tS:Types, eS:Expressions, i:Nat)
         i < length eS
      && i < length fS
      && pj (wellTypedExpr (cx, RECORD fS eS, TRECORD fS tS))
      => pj (theore (cx, (RECORD fS eS) DOTr (fS elem i) == (eS elem i))))
    | thTupleProjection ->
      (fa (cx:Context, tS:Types, eS:Expressions, i:Nat)
         i < length eS
      && pj (wellTypedExpr (cx, TUPLE eS, PRODUCT tS))
      => pj (theore (cx, (TUPLE eS) DOTt (i + 1) == (eS elem i))))
    | thRecordUpdate1 ->
      (fa (cx:Context, fS1:Fields, fS2:Fields, tS1:Types, tS2:Types,
           eS1:Expressions, eS2:Expressions, i:Nat)
         i < length fS1
      && i < length eS1
      && pj (wellTypedExpr (cx, RECORD fS1 eS1, TRECORD fS1 tS1))
      && pj (wellTypedExpr (cx, RECORD fS2 eS2, TRECORD fS2 tS2))
      && ~((fS1 elem i) in? fS2)
      && pj (theore (cx,
                     ((RECORD fS1 eS1) <<< (RECORD fS2 eS2)) DOTr (fS1 elem i)
                     == (eS1 elem i))))
    | thRecordUpdate2 ->
      (fa (cx:Context, fS1:Fields, fS2:Fields, tS1:Types, tS2:Types,
           eS1:Expressions, eS2:Expressions, i:Nat)
         i < length fS2
      && i < length eS2
      && pj (wellTypedExpr (cx, RECORD fS1 eS1, TRECORD fS1 tS1))
      && pj (wellTypedExpr (cx, RECORD fS2 eS2, TRECORD fS2 tS2))
      && pj (theore (cx,
                     ((RECORD fS1 eS1) <<< (RECORD fS2 eS2)) DOTr (fS2 elem i)
                     == (eS2 elem i))))
    | thEmbedderSurjective ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, v:Variable, v1:Variable,
           disjuncts:Expressions)
         pj (wellFormedType (cx, SUM cS t?S))
      && v ~= v1
      && length cS = length t?S
      && length disjuncts = length cS
      && (fa(i:Nat) i < length disjuncts =>
            disjuncts elem i =
            (case (t?S elem i) of
               | Some t -> EX (v1, t)
                              (VAR v ==
                               (EMBED (SUM cS t?S) (cS elem i)) __ VAR v1)
               | None -> VAR v == EMBED (SUM cS t?S) (cS elem i)))
      => pj (theore (cx, FA (v, SUM cS t?S) (disjoinAll disjuncts))))
    | thEmbeddersDistinct ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, i:Nat, j:Nat,
           vi:Variable, vj:Variable, conclusion:Expression)
         pj (wellFormedType (cx, SUM cS t?S))
      && i < length cS
      && j < length cS
      && i < length t?S
      && j < length t?S
      && i ~= j
      && vi ~= vj
      && conclusion =
         (case (t?S elem i, t?S elem j) of
            | (Some ti, Some tj) ->
              FAA (seq2 ((vi, ti), (vj, tj)))
                  (EMBED (SUM cS t?S) (cS elem i) __ VAR vi =/=
                   EMBED (SUM cS t?S) (cS elem i) __ VAR vj)
            | (Some ti, None) ->
              FA (vi, ti) (EMBED (SUM cS t?S) (cS elem i) __ VAR vi =/=
                           EMBED (SUM cS t?S) (cS elem j))
            | (None, Some tj) ->
              FA (vj, tj) (EMBED (SUM cS t?S) (cS elem i) =/=
                           EMBED (SUM cS t?S) (cS elem j) __ VAR vj)
            | (None, None) ->
              EMBED (SUM cS t?S) (cS elem i) =/= EMBED (SUM cS t?S) (cS elem j))
      => pj (theore (cx, conclusion)))
    | thEmbedderInjective ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, v1:Variable, v2:Variable,
           i:Nat, ti:Type)
         i < length cS
      && i < length t?S
      && t?S elem i = Some ti
      && pj (wellFormedType (cx, SUM cS t?S))
      && v1 ~= v2
      => pj (theore (cx, FAA (seq2 ((v1,ti), (v2,ti)))
                             (VAR v1 =/= VAR v2 ==>
                              EMBED (SUM cS t?S) (cS elem i) __ VAR v1 =/=
                              EMBED (SUM cS t?S) (cS elem i) __ VAR v2))))
    | thRelaxatorSatisfiesPredicate ->
      (fa (cx:Context, t:Type, r:Expression, v:Variable)
         pj (wellFormedType (cx, t \\ r))
      => pj (theore (cx, FA (v, t \\ r)
                            (r __ (RELAX r __ (VAR v))))))
    | thRelaxatorInjective ->
      (fa (cx:Context, t:Type, r:Expression, v1:Variable, v2:Variable)
         pj (wellFormedType (cx, t \\ r))
      && v1 ~= v2
      => pj (theore (cx, FAA (seq2 ((v1, t \\ r), (v2, t \\ r)))
                             (VAR v1 =/= VAR v2 ==>
                              RELAX r __ (VAR v1) =/= RELAX r __ (VAR v2)))))
    | thRelexatorSurjective ->
      (fa (cx:Context, t:Type, r:Expression, v:Variable, v1:Variable)
         pj (wellFormedType (cx, t \\ r))
      && v ~= v1
      => pj (theore (cx, FA (v, t)
                            (r __ (VAR v) ==>
                             EX (v1, t \\ r) (VAR v == RELAX r __ (VAR v1))))))
    | thRestriction ->
      (fa (cx:Context, t:Type, r:Expression, v:Variable)
         pj (wellFormedType (cx, t \\ r))
      => pj (theore (cx, FA (v, t \\ r)
                            (RESTRICT r (RELAX r __ (VAR v)) == VAR v))))
    | thQuotienterSurjective ->
      (fa (cx:Context, t:Type, q:Expression, v:Variable, v1:Variable)
         pj (wellFormedType (cx, t // q))
      && v ~= v1
      => pj (theore (cx, FA (v, t // q)
                            (EX (v1, t) (QUOTIENT q __ (VAR v1) == VAR v)))))
    | thQuotienterConstancy ->
      (fa (cx:Context, t:Type, q:Expression, v1:Variable, v2:Variable)
         pj (wellFormedType (cx, t // q))
      && v1 ~= v2
      => pj (theore (cx, FAA (seq2 ((v1, t), (v2, t)))
                             (q __ PAIR (VAR v1) (VAR v2) <==>
                              QUOTIENT q __ VAR v1 == QUOTIENT q __ VAR v2))))
    | thChoice ->
      (fa (cx:Context, t:Type, t1:Type, q:Expression, e:Expression, v:Variable)
         pj (wellTypedExpr (cx, CHOOSE q e, t // q --> t1))
      && ~(v in? exprFreeVars e)
      => pj (theore (cx, FA (v, t)
                            (CHOOSE q e __ (QUOTIENT q __ VAR v) ==
                             e __ (VAR v)))))
    | thCase ->
      (fa (cx:Context, e:Expression, n:Nat, pS:Patterns, eS:Expressions,
           t:Type, posCxS:FSeq Context, negCxS:FSeq Context, e1:Expression)
         length pS = n
      && length eS = n
      && length posCxS = n
      && length negCxS = n
      && pj (wellTypedExpr (cx, CASE e (zip (pS, eS)), t))
      && (fa(i:Nat) i < n =>
            posCxS elem i =
            multiVarDecls (pattBoundVars (pS elem i))
              <| axio (empty, pattAssumptions (pS elem i, e)))
      && (fa(i:Nat) i < n =>
            (let conjuncts:Expressions = the (fn conjuncts ->
                 length conjuncts = i &&
                 (fa(j:Nat) j < i =>
                    conjuncts elem j =
                    FAA (pattBoundVars (pS elem i))
                        (pattAssumptions (pS elem i, e)))) in
             negCxS elem i =
             singleton (axio (empty, conjoinAll conjuncts))))
      && (fa(i:Nat) i < n =>
            pj (theore (cx ++ (negCxS elem i) ++ (posCxS elem i),
                        (eS elem i) == e1)))
      && (fa(i:Nat) i < n =>
            exprFreeVars e1 /\ pattVars (pS elem i) = empty)
      => pj (theore (cx, CASE e (zip (pS, eS)) == e1)))
    | thRecursiveLet ->
      (fa (cx:Context, vS:Variables, tS:Types, bvS:BoundVars, eS:Expressions,
           n:Nat, e:Expression, t:Type, e1:Expression, conjuncts:Expressions)
         length vS = n
      && length tS = n
      && length eS = n
      && length conjuncts = n
      && bvS = zip (vS, tS)
      && pj (wellTypedExpr (cx, LETDEF bvS eS e, t))
      && (fa(i:Nat) i < n =>
            conjuncts elem i =
            VAR (vS elem i) == (eS elem i))
      && pj (theore (cx ++ multiVarDecls bvS
                        <| axio (empty, conjoinAll conjuncts),
                     e == e1))
      && toSet vS /\ exprFreeVars e1 = empty
      => pj (theore (cx, LETDEF bvS eS e == e1)))
    | thAbbrevTrue ->
      (fa (cx:Context, v:Variable)
         pj (wellFormedContext cx)
      && pj (theore (cx, TRUE ==
                         (FN (v, BOOL) (VAR v) == FN (v, BOOL) (VAR v)))))
    | thAbbrevFalse ->
      (fa (cx:Context, v:Variable)
         pj (wellFormedContext cx)
      && pj (theore (cx, FALSE ==
                         (FN (v, BOOL) (VAR v) == FN (v, BOOL) TRUE))))
    | thAbbrevNegation ->
      (fa (cx:Context, e:Expression)
         pj (wellTypedExpr (cx, ~~ e, BOOL))
      => pj (theore (cx, ~~ e == IF e FALSE TRUE)))
    | thAbbrevInequation ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 =/= e2, BOOL))
      => pj (theore (cx, (e1 =/= e2) == ~~ (e1 == e2))))
    | thAbbrevConjunction ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 &&& e2, BOOL))
      => pj (theore (cx, (e1 &&& e2) == IF e1 e2 FALSE)))
    | thAbbrevDisjunction ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 ||| e2, BOOL))
      => pj (theore (cx, (e1 ||| e2) == IF e1 TRUE e2)))
    | thAbbrevImplication ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 ==> e2, BOOL))
      => pj (theore (cx, (e1 ==> e2) == IF e1 e2 FALSE)))
    | thAbbrevEquivalence ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 <==> e2, BOOL))
      => pj (theore (cx, (e1 <==> e2) == (e1 == e2))))
    | thAbbrevUniversal ->
      (fa (cx:Context, bvS:BoundVars, e:Expression)
         pj (wellTypedExpr (cx, FAA bvS e, BOOL))
      && pj (theore (cx, FAA bvS e ==
                         (FNN bvS e == FNN bvS TRUE))))
    | thAbbrevExistential ->
      (fa (cx:Context, bvS:BoundVars, e:Expression)
         pj (wellTypedExpr (cx, EXX bvS e, BOOL))
      => pj (theore (cx, EXX bvS e == ~~ (FAA bvS (~~ e)))))
    | thAbbrevExistential1 ->
      (fa (cx:Context, vS:Variables, tS:Types, bvS:BoundVars, e:Expression,
           vS1:Variables, bvS1:BoundVars, esbs:ExpressionSubstitution)
         length vS = length tS
      && length vS1 = length vS
      && bvS = zip (vS, tS)
      && bvS1 = zip (vS1, tS)
      && noRepetitions? vS
      && esbs = FMap.fromSequences (vS, map (VAR, vS1))
      && toSet vS /\ toSet vS1 = empty
      && exprSubstOK? (e, esbs)
      && pj (wellTypedExpr (cx, EXX bvS e, BOOL))
      => pj (theore (cx, EXX bvS
                             e &&& (FAA bvS1
                                        (exprSubst esbs e ==>
                                         TUPLE (map (VAR, vS)) ==
                                         TUPLE (map (VAR, vS1)))))))
    | thAbbrevNonRecursiveLet ->
      (fa (cx:Context, p:Pattern, e:Expression, e1:Expression, t:Type)
         pj (wellTypedExpr (cx, LET p e e1, t))
      => pj (theore (cx, LET p e e1 == CASE e (singleton (p, e1)))))


  op provable? : Predicate Judgement
  def provable? = min (fn provable? ->
    (fa(ir:InferenceRule) satisfiesRule? provable? ir))

  type ProvableJudgement = (Judgement | provable?)

endspec
