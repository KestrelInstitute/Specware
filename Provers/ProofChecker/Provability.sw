spec

  import SyntacticOperations


  (* It is convenient to define a meta type for rules, so that we can more
  easily refer to them. The names of the rules are similar to those used in LD
  but they are a bit more explicit.

  Note that there are more rules here than in LD, because here we model
  explicitly various types, expressions, and patterns that in LD are simply
  viewed as abbreviations. Nonetheless, we exploit the fact that certain
  expressions can be seen as abbreviations of others in certain inference
  rules. *)

  type InferenceRule =
    % well-formed contexts:
    | cxEmpty
    | cxTypeDecl
    | cxOpDecl
    | cxTypeDef
    | cxOpDef
    | cxAxiom
    | cxTypeVarDecl
    | cxVarDecl
    % well-formed specs:
    | spe
    % well-formed types:
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
    % well-typed expressions:
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
    | exAlphaCase
    | exAlphaRecursiveLet
    % well-typed patterns:
    | paVariable
    | paEmbedding0
    | paEmbedding1
    | paRecord
    | paTuple
    | paAlias
    | paEquivalentTypes
    % theorems:
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
    | thQuotienterEquivClass
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

    %%%%%%%%%% well-formed contexts:
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
      (fa (cx:Context, o:Operation, tvS:TypeVariables, t:Type, tvS1:TypeVariables,
           tsbs:TypeSubstitution, v:Variable, e:Expression, esbs:ExprSubstitution)
         noRepetitions? tvS
      && pj (wellFormedContext cx)
      && opDeclaration (o, tvS, t) in? cx
      && ~(contextDefinesOp? (cx, o))
      && length tvS1 = length tvS
      && tsbs = FMap.fromSequences (tvS, map (TVAR, tvS1))
      && pj (theoreM (cx ++ multiTypeVarDecls tvS1,
                      EX1 (v, typeSubstInType tsbs t) (VAR v == e)))
      && ~(o in? exprOps e)
      && esbs = FMap.singleton (v, OPP o (map (TVAR, tvS1)))
      => pj (wellFormedContext (cx <| opDefinition (o, tvS1, exprSubst esbs e))))
    | cxAxiom ->
      (fa (cx:Context, tvS:TypeVariables, e:Expression, an:AxiomName)
         pj (wellFormedContext cx)
      && pj (wellTypedExpr (cx ++ multiTypeVarDecls tvS, e, BOOL))
      && ~(an in? contextAxioms cx)
      => pj (wellFormedContext (cx <| axioM (an, tvS, e))))
    | cxTypeVarDecl ->
      (fa (cx:Context, tv:TypeVariable)
         pj (wellFormedContext cx)
      && ~(tv in? contextTypeVars cx)
      => pj (wellFormedContext (cx <| typeVarDeclaration tv)))
    | cxVarDecl ->
      (fa (cx:Context, v:Variable, t:Type)
         pj (wellFormedContext cx)
      && ~(v in? contextVars cx)
      && pj (wellFormedType (cx, t))
      => pj (wellFormedContext (cx <| varDeclaration (v, t))))

    %%%%%%%%%% well-formed specs:
    | spe ->
      (fa (sp:Spec)
         pj (wellFormedContext sp)
      => pj (wellFormedSpec sp))

    %%%%%%%%%% well-formed types:
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
         (* Since here we explicitly model sum type components with no type,
         we need to add well-formedness of `cx' in this rule because otherwise
         if no sum type component has a type, then nothing would constrain
         `cx' to be well-formed. *)
         pj (wellFormedContext cx)
      && noRepetitions? cS
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
         pj (wellFormedContext cx)
      && (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS elem i)))
      => pj (wellFormedType (cx, PRODUCT tS)))
    | tySub ->
      (fa (cx:Context, r:Expression, t:Type)
         pj (wellTypedExpr (cx, r, t --> BOOL))
      && exprFreeVars r = empty
      => pj (wellFormedType (cx, t \ r)))
    | tyQuot ->
      (fa (cx:Context, v:Variable, v1:Variable, v2:Variable, t:Type, q:Expression)
         pj (theoreM (cx, FA (v,t) (q @ PAIR (VAR v) (VAR v))))
      && pj (theoreM (cx, FAA (seq2 ((v,t), (v1,t)))
                              (q @ PAIR (VAR v) (VAR v1)
                               ==>
                               q @ PAIR (VAR v1) (VAR v))))
      && pj (theoreM (cx, FAA (seq3 ((v,t), (v1,t), (v2,t)))
                              (q @ PAIR (VAR v)  (VAR v1)
                               &&&
                               q @ PAIR (VAR v1) (VAR v2)
                               ==>
                               q @ PAIR (VAR v)  (VAR v2))))
      && v ~= v1 && v1 ~= v2 && v2 ~= v
      && exprFreeVars q = empty
      => pj (wellFormedType (cx, t / q)))

    %%%%%%%%%% type equivalence:
    | tyEqDef ->
      (fa (cx:Context, tn:TypeName, tvS:TypeVariables, t:Type,
           tS:Types, tsbs:TypeSubstitution)
         pj (wellFormedContext cx)
      && typeDefinition (tn, tvS, t) in? cx
      && (fa(i:Nat) i < length tvS =>
            pj (wellFormedType (cx, tS elem i)))
      && noRepetitions? tvS
      && length tvS = length tS
      && tsbs = FMap.fromSequences (tvS, tS)
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
      (fa (cx:Context, t:Type, t1:Type, t2:Type, pos:Position, newT:Type)
         pj (wellFormedType (cx, t))
      && pj (typeEquivalence (cx, t1, t2))
      && typeSubstInTypeAt (t, t1, t2, pos, newT)
      => pj (typeEquivalence (cx, t, newT)))
    | tyEqSumOrder ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, prm:Permutation)
         pj (wellFormedType (cx, SUM cS t?S))
      && length cS = length t?S
      && permutationForLength? (prm, length cS)
      => pj (typeEquivalence
               (cx, SUM cS t?S, SUM (permute(cS,prm)) (permute(t?S,prm)))))
    | tyEqRecordOrder ->
      (fa (cx:Context, fS:Fields, tS:Types, prm:Permutation)
         pj (wellFormedType (cx, TRECORD fS tS))
      && length fS = length tS
      && permutationForLength? (prm, length fS)
      => pj (typeEquivalence
               (cx, TRECORD fS tS, TRECORD (permute(fS,prm)) (permute(tS,prm)))))
    | tyEqProductOrder ->
      (fa (cx:Context, tS:Types, prm:Permutation)
         pj (wellFormedType (cx, PRODUCT tS))
      && permutationForLength? (prm, length tS)
      => pj (typeEquivalence (cx, PRODUCT tS, PRODUCT (permute(tS,prm)))))
    | tyEqSubPredicate ->
      (fa (cx:Context, t:Type, r1:Expression, r2:Expression)
         pj (wellFormedType (cx, t \ r1))
      && pj (wellFormedType (cx, t \ r2))
      && pj (theoreM (cx, r1 == r2))
      => pj (typeEquivalence (cx, t \ r1, t \ r2)))
    | tyEqQuotientPredicate ->
      (fa (cx:Context, t:Type, q1:Expression, q2:Expression)
         pj (wellFormedType (cx, t / q1))
      && pj (wellFormedType (cx, t / q2))
      && pj (theoreM (cx, q1 == q2))
      => pj (typeEquivalence (cx, t / q1, t / q2)))

    %%%%%%%%%% well-typed expressions:
    | exVariable ->
      (fa (cx:Context, v:Variable, t:Type)
         pj (wellFormedContext cx)
      && varDeclaration (v,t) in? cx
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
         pj (wellTypedExpr (cx, e, TRECORD fS tS))
      && i < length fS
      && i < length tS
      => pj (wellTypedExpr (cx, e DOTr (fS elem i), tS elem i)))
    | exTupleProjection ->
      (fa (cx:Context, e:Expression, tS:Types, i:PosNat)
         pj (wellTypedExpr (cx, e, PRODUCT tS))
      && i <= length tS
      => pj (wellTypedExpr (cx, e DOTt i, tS elem (i-1))))
    | exRelaxator ->
      (fa (cx:Context, t:Type, r:Expression)
         pj (wellFormedType (cx, t \ r))
      => pj (wellTypedExpr (cx, RELAX r, t\r --> t)))
    | exQuotienter ->
      (fa (cx:Context, t:Type, q:Expression)
         pj (wellFormedType (cx, t / q))
      => pj (wellTypedExpr (cx, QUOTIENT q, t --> t/q)))
    | exNegation ->
      (fa (cx:Context, e:Expression)
         pj (wellTypedExpr (cx, e, BOOL))
      => pj (wellTypedExpr (cx, ~~ e, BOOL)))
    | exApplication ->
      (fa (cx:Context, e1:Expression, e2:Expression, t1:Type, t2:Type)
         pj (wellTypedExpr (cx, e1, t1 --> t2))
      && pj (wellTypedExpr (cx, e2, t1))
      => pj (wellTypedExpr (cx, e1 @ e2, t2)))
    | exEquation ->
      (fa (cx:Context, e1:Expression, e2:Expression, t:Type)
         pj (wellTypedExpr (cx, e1, t))
      && pj (wellTypedExpr (cx, e2, t))
      => pj (wellTypedExpr (cx, e1 == e2, BOOL)))
    | exInequation ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 == e2, BOOL))
      => pj (wellTypedExpr (cx, e1 ~== e2, BOOL)))
    | exRecordUpdate ->
      (fa (cx:Context, e1:Expression, e2:Expression,
           fS:Fields, fS1:Fields, fS2:Fields, tS:Types, tS1:Types, tS2:Types)
         pj (wellTypedExpr (cx, e1, TRECORD (fS ++ fS1) (tS ++ tS1)))
      && pj (wellTypedExpr (cx, e2, TRECORD (fS ++ fS2) (tS ++ tS2)))
      && length fS = length tS
      && toSet fS1 /\ toSet fS2 = empty
      => pj (wellTypedExpr (cx,
                            e1 <<< e2,
                            TRECORD (fS ++ fS1 ++ fS2) (tS ++ tS1 ++ tS2))))
    | exRestriction ->
      (fa (cx:Context, t:Type, r:Expression, e:Expression)
         pj (wellFormedType (cx, t \ r))
      && pj (wellTypedExpr (cx, e, t))
      && pj (theoreM (cx, r @ e))
      => pj (wellTypedExpr (cx, RESTRICT r e, t \ r)))
    | exChoice ->
      (fa (cx:Context, t:Type, q:Expression, e:Expression, t1:Type,
           v1:Variable, v2:Variable)
         pj (wellFormedType (cx, t / q))
      && pj (wellTypedExpr (cx, e, t --> t1))
      && pj (theoreM (cx, FAA (seq2 ((v1,t), (v2,t)))
                              (q @ PAIR (VAR v1) (VAR v2)
                               ==>
                               e @ VAR v1 == e @ VAR v2)))
      && v1 ~= v2
      && ~(v1 in? exprFreeVars e) && ~(v2 in? exprFreeVars e)
      => pj (wellTypedExpr (cx, CHOOSE q e, t/q --> t1)))
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
         pj (wellFormedType (cx, TRECORD fS tS))
      && length tS = length eS
      && (fa(i:Nat) i < length eS =>
            pj (wellTypedExpr (cx, eS elem i, tS elem i)))
      => pj (wellTypedExpr (cx, RECORD fS eS, TRECORD fS tS)))
    | exTuple ->
      (fa (cx:Context, tS:Types, eS:Expressions)
         pj (wellFormedType (cx, PRODUCT tS))
      && length tS = length eS
      && (fa(i:Nat) i < length eS =>
            pj (wellTypedExpr (cx, eS elem i, tS elem i)))
      => pj (wellTypedExpr (cx, TUPLE eS, PRODUCT tS)))
    | exAbstraction ->
      (fa (cx:Context, vS:Variables, tS:Types, bvS:BoundVariables,
           e:Expression, t:Type)
         length vS = length tS
      && bvS = zip (vS, tS)
      && pj (wellTypedExpr (cx ++ multiVarDecls bvS, e, t))
      => pj (wellTypedExpr (cx, FNN bvS e, PRODUCT tS --> t)))
    | exUniversal ->
      (fa (cx:Context, bvS:BoundVariables, e:Expression)
         pj (wellTypedExpr (cx ++ multiVarDecls bvS, e, BOOL))
      => pj (wellTypedExpr (cx, FAA bvS e, BOOL)))
    | exExistential ->
      (fa (cx:Context, bvS:BoundVariables, e:Expression)
         pj (wellTypedExpr (cx ++ multiVarDecls bvS, e, BOOL))
      => pj (wellTypedExpr (cx, EXX bvS e, BOOL)))
    | exExistential1 ->
      (fa (cx:Context, bvS:BoundVariables, e:Expression)
         pj (wellTypedExpr (cx ++ multiVarDecls bvS, e, BOOL))
      => pj (wellTypedExpr (cx, EXX1 bvS e, BOOL)))
    | exIfThenElse ->
      (fa (cx:Context, e0:Expression, e1:Expression, e2:Expression, t:Type,
           an1:AxiomName, an2:AxiomName)
         pj (wellTypedExpr (cx, e0, BOOL))
      && pj (wellTypedExpr (cx <| axioM (an1, empty,    e0), e1, t))
      && pj (wellTypedExpr (cx <| axioM (an2, empty, ~~ e0), e2, t))
      => pj (wellTypedExpr (cx, IF e0 e1 e2, t)))
    | exOpInstance ->
      (fa (cx:Context, o:Operation, tvS:TypeVariables, t:Type, tS:Types,
           tsbs:TypeSubstitution)
         pj (wellFormedContext cx)
      && opDeclaration (o, tvS, t) in? cx
      && (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS elem i)))
      && noRepetitions? tvS
      && length tvS = length tS
      && tsbs = FMap.fromSequences (tvS, tS)
      => pj (wellTypedExpr (cx, OPP o tS, typeSubstInType tsbs t)))
    | exEmbedder0 ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, i:Nat)
         pj (wellFormedType (cx, SUM cS t?S))
      && i < length cS
      && i < length t?S
      && t?S elem i = None
      => pj (wellTypedExpr (cx, EMBED (SUM cS t?S) (cS elem i), SUM cS t?S)))
    | exEmbedder1 ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, i:Nat, t:Type)
         pj (wellFormedType (cx, SUM cS t?S))
      && i < length cS
      && i < length t?S
      && t?S elem i = Some t
      => pj (wellTypedExpr
               (cx, EMBED (SUM cS t?S) (cS elem i), t --> SUM cS t?S)))
    | exCase ->
      (fa (cx:Context, e:Expression, n:PosNat, pS:Patterns, eS:Expressions,
           t:Type, t1:Type, caseMatches:Expressions, posCxS:FSeq Context,
           negCxS:FSeq Context, posAnS:FSeq AxiomName, negAnS:FSeq AxiomName)
         pj (wellTypedExpr (cx, e, t))
      && length pS = n
      && (fa(i:Nat) i < n =>
            pj (wellTypedPatt (cx, pS elem i, t)))
      && length caseMatches = n
      && (fa(i:Nat) i < n =>
            caseMatches elem i =
            EXX (pattBoundVars (pS elem i))
                (pattAssumptions (pS elem i, e)))
      && pj (theoreM (cx, disjoinAll caseMatches))
      && length posCxS = n
      && length posAnS = n
      && (fa(i:Nat) i < n =>
            posCxS elem i =
            multiVarDecls (pattBoundVars (pS elem i))
              <| axioM (posAnS elem i, empty, pattAssumptions (pS elem i, e)))
      && length negCxS = n
      && length negAnS = n
      && (fa(i:Nat) i < n =>
            (let conjuncts:Expressions = the (fn conjuncts ->
                 length conjuncts = i &&
                 (fa(j:Nat) j < i =>
                    conjuncts elem j = ~~ (caseMatches elem j))) in
             negCxS elem i =
             singleton (axioM (negAnS elem i, empty, conjoinAll conjuncts))))
      && length eS = n
      && (fa(i:Nat) i < n =>
            pj (wellTypedExpr (cx ++ (negCxS elem i) ++ (posCxS elem i),
                               eS elem i,
                               t1)))
      => pj (wellTypedExpr (cx, CASE e pS eS, t1)))
    | exRecursiveLet ->
      (* Since here we have defined unique existentials (`EXX1') to bind
      multiple variables, the expression of the rule here is actually simpler
      than in LD, where unique existentials can only bind one variable. *)
      (fa (cx:Context, vS:Variables, tS:Types, bvS:BoundVariables,
           eS:Expressions, n:PosNat, e:Expression, t:Type)
         length vS = n
      && length tS = n
      && bvS = zip (vS, tS)
      && length eS = n
      && pj (theoreM (cx, EXX1 bvS (TUPLE (map (VAR, vS)) == TUPLE eS)))
      && pj (wellTypedExpr (cx ++ multiVarDecls bvS, e, t))
      => pj (wellTypedExpr (cx, LETDEF bvS eS e, t)))
    | exNonRecursiveLet ->
      (fa (cx:Context, p:Pattern, e:Expression, e1:Expression, t:Type)
         pj (wellTypedExpr (cx, CASE e (singleton p) (singleton e1), t))
      => pj (wellTypedExpr (cx, LET p e e1, t)))
    | exEquivalentTypes ->
      (fa (cx:Context, e:Expression, t:Type, t1:Type)
         pj (wellTypedExpr (cx, e, t))
      && pj (typeEquivalence (cx, t, t1))
      => pj (wellTypedExpr (cx, e, t1)))
    | exAlphaAbstraction ->
      (fa (cx:Context, tS:Types, e:Expression, t:Type, i:Nat,
           oldVi:Variable, newVi:Variable, oldVS:Variables, newVS:Variables,
           oldBvS:BoundVariables, newBvS:BoundVariables, esbs:ExprSubstitution)
         length oldVS = length tS
      && oldBvS = zip (oldVS, tS)
      && pj (wellTypedExpr (cx, FNN oldBvS e, t))
      && i < length oldVS
      && oldVi = oldVS elem i
      && esbs = FMap.singleton (oldVi, VAR newVi)
      && ~(newVi in? toSet oldVS \/ exprFreeVars e \/ captVars oldVi e)
      && newVS = update (oldVS, i, newVi)
      && newBvS = zip (newVS, tS)
      => pj (wellTypedExpr (cx, FNN newBvS (exprSubst esbs e), t)))
    | exAlphaCase ->
      (fa (cx:Context, e:Expression, t:Type, i:Nat,
           oldPS:Patterns, newPS:Patterns, oldPi:Pattern, newPi:Pattern,
           oldV:Variable, newV:Variable, oldES:Expressions,
           newES:Expressions, oldEi:Expression, newEi:Expression,
           esbs:ExprSubstitution)
         pj (wellTypedExpr (cx, CASE e oldPS oldES, t))
      && i < length oldPS
      && oldPi = oldPS elem i
      && i < length oldES
      && oldEi = oldES elem i
      && oldV in? pattVars oldPi
      && esbs = FMap.singleton (oldV, VAR newV)
      && ~(newV in? pattVars oldPi \/ exprFreeVars oldEi \/ captVars oldV oldEi)
      && newPi = pattSubst (oldV, newV) oldPi
      && newPS = update (oldPS, i, newPi)
      && newEi = exprSubst esbs oldEi
      && newES = update (oldES, i, newEi)
      => pj (wellTypedExpr (cx, CASE e newPS newES, t)))
    | exAlphaRecursiveLet ->
      (fa (cx:Context, tS:Types, i:Nat, esbs:ExprSubstitution, t:Type,
           oldVi:Variable, newVi:Variable, oldVS:Variables, newVS:Variables,
           oldBvS:BoundVariables, newBvS:BoundVariables, oldE:Expression,
           newE:Expression, oldES:Expressions, newES:Expressions)
         length oldVS = length tS
      && oldBvS = zip (oldVS, tS)
      && pj (wellTypedExpr (cx, LETDEF oldBvS oldES oldE, t))
      && i < length oldVS
      && oldVi = oldVS elem i
      && esbs = FMap.singleton (oldVi, VAR newVi)
      && ~(newVi in? toSet oldVS \/ captVars oldVi oldE \/ exprFreeVars oldE \/
                     unionAll (map (exprFreeVars, oldES)) \/
                     unionAll (map (captVars oldVi, oldES)))
      && newVS = update (oldVS, i, newVi)
      && newBvS = zip (newVS, tS)
      && newES = map (exprSubst esbs, oldES)
      && newE = exprSubst esbs oldE
      => pj (wellTypedExpr (cx, LETDEF newBvS newES newE, t)))

    %%%%%%%%%% well-typed patterns:
    | paVariable ->
      (fa (cx:Context, t:Type, v:Variable)
         pj (wellFormedType (cx, t))
      && ~(v in? contextVars cx)
      => pj (wellTypedPatt (cx, PVAR (v,t), t)))
    | paEmbedding0 ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, i:Nat)
         pj (wellFormedType (cx, SUM cS t?S))
      && i < length cS
      && i < length t?S
      && t?S elem i = None
      => pj (wellTypedPatt (cx, PEMBE (SUM cS t?S) (cS elem i), SUM cS t?S)))
    | paEmbedding1 ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, p:Pattern, t:Type, i:Nat)
         pj (wellFormedType (cx, SUM cS t?S))
      && pj (wellTypedPatt (cx, p, t))
      && i < length cS
      && i < length t?S
      && t?S elem i = Some t
      => pj (wellTypedPatt (cx, PEMBED (SUM cS t?S) (cS elem i) p, SUM cS t?S)))
    | paRecord ->
      (fa (cx:Context, fS:Fields, tS:Types, pS:Patterns)
         pj (wellFormedType (cx, TRECORD fS tS))
      && length pS = length tS
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
      => pj (wellTypedPatt (cx, (v,t) AS p, t)))
    | paEquivalentTypes ->
      (fa (cx:Context, p:Pattern, t:Type, t1:Type)
         pj (wellTypedPatt (cx, p, t))
      && pj (typeEquivalence (cx, t, t1))
      => pj (wellTypedPatt (cx, p, t1)))

    %%%%%%%%%% theorems:
    | thAxiom ->
      (fa (cx:Context, an:AxiomName, tvS:TypeVariables, e:Expression, tS:Types,
           tsbs:TypeSubstitution)
         pj (wellFormedContext cx)
      && axioM (an, tvS, e) in? cx
      && (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS elem i)))
      && noRepetitions? tvS
      && length tvS = length tS
      && tsbs = FMap.fromSequences (tvS, tS)
      => pj (theoreM (cx, typeSubstInExpr tsbs e)))
    | thOpDef ->
      (fa (cx:Context, tvS:TypeVariables, o:Operation, e:Expression, tS:Types,
           tsbs:TypeSubstitution)
         pj (wellFormedContext cx)
      && opDefinition (o, tvS, e) in? cx
      && (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS elem i)))
      && noRepetitions? tvS
      && length tvS = length tS
      && tsbs = FMap.fromSequences (tvS, tS)
      => pj (theoreM (cx, OPP o tS == typeSubstInExpr tsbs e)))
    | thSubstitution ->
      (fa (cx:Context, oldE:Expression, e1:Expression, e2:Expression,
           newE:Expression, pos:Position)
         pj (theoreM (cx, oldE))
      && pj (theoreM (cx, e1 == e2))
      && exprSubstAt (oldE, e1, e2, pos, newE)
      && exprSubstAtOK? (oldE, e1, e2, pos)
      => pj (theoreM (cx, newE)))
    | thTypeSubstitution ->
      (fa (cx:Context, oldE:Expression, t1:Type, t2:Type, pos:Position,
           newE:Expression)
         pj (theoreM (cx, oldE))
      && pj (typeEquivalence (cx, t1, t2))
      && typeSubstInExprAt (oldE, t1, t2, pos, newE)
      => pj (theoreM (cx, newE)))
    | thBoolean ->
      (fa (cx:Context, e:Expression, v:Variable)
         pj (wellTypedExpr (cx, e, BOOL --> BOOL))
      && ~(v in? exprFreeVars e)
      => pj (theoreM (cx, e @ TRUE &&& e @ FALSE <==> FA (v,BOOL) e @ VAR v)))
    | thCongruence ->
      (fa (cx:Context, e1:Expression, e2:Expression, e:Expression,
           t:Type, t1:Type)
         pj (wellTypedExpr (cx, e1, t))
      && pj (wellTypedExpr (cx, e2, t))
      && pj (wellTypedExpr (cx, e, t --> t1))
      => pj (theoreM (cx, e1 == e2 ==> e @ e1 == e @ e2)))
    | thExtensionality ->
      (fa (cx:Context, e1:Expression, e2:Expression, t:Type, t1:Type, v:Variable)
         pj (wellTypedExpr (cx, e1, t --> t1))
      && pj (wellTypedExpr (cx, e2, t --> t1))
      && ~(v in? exprFreeVars e1 \/ exprFreeVars e2)
      => (pj (theoreM (cx, e1 == e2 <==>
                           FA (v,t) e1 @ VAR v == e2 @ VAR v))))
    | thAbstraction ->
      (fa (cx:Context, vS:Variables, tS:Types, bvS:BoundVariables, e:Expression,
           eS:Expressions, t:Type, esbs:ExprSubstitution,
           an1:AxiomName, an2:AxiomName)
         length vS = length tS
      && bvS = zip (vS, tS)
      && pj (wellTypedExpr (cx, FNN bvS e @ TUPLE eS, t))
      && noRepetitions? vS
      && length vS = length eS
      && esbs = FMap.fromSequences (vS, eS)
      && exprSubstOK? (e, esbs)
      => pj (theoreM (cx, FNN bvS e @ TUPLE eS == exprSubst esbs e)))
    | thIfThenElse ->
      (fa (cx:Context, e0:Expression, e1:Expression, e2:Expression,
           e:Expression, t:Type, an1:AxiomName, an2:AxiomName)
         pj (wellTypedExpr (cx, IF e0 e1 e2, t))
      && pj (theoreM (cx <| axioM (an1, empty,   e0), e1 == e))
      && pj (theoreM (cx <| axioM (an2, empty, ~~e0), e2 == e))
      => pj (theoreM (cx, IF e0 e1 e2 == e)))
    | thRecord ->
      (fa (cx:Context, fS:Fields, tS:Types, v:Variable, vS:Variables)
         pj (wellFormedType (cx, TRECORD fS tS))
      && noRepetitions? (v |> vS)
      && length vS = length tS
      => pj (theoreM (cx, FA (v, TRECORD fS tS)
                             (EXX1 (zip (vS, tS))
                                   (VAR v == RECORD fS (map (VAR, vS)))))))
    | thTuple ->
      (fa (cx:Context, tS:Types, v:Variable, vS:Variables)
         pj (wellFormedType (cx, PRODUCT tS))
      && noRepetitions? (v |> vS)
      && length vS = length tS
      => pj (theoreM (cx, FA (v, PRODUCT tS)
                             (EXX1 (zip (vS, tS))
                                   (VAR v == TUPLE (map (VAR, vS)))))))
    | thRecordProjection ->
      (fa (cx:Context, fS:Fields, tS:Types, eS:Expressions, i:Nat)
         pj (wellTypedExpr (cx, RECORD fS eS, TRECORD fS tS))
      && i < length fS
      && i < length eS
      => pj (theoreM (cx, (RECORD fS eS) DOTr (fS elem i) == (eS elem i))))
    | thTupleProjection ->
      (fa (cx:Context, tS:Types, eS:Expressions, i:Nat)
         pj (wellTypedExpr (cx, TUPLE eS, PRODUCT tS))
      && i < length eS
      => pj (theoreM (cx, (TUPLE eS) DOTt (i+1) == (eS elem i))))
    | thRecordUpdate1 ->
      (fa (cx:Context, fS1:Fields, fS2:Fields, tS1:Types, tS2:Types,
           eS1:Expressions, eS2:Expressions, i:Nat)
         pj (wellTypedExpr (cx, RECORD fS1 eS1, TRECORD fS1 tS1))
      && pj (wellTypedExpr (cx, RECORD fS2 eS2, TRECORD fS2 tS2))
      && i < length fS1
      && i < length eS1
      && ~((fS1 elem i) in? fS2)
      && pj (theoreM (cx,
                      (RECORD fS1 eS1 <<< RECORD fS2 eS2) DOTr (fS1 elem i)
                      == (eS1 elem i))))
    | thRecordUpdate2 ->
      (fa (cx:Context, fS1:Fields, fS2:Fields, tS1:Types, tS2:Types,
           eS1:Expressions, eS2:Expressions, i:Nat)
         pj (wellTypedExpr (cx, RECORD fS1 eS1, TRECORD fS1 tS1))
      && pj (wellTypedExpr (cx, RECORD fS2 eS2, TRECORD fS2 tS2))
      && i < length fS2
      && i < length eS2
      => pj (theoreM (cx,
                      (RECORD fS1 eS1 <<< RECORD fS2 eS2) DOTr (fS2 elem i)
                      == (eS2 elem i))))
    | thEmbedderSurjective ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, v:Variable, v1:Variable,
           disjuncts:Expressions)
         pj (wellFormedType (cx, SUM cS t?S))
      && length cS = length t?S
      && length disjuncts = length cS
      && v ~= v1
      && (fa(i:Nat) i < length disjuncts =>
            disjuncts elem i =
            (case (t?S elem i) of
               | Some t -> EX (v1,t)
                              (VAR v == EMBED (SUM cS t?S) (cS elem i) @ VAR v1)
               | None   -> VAR v == EMBED (SUM cS t?S) (cS elem i)))
      => pj (theoreM (cx, FA (v, SUM cS t?S) (disjoinAll disjuncts))))
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
              FAA (seq2 ((vi,ti), (vj,tj)))
                  (EMBED (SUM cS t?S) (cS elem i) @ VAR vi ~==
                   EMBED (SUM cS t?S) (cS elem j) @ VAR vj)
            | (Some ti, None) ->
              FA (vi, ti) (EMBED (SUM cS t?S) (cS elem i) @ VAR vi ~==
                           EMBED (SUM cS t?S) (cS elem j))
            | (None, Some tj) ->
              FA (vj, tj) (EMBED (SUM cS t?S) (cS elem i) ~==
                           EMBED (SUM cS t?S) (cS elem j) @ VAR vj)
            | (None, None) ->
              EMBED (SUM cS t?S) (cS elem i) ~== EMBED (SUM cS t?S) (cS elem j))
      => pj (theoreM (cx, conclusion)))
    | thEmbedderInjective ->
      (fa (cx:Context, cS:Constructors, t?S:Type?s, v1:Variable, v2:Variable,
           i:Nat, ti:Type)
         pj (wellFormedType (cx, SUM cS t?S))
      && i < length cS
      && i < length t?S
      && t?S elem i = Some ti
      && v1 ~= v2
      => pj (theoreM (cx, FAA (seq2 ((v1,ti), (v2,ti)))
                              (VAR v1 ~== VAR v2 ==>
                               EMBED (SUM cS t?S) (cS elem i) @ VAR v1 ~==
                               EMBED (SUM cS t?S) (cS elem i) @ VAR v2))))
    | thRelaxatorSatisfiesPredicate ->
      (fa (cx:Context, t:Type, r:Expression, v:Variable)
         pj (wellFormedType (cx, t \ r))
      => pj (theoreM (cx, FA (v,t\r) (r @ (RELAX r @ VAR v)))))
    | thRelaxatorInjective ->
      (fa (cx:Context, t:Type, r:Expression, v1:Variable, v2:Variable)
         pj (wellFormedType (cx, t \ r))
      && v1 ~= v2
      => pj (theoreM (cx, FAA (seq2 ((v1,t\r), (v2,t\r)))
                              (VAR v1 ~== VAR v2 ==>
                               RELAX r @ VAR v1 ~== RELAX r @ VAR v2))))
    | thRelexatorSurjective ->
      (fa (cx:Context, t:Type, r:Expression, v:Variable, v1:Variable)
         pj (wellFormedType (cx, t \ r))
      && v ~= v1
      => pj (theoreM (cx, FA (v,t)
                             (r @ VAR v ==>
                              EX (v1,t\r) (VAR v == RELAX r @ VAR v1)))))
    | thRestriction ->
      (fa (cx:Context, t:Type, r:Expression, v:Variable)
         pj (wellFormedType (cx, t \ r))
      => pj (theoreM (cx, FA (v,t\r) (RESTRICT r (RELAX r @ VAR v) == VAR v))))
    | thQuotienterSurjective ->
      (fa (cx:Context, t:Type, q:Expression, v:Variable, v1:Variable)
         pj (wellFormedType (cx, t / q))
      && v ~= v1
      => pj (theoreM (cx, FA (v,t/q) (EX (v1,t) (QUOTIENT q @ VAR v1 == VAR v)))))
    | thQuotienterEquivClass ->
      (fa (cx:Context, t:Type, q:Expression, v1:Variable, v2:Variable)
         pj (wellFormedType (cx, t / q))
      && v1 ~= v2
      => pj (theoreM (cx, FAA (seq2 ((v1,t), (v2,t)))
                              (q @ PAIR (VAR v1) (VAR v2) <==>
                               QUOTIENT q @ VAR v1 == QUOTIENT q @ VAR v2))))
    | thChoice ->
      (fa (cx:Context, t:Type, t1:Type, q:Expression, e:Expression, v:Variable)
         pj (wellTypedExpr (cx, CHOOSE q e, t/q --> t1))
      && ~(v in? exprFreeVars e)
      => pj (theoreM (cx, FA (v,t)
                             (CHOOSE q e @ (QUOTIENT q @ VAR v) == e @ VAR v))))
    | thCase ->
      (fa (cx:Context, e:Expression, n:Nat, pS:Patterns, eS:Expressions,
           t:Type, posCxS:FSeq Context, negCxS:FSeq Context, e0:Expression,
           posAnS:FSeq AxiomName, negAnS:FSeq AxiomName)
         pj (wellTypedExpr (cx, CASE e pS eS, t))
      && length pS = n
      && length posCxS = n
      && length posAnS = n
      && (fa(i:Nat) i < n =>
            posCxS elem i =
            multiVarDecls (pattBoundVars (pS elem i))
              <| axioM (posAnS elem i, empty, pattAssumptions (pS elem i, e)))
      && length negCxS = n
      && length negAnS = n
      && (fa(i:Nat) i < n =>
            (let conjuncts:Expressions = the (fn conjuncts ->
                 length conjuncts = i &&
                 (fa(j:Nat) j < i =>
                    conjuncts elem j =
                    FAA (pattBoundVars (pS elem i))
                        (pattAssumptions (pS elem i, e)))) in
             negCxS elem i =
             singleton (axioM (negAnS elem i, empty, conjoinAll conjuncts))))
      && length eS = n
      && (fa(i:Nat) i < n =>
            pj (theoreM (cx ++ (negCxS elem i) ++ (posCxS elem i),
                         (eS elem i) == e0)))
      && (fa(i:Nat) i < n =>
            exprFreeVars e0 /\ pattVars (pS elem i) = empty)
      => pj (theoreM (cx, CASE e pS eS == e0)))
    | thRecursiveLet ->
      (fa (cx:Context, vS:Variables, tS:Types, bvS:BoundVariables, eS:Expressions,
           n:Nat, e:Expression, t:Type, e0:Expression, conjuncts:Expressions,
           an:AxiomName)
         length vS = n
      && length tS = n
      && bvS = zip (vS, tS)
      && pj (wellTypedExpr (cx, LETDEF bvS eS e, t))
      && length eS = n
      && length conjuncts = n
      && (fa(i:Nat) i < n =>
            conjuncts elem i =
            (VAR (vS elem i) == (eS elem i)))
      && pj (theoreM (cx ++ multiVarDecls bvS
                        <| axioM (an, empty, conjoinAll conjuncts),
                      e == e0))
      && toSet vS /\ exprFreeVars e0 = empty
      => pj (theoreM (cx, LETDEF bvS eS e == e0)))
    | thAbbrevTrue ->
      (fa (cx:Context, v:Variable)
         pj (wellFormedContext cx)
      => pj (theoreM (cx, TRUE <==> FN (v,BOOL) (VAR v) == FN (v,BOOL) (VAR v))))
    | thAbbrevFalse ->
      (fa (cx:Context, v:Variable)
         pj (wellFormedContext cx)
      => pj (theoreM (cx, FALSE <==> FN (v,BOOL) (VAR v) == FN (v,BOOL) TRUE)))
    | thAbbrevNegation ->
      (fa (cx:Context, e:Expression)
         pj (wellTypedExpr (cx, ~~e, BOOL))
      => pj (theoreM (cx, ~~e <==> IF e FALSE TRUE)))
    | thAbbrevInequation ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 ~== e2, BOOL))
      => pj (theoreM (cx, (e1 ~== e2) <==> ~~(e1 == e2))))
    | thAbbrevConjunction ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 &&& e2, BOOL))
      => pj (theoreM (cx, e1 &&& e2 <==> IF e1 e2 FALSE)))
    | thAbbrevDisjunction ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 ||| e2, BOOL))
      => pj (theoreM (cx, e1 ||| e2 <==> IF e1 TRUE e2)))
    | thAbbrevImplication ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 ==> e2, BOOL))
      => pj (theoreM (cx, e1 ==> e2 <==> IF e1 e2 TRUE)))
    | thAbbrevEquivalence ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (wellTypedExpr (cx, e1 <==> e2, BOOL))
      => pj (theoreM (cx, (e1 <==> e2) == (e1 == e2))))
    | thAbbrevUniversal ->
      (fa (cx:Context, bvS:BoundVariables, e:Expression)
         pj (wellTypedExpr (cx, FAA bvS e, BOOL))
      => pj (theoreM (cx, FAA bvS e <==> FNN bvS e == FNN bvS TRUE)))
    | thAbbrevExistential ->
      (fa (cx:Context, bvS:BoundVariables, e:Expression)
         pj (wellTypedExpr (cx, EXX bvS e, BOOL))
      => pj (theoreM (cx, EXX bvS e <==> ~~(FAA bvS (~~e)))))
    | thAbbrevExistential1 ->
      (fa (cx:Context, vS:Variables, tS:Types, bvS:BoundVariables, e:Expression,
           vS1:Variables, bvS1:BoundVariables, esbs:ExprSubstitution)
         length vS = length tS
      && bvS = zip (vS, tS)
      && pj (wellTypedExpr (cx, EXX1 bvS e, BOOL))
      && length vS1 = length vS
      && noRepetitions? vS
      && esbs = FMap.fromSequences (vS, map (VAR, vS1))
      && bvS1 = zip (vS1, tS)
      && toSet vS /\ toSet vS1 = empty
      && exprSubstOK? (e, esbs)
      => pj (theoreM (cx, EXX1 bvS e <==>
                          EXX bvS (e &&&
                                   FAA bvS1 (exprSubst esbs e ==>
                                             TUPLE (map (VAR, vS)) ==
                                             TUPLE (map (VAR, vS1)))))))
    | thAbbrevNonRecursiveLet ->
      (fa (cx:Context, p:Pattern, e:Expression, e1:Expression, t:Type)
         pj (wellTypedExpr (cx, LET p e e1, t))
      => pj (theoreM (cx, LET p e e1 == CASE e (singleton p) (singleton e1))))


  op provable? : Predicate Judgement
  def provable? = min (fn provable? ->
    (fa(ir:InferenceRule) satisfiesRule? provable? ir))

  type ProvableJudgement = (Judgement | provable?)

endspec
