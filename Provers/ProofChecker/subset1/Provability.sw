spec

  import SyntaxWithCoreOps


  type InferenceRule =
    % well-formed contexts:
    | cxEmpty
    | cxTypeDecl
    | cxOpDecl
    | cxTypeDef
    | cxOpDef
    | cxAxiom
    | cxVarDecl
    % well-formed specs:
    | speC
    % well-formed types:
    | tyBoolean
    | tyNamed
    | tyArrow
    % type equivalence:
    | tyEqDef
    | tyEqReflexive
    | tyEqSymmetric
    | tyEqTransitive
    | tyEqSubstitution
    % well-typed expressions:
    | exVariable
    | exOp
    | exApplication
    | exEquation
    | exAbstraction
    | exEquivalentTypes
    | exAlphaAbstraction
    % theorems:
    | thAxiom
    | thOpDef
    | thSubstitution
    | thTypeSubstitution
    | thBoolean
    | thCongruence
    | thExtensionality
    | thAbstraction


  op satisfiesInferenceRule? : (Judgement -> Boolean) -> InferenceRule -> Boolean
  def satisfiesRule? pj = fn

    %%%%%%%%%% well-formed contexts:
    | cxEmpty ->
      pj (wellFormedContext empty)
    | cxTypeDecl ->
      (fa (cx:Context, tn:TypeName)
         pj (wellFormedContext cx)
      && ~(tn in? contextTypes cx)
      => pj (wellFormedContext (cx <| typeDeclaration tn)))
    | cxOpDecl ->
      (fa (cx:Context, o:Operation, t:Type)
         pj (wellFormedContext cx)
      && ~(o in? contextOps cx)
      && pj (wellFormedType (cx, t))
      => pj (wellFormedContext (cx <| opDeclaration (o, t))))
    | cxTypeDef ->
      (fa (cx:Context, tn:TypeName, t:Type)
         pj (wellFormedContext cx)
      && typeDeclaration tn in? cx
      && ~(contextDefinesType? (cx, tn))
      && pj (wellFormedType (cx, t))
      => pj (wellFormedContext (cx <| typeDefinition (tn, t))))
    | cxOpDef ->
      (fa (cx:Context, o:Operation, t:Type,
           v:VariableNotV, e:Expression, e1:Expression)
         pj (wellFormedContext cx)
      && opDeclaration (o, t) in? cx
      && ~(contextDefinesOp? (cx, o))
      && pj (theoreM (cx, EX1 v t (VAR v == e)))
      && ~(o in? exprOps e)
      && e1 = exprSubst1 v (opp o) e
      => pj (wellFormedContext (cx <| opDefinition (o, e1))))
    | cxAxiom ->
      (fa (cx:Context, e:Expression, an:AxiomName)
         pj (wellFormedContext cx)
      && pj (wellTypedExpr (cx, e, BOOL))
      && ~(an in? contextAxioms cx)
      => pj (wellFormedContext (cx <| axioM (an, e))))
    | cxVarDecl ->
      (fa (cx:Context, v:Variable, t:Type)
         pj (wellFormedContext cx)
      && ~(v in? contextVars cx)
      && pj (wellFormedType (cx, t))
      => pj (wellFormedContext (cx <| varDeclaration (v, t))))

    %%%%%%%%%% well-formed specs:
    | speC ->
      (fa (sp:Spec)
         pj (wellFormedContext sp)
      => pj (wellFormedSpec sp))

    %%%%%%%%%% well-formed types:
    | tyBoolean ->
      (fa (cx:Context)
         pj (wellFormedContext cx)
      => pj (wellFormedType (cx, BOOL)))
    | tyNamed ->
      (fa (cx:Context, tn:TypeName)
         pj (wellFormedContext cx)
      && typeDeclaration tn in? cx
      => pj (wellFormedType (cx, TYP tn)))
    | tyArrow ->
      (fa (cx:Context, t1:Type, t2:Type)
         pj (wellFormedType (cx, t1))
      && pj (wellFormedType (cx, t2))
      => pj (wellFormedType (cx, t1 --> t2)))

    %%%%%%%%%% type equivalence:
    | tyEqDef ->
      (fa (cx:Context, tn:TypeName, t:Type)
         pj (wellFormedContext cx)
      && typeDefinition (tn, t) in? cx
      => pj (typeEquivalence (cx, TYP tn, t)))
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
      (fa (cx:Context, oldT:Type, t1:Type, t2:Type, pos:Position, newT:Type)
         pj (wellFormedType (cx, oldT))
      && pj (typeEquivalence (cx, t1, t2))
      && isTypeSubstInTypeAt? (oldT, t1, t2, pos, newT)
      => pj (typeEquivalence (cx, oldT, newT)))

    %%%%%%%%%% well-typed expressions:
    | exVariable ->
      (fa (cx:Context, v:Variable, t:Type)
         pj (wellFormedContext cx)
      && varDeclaration (v,t) in? cx
      => pj (wellTypedExpr (cx, VAR v, t)))
    | exOpInstance ->
      (fa (cx:Context, o:Operation, t:Type)
         pj (wellFormedContext cx)
      && opDeclaration (o, t) in? cx
      => pj (wellTypedExpr (cx, OP o, t)))
    | exApplication ->
      (fa (cx:Context, e1:Expression, e2:Expression, t1:Type, t2:Type)
         pj (wellTypedExpr (cx, e1, t1 --> t2))
      && pj (wellTypedExpr (cx, e2, t1))
      => pj (wellTypedExpr (cx, e1 @ e2, t2)))
    | exAbstraction ->
      (fa (cx:Context, v:Variable, t:Type, e:Expression, t1:Type)
         pj (wellTypedExpr (cx <| varDeclaration (v, t), e, t1))
      => pj (wellTypedExpr (cx, FN v t e, t --> t1)))
    | exEquation ->
      (fa (cx:Context, e1:Expression, e2:Expression, t:Type)
         pj (wellTypedExpr (cx, e1, t))
      && pj (wellTypedExpr (cx, e2, t))
      => pj (wellTypedExpr (cx, e1 == e2, BOOL)))
    | exEquivalentTypes ->
      (fa (cx:Context, e:Expression, t:Type, t1:Type)
         pj (wellTypedExpr (cx, e, t))
      && pj (typeEquivalence (cx, t, t1))
      => pj (wellTypedExpr (cx, e, t1)))
    | exAlphaAbstraction ->
      (fa (cx:Context, t:Type, e:Expression, t1:Type,
           oldV:Variable, newV:Variable)
         pj (wellTypedExpr (cx, FN oldV t e, t1))
      && newV ~= oldV
      && ~(newV in? exprFreeVars e \/ captVars oldV e)
      => pj (wellTypedExpr (cx, FN newV t (exprSubst1 oldV (VAR newV) e), t1)))

    %%%%%%%%%% theorems:
    | thAxiom ->
      (fa (cx:Context, an:AxiomName, e:Expression)
         pj (wellFormedContext cx)
      && axioM (an, e) in? cx
      => pj (theoreM (cx, e)))
    | thOpDef ->
      (fa (cx:Context, o:Operation, e:Expression)
         pj (wellFormedContext cx)
      && opDefinition (o, e) in? cx
      => pj (theoreM (cx, OP o == e)))
    | thSubstitution ->
      (fa (cx:Context, oldE:Expression, e1:Expression, e2:Expression,
           newE:Expression, pos:Position)
         pj (theoreM (cx, oldE))
      && pj (theoreM (cx, e1 == e2))
      && isExprSubstAt? (oldE, e1, e2, pos, newE)
      && exprSubstAtOK? (oldE, e1, e2, pos)
      => pj (theoreM (cx, newE)))
    | thTypeSubstitution ->
      (fa (cx:Context, oldE:Expression, t1:Type, t2:Type, pos:Position,
           newE:Expression)
         pj (theoreM (cx, oldE))
      && pj (typeEquivalence (cx, t1, t2))
      && isTypeSubstInExprAt? (oldE, t1, t2, pos, newE)
      => pj (theoreM (cx, newE)))
    | thBoolean ->
      (fa (cx:Context, e:Expression, v:Variable)
         pj (wellTypedExpr (cx, e, BOOL --> BOOL))
      && ~(v in? exprFreeVars e)
      => pj (theoreM (cx, e @ TRUE &&& e @ FALSE <==> FA v BOOL (e @ VAR v))))
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
                           FA v t (e1 @ VAR v == e2 @ VAR v)))))
    | thAbstraction ->
      (fa (cx:Context, v:Variable, t:Type, e:Expression,
           e1:Expression, t1:Type, esbs:ExprSubstitution)
         pj (wellTypedExpr (cx, FN v t e @ e1, t1))
      && esbs = single v e1
      && exprSubstOK? (e, esbs)
      => pj (theoreM (cx, FN v t e @ e1 == exprSubst esbs e)))


  op provable? : Judgement -> Boolean
  def provable? = min (fn provable? ->
    (fa(ir:InferenceRule) satisfiesRule? provable? ir))

  type ProvableJudgement = (Judgement | provable?)

endspec
