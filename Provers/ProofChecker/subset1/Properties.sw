spec

  import Provability

  conjecture exTrue is
    fa (cx:Context)
      provable? (wellFormedContext cx)
   => provable? (wellTypedExpr (cx, TRUE, BOOL))

  conjecture exFalse is
    fa (cx:Context)
      provable? (wellFormedContext cx)
   => provable? (wellTypedExpr (cx, FALSE, BOOL))

  conjecture exNegation is
    fa (cx:Context, e:Expression)
      provable? (wellTypedExpr (cx, e, BOOL))
   => provable? (wellTypedExpr (cx, ~~ e, BOOL))

  conjecture exConjunction is
    fa (cx:Context, e1:Expression, e2:Expression)
      provable? (wellTypedExpr (cx, e1, BOOL))
   && provable? (wellTypedExpr (cx, e2, BOOL))
   => provable? (wellTypedExpr (cx, e1 &&& e2, BOOL))

  conjecture exDisjunction is
    fa (cx:Context, e1:Expression, e2:Expression)
      provable? (wellTypedExpr (cx, e1, BOOL))
   && provable? (wellTypedExpr (cx, e2, BOOL))
   => provable? (wellTypedExpr (cx, e1 ||| e2, BOOL))

  conjecture exImplication is
    fa (cx:Context, e1:Expression, e2:Expression)
      provable? (wellTypedExpr (cx, e1, BOOL))
   && provable? (wellTypedExpr (cx, e2, BOOL))
   => provable? (wellTypedExpr (cx, e1 ==> e2, BOOL))

  conjecture exEquivalence is
    fa (cx:Context, e1:Expression, e2:Expression)
      provable? (wellTypedExpr (cx, e1, BOOL))
   && provable? (wellTypedExpr (cx, e2, BOOL))
   => provable? (wellTypedExpr (cx, e1 <==> e2, BOOL))

  conjecture exUniversal is
    fa (cx:Context, v:Variable, t:Type, e:Expression)
      provable? (wellTypedExpr (cx <| varDeclaration (v, t), e, BOOL))
   => provable? (wellTypedExpr (cx, FA v t e, BOOL))

  conjecture exExistential is
    fa (cx:Context, v:Variable, t:Type, e:Expression)
      provable? (wellTypedExpr (cx <| varDeclaration (v, t), e, BOOL))
   => provable? (wellTypedExpr (cx, EX v t e, BOOL))

  conjecture exExistential1 is
    fa (cx:Context, v:VariableNotV, t:Type, e:Expression)
      provable? (wellTypedExpr (cx <| varDeclaration (v, t), e, BOOL))
   => provable? (wellTypedExpr (cx, EX1 v t e, BOOL))


  % many more here...
    
endspec
