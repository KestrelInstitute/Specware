spec

  import Provability

  conjecture exTrue is  % OK
    fa(cx) wfCx cx => wtEx cx TRUE BOOL

  conjecture exFalse is  % OK
    fa(cx) wfCx cx => wtEx cx FALSE BOOL

  conjecture exNegation is  % OK
    fa(cx,e) wtEx cx e BOOL => wtEx cx (~~ e) BOOL

  conjecture alwaysWellFormedContext is  % OK
    (fa(cx,t) wfTy cx t          => wfCx cx)
    &&
    (fa(cx,t1,t2) tyEq cx t1 t2 => wfCx cx)
    &&
    (fa(cx,e,t) wtEx cx e t     => wfCx cx)
    &&
    (fa(cx,e) theo cx e           => wfCx cx)

  conjecture exUniversal is  % OK
    fa(cx,v,t,e)
      wtEx (cx <| varDeclaration(v,t)) e BOOL => wtEx cx (FA v t e) BOOL

  conjecture exExistential is  % OK
    fa(cx,v,t,e)
      wtEx (cx <| varDeclaration(v,t)) e BOOL => wtEx cx (EX v t e) BOOL

  conjecture deleteVarWellFormedType is  % OK
    fa(cx,v,t,t1)
      wfTy (cx <| varDeclaration(v,t)) t1 <=> wfTy cx t1

  conjecture swapVarDecls is
    fa(cx1,cx2,preCx,postCx,v1,t1,v2,t2)
      cx1 = preCx <| varDeclaration(v1,t1) ++ varDeclaration(v2,t2) |> postCx &&
      cx2 = preCx <| varDeclaration(v2,t2) ++ varDeclaration(v1,t1) |> postCx =>
      (wfCx cx1 => wfCx cx2)  % OK
      &&
      (fa(t) wfTy cx1 t => wfTy cx2 t)
      &&
      (fa(t1,t2) tyEq cx1 t1 t2 => tyEq cx2 t1 t2)
      &&
      (fa(e,t) wtEx cx1 e t => wtEx cx2 e t)
      &&
      (fa(e) theo cx1 e => theo cx2 e)



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

  conjecture exExistential1 is
    fa (cx:Context, v:Variable, t:Type, e:Expression)
      provable? (wellTypedExpr (cx <| varDeclaration (v, t), e, BOOL))
   => provable? (wellTypedExpr (cx, EX1 v t e, BOOL))


  % many more here...
    
endspec
