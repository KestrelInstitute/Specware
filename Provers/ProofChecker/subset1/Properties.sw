spec

  import Provability

  % can rename v to fresh v' in any proof

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

  conjecture swapVarDecls is  % OK
    fa(cx1,cx2,preCx,postCx,v1,t1,v2,t2)
      cx1 = preCx <| varDeclaration(v1,t1) ++ varDeclaration(v2,t2) |> postCx &&
      cx2 = preCx <| varDeclaration(v2,t2) ++ varDeclaration(v1,t1) |> postCx =>
      (wfCx cx1 => wfCx cx2)
      &&
      (fa(t) wfTy cx1 t => wfTy cx2 t)
      &&
      (fa(t1,t2) tyEq cx1 t1 t2 => tyEq cx2 t1 t2)
      &&
      (fa(e,t) wtEx cx1 e t => wtEx cx2 e t)
      &&
      (fa(e) theo cx1 e => theo cx2 e)

  conjecture canAddVarDecl is  % OK
    fa(cx,v,t)
      wfCx (cx <| varDeclaration(v,t))
      =>
      (fa(t1) wfTy cx t1 => wfTy (cx <| varDeclaration(v,t)) t1)
      &&
      (fa(t1,t2) tyEq cx t1 t2 => tyEq (cx <| varDeclaration(v,t)) t1 t2)
      &&
      (fa(e,t1) wtEx cx e t1 => wtEx (cx <| varDeclaration(v,t)) e t1)
      &&
      (fa(e) theo cx e => theo (cx <| varDeclaration(v,t)) e)

  conjecture exConjunction is  % OK
    fa(cx,e1,e2) wtEx cx e1 BOOL && wtEx cx e2 BOOL => wtEx cx (e1 &&& e2) BOOL

  conjecture exDisjunction is  % OK
    fa(cx,e1,e2) wtEx cx e1 BOOL && wtEx cx e2 BOOL => wtEx cx (e1 ||| e2) BOOL

  conjecture exImplication is  % OK
    fa(cx,e1,e2) wtEx cx e1 BOOL && wtEx cx e2 BOOL => wtEx cx (e1 ==> e2) BOOL

  conjecture exEquivalence is  % OK
    fa(cx,e1,e2) wtEx cx e1 BOOL && wtEx cx e2 BOOL => wtEx cx (e1 <==> e2) BOOL

  conjecture exExistential1 is  % OK
    fa(cx,v,t,e)
      wtEx (cx <| varDeclaration(v,t)) e BOOL => wtEx cx (EX1 v t e) BOOL

  conjecture wellFormedTypeMonotonic is  % OK
    fa(cx1,cx2,t) wfTy cx1 t && wfCx (cx1 ++ cx2) => wfTy (cx1 ++ cx2) t

  conjecture equivalentTypesAreWellFormed is  % OK
    fa(cx,t1,t2)
      tyEq cx t1 t2 => wfTy cx t1 && wfTy cx t2

  % more...

endspec
