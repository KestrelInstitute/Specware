(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec

  import Monad
  import ../DPGen/Inequality

%  op hdVar: Poly -> Var
%  def hdVar(poly) =
%    var(hdTerm(poly))

  op ineq: Proof -> Ineq
  def ineq(p) =
    if axiomIR?(p)
      then ineq(p)
    else if normIR?(p)
      then
	pIneq(p)
    else if chainNZIR?(p)
      then
	let i0 = ineq(p1(p)) in
	let i1 = ineq(p2(p)) in
	chainNZ(i0, i1, p1Mult(p), p2Mult(p))
    else if chainNEQIR?(p)
      then
	let i0 = ineq(p1(p)) in
	let i1 = ineq(p2(p)) in
	chainNEQ(i0, i1, p1Mult(p), p2Mult(p))
    else if chainZIR?(p)
      then
	let i0 = ineq(p1(p)) in
	let i1 = ineq(p2(p)) in
	chainZ(i0, i1, p1Mult(p), p2Mult(p))
    else %if narrowIntIR(p) then
	let i0 = ineq(p1(p)) in
	narrowInt(i0)

  op chainNZ: Ineq * Ineq * Coef * Coef -> Ineq
  op chainZ: Ineq * Ineq * Coef * Coef -> Ineq
  op chainNEQ: Ineq * Ineq * Coef * Coef -> Ineq
  op narrowInt: Ineq -> Ineq

  op polyMinusPoly: Poly * Poly -> Poly
  def polyMinusPoly(p1, p2) =
    polyPlusPoly(p1, negatePoly(p2))

  op negatePoly: Poly -> Poly
  def negatePoly (p) =
    coefTimesPoly(minusOne, p)

  op checkProof: Proof -> Bool
  def checkProof(p) =
    let checkRes = run check p in
    case checkRes of
      | RETURN res ->
      if res = contradictIneqGt ||
	res = contradictIneqGtEq ||
	res = contradictIneqGtZero
	then true
	else
	  fail("fmCheck proof doesn't check")
      | _ -> fail("fmCheck")
  
  op check: Proof -> Check.M Ineq
  def check(p) =
    if axiomIR?(p)
      then return (pIneq(p))
    else if normIR?(p)
      then
	checkNormIR(p)
    else if chainNZIR?(p)
      then
	checkChainNZIR(p)
    else if chainNEQIR?(p)
      then
	checkChainNEQIR(p)
    else if chainZIR?(p)
      then
	checkChainZIR(p)
    else %if narrowIntIR(p) then
      checkNarrowIntIR(p)


  op checkNormIR: Proof -> Check.M Ineq
  def checkNormIR(p) =
    let p1 = p1(p) in
    {
     i1 <- check(p1);
     let comp = compPred(i1) in
     let p = poly(i1) in
     let normP = normalize(p) in
     let res = mkNormIneq(comp, normP) in
     return res
     }

  op checkChainNZIR: Proof -> Check.M Ineq
  def checkChainNZIR(p) =
    let p1 = p1(p) in
    let p2 = p2(p) in
    let c1 = p1Mult(p) in
    let c2 = p2Mult(p) in
    {
     i1 <- check(p1);
     poly1 <- return(poly(i1));
     i2 <- check(p2);
     poly2 <- return(poly(i2));
     hdVarI1 <- return(hdVar(poly1));
     hdVarI2 <- return(hdVar(poly2));
     newPoly <- return (polyPlusPoly(coefTimesPoly(c1, poly1), coefTimesPoly(c2, poly2)));
     newI <- return(mkIneq(GtEq, newPoly));
     newHdVar <- return(hdVar(newPoly));
     if hdVarI1 = hdVarI2  && compPred(i1) = compPred(i2) && compPred(i1) = GtEq
       && hdVarI1 ~= newHdVar
       then return newI
     else throw "Error ChainNZ"
     }

  op checkChainNEQIR: Proof -> Check.M Ineq
  def checkChainNEQIR(p) =
    let p1 = p1(p) in
    let p2 = p2(p) in
    let c1 = p1Mult(p) in
    let c2 = p2Mult(p) in
    {
     i1 <- check(p1);
     poly1 <- return(poly(i1));
     i2 <- check(p2);
     poly2 <- return(poly(i2));
     hdVarI1 <- return(hdVar(poly1));
     hdVarI2 <- return(hdVar(poly2));
     newPoly <- return (polyPlusPoly(coefTimesPoly(c1, poly1), coefTimesPoly(c2, poly2)));
     newI <- return(mkIneq(Gt, coefTimesPoly(c1, poly1)));
     if Poly.zero?(newPoly) && hdVarI1 = hdVarI2  && compPred(i1) = compPred(i2) && compPred(i1) = GtEq
       then return newI
     else throw "Error ChainNEQ"
     }


  op checkChainZIR: Proof -> Check.M Ineq
  def checkChainZIR(p) =
    let p1 = p1(p) in
    let p2 = p2(p) in
    let c1 = p1Mult(p) in
    let c2 = p2Mult(p) in
    {
     i1 <- check(p1);
     poly1 <- return(poly(i1));
     i2 <- check(p2);
     poly2 <- return(poly(i2));
     hdVarI1 <- return(hdVar(poly1));
     hdVarI2 <- return(hdVar(poly2));
     newPoly <- return (polyPlusPoly(coefTimesPoly(c1, poly1), coefTimesPoly(c2, poly2)));
     newI <- return(mkIneq(Eq, coefTimesPoly(c1, poly1)));
     if Poly.zero?(newPoly) && hdVarI1 = hdVarI2  && compPred(i1) = compPred(i2) && compPred(i1) = GtEq
       then return newI
     else throw "Error ChainZ"
     }


  op checkNarrowIntIR: Proof -> Check.M Ineq
  def checkNarrowIntIR(p) =
    let p1 = p1(p) in
    {
     i1 <- check(p1);
     poly1 <- return(poly(i1));
     newPoly <- return (polyMinusOne(poly1));
     newI <- return(mkIneq(GtEq, newPoly));
     if compPred(i1) = Gt
       then return newI
     else throw "Error Narrow"
     }
     
      

endspec
