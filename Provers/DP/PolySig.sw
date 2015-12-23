(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Poly qualifying spec

  import Coefficient

  type Var
  type Term
  type Poly

  op toString: Var -> String
  op equal: Poly * Poly -> Bool
  op plus: Term * Poly -> Poly
  op PolyTerm.zero?: Term -> Bool
  op zero?: Poly -> Bool
  op toTerm: Coef -> Term
  op mkTerm: Coef * Var -> Term
  op toPoly: Term -> Poly
  op PolyTerm.constant?: Term -> Bool
  op constant?: Poly -> Bool
  op PolyTerm.constant: Term -> Coef
  op PolyTerm.var: Term -> Var
  op constant: Poly -> Coef
  op constantPlusConstant: Coef * Coef -> Poly
  op termPlusConstant: Term * Coef -> Poly
  op hdTerm: Poly -> Term
  op restPoly: Poly -> Poly
  op Var.equal?: Var * Var -> Bool
  op Var.compare: Var * Var -> Comparison
  op Var.print: Var -> String

endspec
