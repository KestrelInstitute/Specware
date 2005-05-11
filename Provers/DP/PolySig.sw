Poly qualifying spec

  import Coefficient

  type Var
  type Term
  type Poly

  op toString: Var -> String
  op equal: Poly * Poly -> Boolean
  op plus: Term * Poly -> Poly
  op PolyTerm.zero?: Term -> Boolean
  op zero?: Poly -> Boolean
  op toTerm: Coef -> Term
  op mkTerm: Coef * Var -> Term
  op toPoly: Term -> Poly
  op PolyTerm.constant?: Term -> Boolean
  op constant?: Poly -> Boolean
  op PolyTerm.constant: Term -> Coef
  op PolyTerm.var: Term -> Var
  op constant: Poly -> Coef
  op constantPlusConstant: Coef * Coef -> Poly
  op termPlusConstant: Term * Coef -> Poly
  op hdTerm: Poly -> Term
  op restPoly: Poly -> Poly
  op Var.equal?: Var * Var -> Boolean
  op Var.compare: Var * Var -> Comparison
  op Var.print: Var -> String

endspec
