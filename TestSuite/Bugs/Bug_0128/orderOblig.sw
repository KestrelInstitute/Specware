S = spec

  op c : Integer

  op d : Nat
  def d = c   % not well-typed

  op e : Integer
  def e = d

  conjecture E is e >= 0

endspec


O = obligations S


P = prove d_Obligation_subsort in O
