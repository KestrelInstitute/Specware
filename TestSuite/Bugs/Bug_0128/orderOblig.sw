S = spec

  op c : Int

  op d : Nat
  def d = c   % not well-typed

  op e : Int
  def e = d

  conjecture E is e >= 0

endspec


O = obligations S


P = prove d_Obligation_subtype in O
