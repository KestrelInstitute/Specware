S = spec

  type RR = {a : {b : Int}}

  op z : RR

  axiom pp is
     z.a.b = 0

endspec


T = spec

  type RR = {a : {b : Int}}

  op z : RR

  def z = {a = {b = 0}}

endspec


BadObl1 = obligations morphism S -> T {}
