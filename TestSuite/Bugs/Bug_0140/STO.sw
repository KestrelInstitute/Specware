S = spec

  type FF a

  op c : [a] FF a

  def [a] c = c

endspec


T = spec

  type FF a

  op c : [a] FF a

endspec


O = obligations morphism S -> T {}
