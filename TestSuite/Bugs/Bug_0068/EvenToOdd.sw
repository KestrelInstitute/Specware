S1 = spec
  sort Even = {n : Nat | ex(m) n = 2 * m}
endspec

S2 = spec
  sort Odd = {n : Nat | ex(m) n = 2 * m + 1}
endspec

M = morphism S1 -> S2 {Even +-> Odd}

O = obligations M
