spec

  axiom A is
     (ex(x:Boolean) x) => false

  axiom B is
     (let zero = 1 in zero) = zero

  axiom C is
     (if true then 1 else 2) + 3 = 4

endspec
