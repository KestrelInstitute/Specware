BinaryRel = spec
  sort X
  op brel infixl 100 : X * X -> Boolean
endspec


BinaryOp = spec
  sort X
  op bop infixl 100 : X * X -> X
endspec


Test1 = generate lisp BinaryRel

Test2 = generate lisp BinaryOp
