BinaryRel = spec
  type X
  op brel infixl 100 : X * X -> Bool
endspec


BinaryOp = spec
  type X
  op bop infixl 100 : X * X -> X
endspec


Test1 = generate lisp BinaryRel

Test2 = generate lisp BinaryOp
