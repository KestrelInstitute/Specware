Assert qualifying spec

  (* This spec defines a useful tool to "insert" proof obligations into
  arbitrary positions inside expressions. The tool is an operation defined on
  the subtype of `Boolean' consisting of `true', which returns nothing. The
  point is that, given a boolean expression (formula) `f', the implicit
  restrict in `assert f' engenders a proof obligation that `f' is true. Given
  an expression `e[e0]' where we have singled out an occurrence of `e0' inside
  `e', if we expect `f' to be true at that occurrence of `e0', we can perform
  the substitution `e[(assert f; e0)]', causing Specware to generate a proof
  obligation that `f' is provable in the context in which `e0' occurs inside
  `e'. *)

  op assert : {b : Boolean | b} -> ()

endspec 
