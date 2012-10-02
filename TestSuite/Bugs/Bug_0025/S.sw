
spec

  op foo : String * String -> Bool

  def foo (x, y) =
    (implode (explode x)) ^ (implode (explode y))
    =
    (implode ((explode x) ++ (explode y)))

endspec
