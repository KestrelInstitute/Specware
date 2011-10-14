spec
  op f: fa(a) a -> Bool
  op g: fa(b) b -> Bool
  %def f(x) = g x
  def fa(a) f(x:a) = g(x:a)
endspec
