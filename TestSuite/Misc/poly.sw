spec
  op f: fa(a) a -> Boolean
  op g: fa(b) b -> Boolean
  %def f(x) = g x
  def fa(a) f(x:a) = g(x:a)
endspec
