Functions qualifying spec

  type Function(a,b) = a -> b
  type Injection(a,b)  = (Function(a,b) | injective?)
  type Surjection(a,b) = (Function(a,b) | surjective?)
  type Bijection(a,b)  = (Function(a,b) | bijective?)

  op id          : fa(a) Function(a,a)
  op o infixl 24 : fa(a,b,c) Function(b,c) * Function(a,b) -> Function(a,c)
  op injective?  : fa(a,b) Function(a,b) -> Boolean
  op surjective? : fa(a,b) Function(a,b) -> Boolean
  op bijective?  : fa(a,b) Function(a,b) -> Boolean
  op inverse     : fa(a,b) Bijection(a,b) -> Bijection(b,a)

  def id (x) = x

  def o (f,g) x = f(g x)

  axiom injective?_def is type fa(a,b)
    fa (f : a -> b) injective? f <=> (fa (x:a,y:a) f x = f y => x = y)

  axiom surjective?_def is type fa(a,b)
    fa (f : a -> b) surjective? f <=> (fa (y:b) (ex (x:a) f x = y))

  axiom bijective?_def is type fa(a,b)
    fa (f : a -> b) bijective? f <=> injective? f && surjective? f

  axiom inverse_def is type fa(a,b)
    fa (f : Bijection(a,b))  (inverse f) o f = id  &&  f o (inverse f) = id

endspec
