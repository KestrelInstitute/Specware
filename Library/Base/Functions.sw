Functions qualifying spec

  import Boolean

  % sorts:

  sort Injective(a,b)  = ((a -> b) | injective?)
  sort Surjective(a,b) = ((a -> b) | surjective?)
  sort Bijective(a,b)  = ((a -> b) | bijective?)

  % ops whose Lisp code is generated:

  op id          : fa(a) a -> a
  op o infixl 24 : fa(a,b,c) (b -> c) * (a -> b) -> (a -> c)

  def id x = x
  def o (f,g) x = f(g x)

  % ops for which no code can be generated (only used for specification):

  op injective?  : fa(a,b) (a -> b) -> Boolean
  op surjective? : fa(a,b) (a -> b) -> Boolean
  op bijective?  : fa(a,b) (a -> b) -> Boolean
  op inverse     : fa(a,b) Bijective(a,b) -> Bijective(b,a)

  axiom injective?_def is sort fa(a,b)
    fa (f : a -> b) injective? f <=> (fa (x,y : a) f x = f y => x = y)

  axiom surjective?_def is sort fa(a,b)
    fa (f : a -> b) surjective? f <=> (fa (y : b) (ex (x : a) f x = y))

  axiom bijective?_def is sort fa(a,b)
    fa (f : a -> b) bijective? f <=> injective? f & surjective? f

  axiom inverse_def is sort fa(a,b)
    fa (f : Bijective(a,b))  (inverse f) o f = id  &  f o (inverse f) = id

endspec
