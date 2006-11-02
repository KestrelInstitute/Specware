Functions qualifying spec

  op id : [a] a -> a
  def id x = x

  op o infixl 24 : [a,b,c] (b -> c) * (a -> b) -> (a -> c)
  def o (f,g) x = f (g x)

  op injective?  : [a,b] (a -> b) -> Boolean
  axiom injective?_def  is [a,b]
    fa (f : a -> b) injective?  f <=> (fa (x:a,y:a) f x = f y => x = y)
%  def injective?  f = (fa(x1,x2) f x1 = f x2 => x1 = x2)

  op surjective? : [a,b] (a -> b) -> Boolean
  axiom surjective?_def is [a,b]
    fa (f : a -> b) surjective? f <=> (fa (y:b) (ex (x:a) f x = y))
%  def surjective? f = (fa(y) (ex(x) f x = y))

  op bijective?  : [a,b] (a -> b) -> Boolean
  axiom bijective?_def  is [a,b]
    fa (f : a -> b) bijective?  f <=> injective? f && surjective? f
%  def bijective?  f = injective? f && surjective? f

  type Injection (a,b) = ((a -> b) | injective?)

  type Surjection(a,b) = ((a -> b) | surjective?)

  type Bijection (a,b) = ((a -> b) | bijective?)

  op inverse : [a,b] Bijection(a,b) -> Bijection(b,a)
  axiom inverse_def is [a,b]
    fa (f:Bijection(a,b))  (inverse f) o f = id  &&  f o (inverse f) = id

  proof Isa ThyMorphism Fun
    Functions.id \_rightarrow id
    Functions.o \_rightarrow o Left 24
    Functions.injective? \_rightarrow inj
    Functions.surjective? \_rightarrow surj
    Functions.bijective? \_rightarrow bij
    Functions.inverse \_rightarrow inv
  end-proof

endspec
