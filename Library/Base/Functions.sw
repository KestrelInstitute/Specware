Functions qualifying spec

  % identity and composition:

  op id : [a] a -> a = fn x -> x

  op [a,b,c] o (g: b -> c, f: a -> b) infixl 24 : a -> c = fn x:a -> g (f x)

  theorem identity is [a,b]
    fa (f: a -> b) id o f = f
                && f o id = f

  theorem associativity is [a,b,c,d]
    fa (h: c -> d, g: b -> c, f: a -> b) (h o g) o f = h o (g o f)

  % injectivity, surjectivity, bijectivity:

  op [a,b] injective? (f: a -> b) : Boolean =
    fa (x1:a,x2:a) f x1 = f x2 => x1 = x2

  op [a,b] surjective? (f: a -> b) : Boolean =
    fa (y:b) (ex (x:a) f x = y)

  op [a,b] bijective? (f: a -> b) : Boolean =
    injective? f && surjective? f

  type Injection (a,b) = ((a -> b) | injective?)

  type Surjection(a,b) = ((a -> b) | surjective?)

  type Bijection (a,b) = ((a -> b) | bijective?)

  % inversion:

  op [a,b] inverse (f: Bijection(a,b)) : Bijection(b,a) =
    fn y:b -> the(x:a) f x = y

  theorem inverse is [a,b]
    fa(f:Bijection(a,b)) f o inverse f = id
                      && inverse f o f = id

  % not clear why this is here:

  op  wfo: [a] (a * a -> Boolean) -> Boolean

  % mapping to Isabelle:

  proof Isa ThyMorphism Fun
    Functions.id \_rightarrow id
    Functions.o \_rightarrow o Left 24
    Functions.injective? \_rightarrow inj
    Functions.surjective? \_rightarrow surj
    Functions.bijective? \_rightarrow bij
    Functions.inverse \_rightarrow inv
  end-proof

endspec
