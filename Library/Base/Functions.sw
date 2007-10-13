Functions qualifying spec

  (* Functions are built-in in Metaslang (A -> B is the type of all functions
  from type A to type B). This spec introduce some operations on functions and
  some subtypes of functions. *)

  % identity and composition:

  op id : [a] a -> a = fn x -> x

  op [a,b,c] o (g: b -> c, f: a -> b) infixl 24 : a -> c = fn x:a -> g (f x)

  theorem identity is [a,b]
    fa (f: a -> b) id o f = f
                && f o id = f

  theorem associativity is [a,b,c,d]
    fa (f: a -> b, g: b -> c, h: c -> d) (h o g) o f = h o (g o f)
  proof Isa
    apply(simp add: o_assoc)
  end-proof

  % forward (a.k.a. diagrammatic) composition:

  op [a,b,c] :> (f: a -> b, g: b -> c) infixl 24 : a -> c = g o f

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
  proof Isa
    apply(simp add: bij_def surj_iff inj_iff)
  end-proof

  theorem f_inverse_apply is [a,b]
    fa(f:Bijection(a,b), x: b) f(inverse f (x)) = x
  proof Isa
    apply(simp add: bij_def surj_f_inv_f)
  end-proof

  theorem inverse_f_apply is [a,b]
    fa(f:Bijection(a,b), x: a) inverse f(f (x)) = x
  proof Isa
    apply(simp add: bij_def inv_f_f)
  end-proof

  % eta conversion:

  theorem eta is [a,b]
    fa(f: a -> b) (fn x -> f x) = f

  % used by obligation generator:

  op  wfo: [a] (a * a -> Boolean) -> Boolean

  % mapping to Isabelle:

  proof Isa ThyMorphism Hilbert_Choice
    Functions.id \_rightarrow id
    Functions.o \_rightarrow o Left 24
    Functions.:> -> o Left 24 reversed
    Functions.injective? \_rightarrow inj
    Functions.surjective? \_rightarrow surj
    Functions.bijective? \_rightarrow bij
    Functions.inverse \_rightarrow inv
  end-proof

endspec
