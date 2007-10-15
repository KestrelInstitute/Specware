Nat qualifying spec

  import Integer

  % we define natural numbers as a subtype of the integers:

  op natural? (i:Integer) : Boolean = i >= zero

  type Nat = (Integer | natural?)

  % positive (i.e. non-zero) natural numbers:

  op posNat? (n:Nat) : Boolean = n > zero

  type PosNat = (Nat | posNat?)

  % successor restricted to natural numbers:

  op succ(n: Nat): Nat = Integer.succ n

  % mapping to Isabelle:

  proof Isa Thy_Morphism
   type Nat.Nat -> nat (int,nat) [+,*,div,rem,<=,<,>=,>,abs,min,max]
   Nat.succ     -> Suc
  end-proof

  (* Metaslang's natural literals are simply syntactic shortcuts for expressions
  involving zero and succ. For example, 0 stands for zero, 3 stands for succ
  (succ (succ zero)), and 0xA stands for succ (succ (succ (succ (succ (succ
  (succ (succ (succ (succ zero))))))))). *)

endspec
