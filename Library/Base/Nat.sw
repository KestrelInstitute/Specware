Nat qualifying spec

  import Integer

  % we define natural numbers as a subtype of the integers:

  op natural? (i:Integer) : Boolean = i >= zero

  type Nat = (Integer | natural?)

  % positive (i.e. non-zero) natural numbers:

  op posNat? (n:Nat) : Boolean = n > zero

  type PosNat = (Nat | posNat?)

  % the following should be probably removed because useless:

  op two : Nat = succ one

  op plus (n:Nat, m:Nat) : Nat = n + m

  op lte (n:Nat, m:Nat) : Boolean = n < m

  op minus (n:Nat, m:Nat | n >= m) : Nat = n - m

  op succ(n: Nat): Nat = Integer.succ n

  % mapping to Isabelle:

  proof Isa Thy_Morphism
   type Nat.Nat -> nat (int,nat) [+,*,div,rem,<=,<,>=,>,abs,min,max]
   Nat.succ     -> Suc
   Nat.two      -> 2
   Nat.plus     -> +     Left 25
   Nat.lte      -> \<le> Left 20
   Nat.minus    -> -     Left 25
  end-proof

  (* Metaslang's natural literals are simply syntactic shortcuts for expressions
  involving zero and succ. For example, 0 stands for zero, 3 stands for succ
  (succ (succ zero)), and 0xA stands for succ (succ (succ (succ (succ (succ
  (succ (succ (succ (succ zero))))))))). *)

endspec
