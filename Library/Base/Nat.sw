Nat qualifying spec

  % usual Peano axiomatization:

  type Nat.Nat  % qualifier required for internal parsing reasons

  op zero : Nat

  op succ : Nat -> Nat

  axiom zero_not_succ is
    ~(ex(n:Nat) zero = succ n)

  axiom succ_injective is
    fa (n1:Nat, n2:Nat) succ n1 = succ n2 => n1 = n2

  axiom induction is
    fa (p : Nat -> Boolean)
      p zero &&
      (fa(n:Nat) p n => p (succ n)) =>
      (fa(n:Nat) p n)

  % positive natural numbers:

  op posNat? : Nat -> Boolean
  def posNat? n = (n ~= zero)

  type PosNat = {n : Nat | posNat? n}

  % other ops:

  op one : Nat
  def one = succ zero

  op two : Nat
  def two = succ(succ zero)

  op plus : Nat * Nat -> Nat
  axiom plus_def1 is
    fa(n:Nat) plus(n,zero) = n
  axiom plus_def2 is
    fa(n:Nat, n0:Nat) plus(n,succ n0) = succ(plus(n,n0))

  op lte : Nat * Nat -> Boolean
  axiom lte_def1 is
    fa(n:Nat) lte(zero,n)
  axiom lte_def2 is
    fa(n:Nat) ~(lte(succ n, zero))
  axiom lte_def3 is
    fa(n1:Nat, n2:Nat) lte(succ n1,succ n2) <=> lte(n1,n2)

  op minus : {(n1,n2) : Nat * Nat | lte(n2,n1)} -> Nat
  axiom minus_def1 is
    fa(n:Nat) minus(n,zero) = n
  axiom minus_def2 is
    fa(n1:Nat, n2:Nat) lte(n2,n1) => minus(succ n1,succ n2) = minus(n1,n2)

  proof Isa Thy_Morphism
   type Nat.Nat \_rightarrow nat (int,nat)
   Nat.zero \_rightarrow 0
   Nat.one \_rightarrow 1
   Nat.two \_rightarrow 2
   Nat.succ \_rightarrow Suc
   Nat.plus \_rightarrow +  Left 25
   Nat.minus \_rightarrow - Left 25
   Nat.lte \_rightarrow \<le> Left 20
  end-proof

endspec
