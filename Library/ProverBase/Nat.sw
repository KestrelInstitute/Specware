PrNat qualifying spec

  import ../Base/Nat

  % usual Peano axiomatization:

  axiom zero_not_succ is
    ~(ex (n : Nat) Nat.zero = succ n)

  axiom zero_not_succ is
    fa (n : Nat) ~(Nat.zero = succ n)

  axiom succ_injective is
    fa (n1:Nat, n2:Nat) succ n1 = succ n2 => n1 = n2

  axiom induction is
    fa (p : Nat -> Boolean)
      p zero &&
      (fa (n:Nat) p n => p (succ n)) =>
      (fa (n:Nat) p n)

  axiom posNat?_def is
    fa (n: Nat) posNat?(n) <=> (n ~= zero)

  axiom one_def is one = succ zero

  axiom two_def is two = succ(succ zero)

  axiom plus_def1 is
    fa(n:Nat) plus(n,zero) = n
  axiom plus_def2 is
    fa(n:Nat, n0:Nat) plus(n,succ n0) = succ(plus(n,n0))

  axiom lte_def1 is
    fa(n:Nat) lte(zero,n)
  axiom lte_def2 is
    fa(n:Nat) ~(lte(succ n, zero))
  axiom lte_def3 is
    fa(n1:Nat, n2:Nat) lte(succ n1,succ n2) <=> lte(n1,n2)

  axiom minus_def1 is
    fa(n:Nat) minus(n,zero) = n
  axiom minus_def2 is
    fa(n1:Nat, n2:Nat) lte(n2,n1) => minus(succ n1,succ n2) = minus(n1,n2)

  theorem minus_def is
    fa(n1: Nat, n2: Nat, n3: Nat) lte(n2, n1) && minus(n1, n2) = n3 => n1 = plus(n2, n3)

endspec
