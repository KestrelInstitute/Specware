PrNat qualifying spec

  import ../Base/Nat

  % usual Peano axiomatization:

  axiom zero_not_succ1 is
    ~(ex (n : Nat) zero = Nat.succ n)

  axiom zero_not_succ2 is
    fa (n : Nat) ~(zero = Nat.succ n)

  axiom succ_injective is
    fa (n1:Nat, n2:Nat) Nat.succ n1 = Nat.succ n2 => n1 = n2

  axiom induction is
    fa (p : Nat -> Boolean)
      p zero &&
      (fa (n:Nat) p n => p (Nat.succ n)) =>
      (fa (n:Nat) p n)

  axiom posNat?_def is
    fa (n: Nat) posNat?(n) <=> (n ~= zero)

  axiom zero_def is zero = 0

  axiom one_def is one = 1

% axiom two_def is two = 2

  axiom plus_def1 is
    fa(n:Nat) n + 0 = n
  axiom plus_def2 is
    fa(n:Nat, n0:Nat) n + Nat.succ n0 = Nat.succ(n + n0)

  axiom lte_def1 is
    fa(n:Nat) 0 <= n
  axiom lte_def2 is
    fa(n:Nat) ~(Nat.succ n <= 0)
  axiom lte_def3 is
    fa(n1:Nat, n2:Nat) Nat.succ n1 <= Nat.succ n2 <=> n1 <= n2

  axiom minus_def1 is
    fa(n:Nat) n - 0 = n
  axiom minus_def2 is
    fa(n1:Nat, n2:Nat) n2 <= n1 => Nat.succ n1 - Nat.succ n2 = n1 - n2

%  theorem minus_def is
%    fa(n1: Nat, n2: Nat, n3: Nat) n2 <= n1 && n1 - n2 = n3 => n1 = n2 + n3

endspec
