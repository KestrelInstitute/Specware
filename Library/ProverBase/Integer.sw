PrInteger qualifying spec

  import ../Base/Integer

  type ProverNat = {i: Integer | i >= 0}

  %type Integer.Integer  % qualifier required for internal parsing reasons

  % true for non-negative integers:
  %op natural? : Integer -> Boolean

  (* The following type definition defines the naturals to be a subtype of the
  integers. However, since the naturals have been axiomatized in spec Nat,
  this definition really constrains the integers to be a supertype of the
  naturals. In addition, it allows us to take advantage of the automatic
  insertions of relax and restrict to map between naturals and integers. Note
  that the qualifier Nat in Nat.Nat is needed because otherwise the following
  type definition would introduce a new unqualified type Nat. *)

  %type Nat.Nat = (Integer | natural?)


  axiom succ_def is fa(n) Integer.isucc n = n + 1

  % negating zero is a no-op
  axiom minus_zero is
    -0 = 0

  theorem unary_minus_involution is
    fa(i:Integer) -(-i) = i

  theorem commutative_plus is
    fa(x,y) x+y = y+x

  theorem associative_plus is
    fa(x,y,z) (x+y)+z = x+(y+z)


%%% RW's theory
  axiom plus_zero is
   fa(x:Integer)
    x + 0 = x

  conjecture number_minus_zero_thm is
   fa(x:Integer)
    x - 0 = x

  conjecture number_minus_number_zero_thm is
   fa(x:Integer)
    x - x = 0

%  axiom plus_monotonic is
%    fa(x:Integer, y:Nat)
%     x <= x + y
   

  axiom minus_migration is
    fa(x:Integer, y:Integer, z:Integer)
     x - z + y = x + y - z
     
  axiom gt_implies_lte is
   fa(x:Integer, y:Integer)
    y > x  <=> x + 1 <= y

  axiom lt_implies_lte is
   fa(x:Integer, y:Integer)
    x < y  <=> x + 1 <= y

  axiom not_lte_implies_lte_plus_1 is
   fa(x:Integer, y:Integer)
   ~(y <= x) => x + 1 <= y

  axiom gte_implies_lte is 
   fa(x:Integer, y:Integer)
    y >= x  <=> x <= y

  axiom not_gt_is_lte is 
   fa(x:Integer, y:Integer)
    ~(x > y) => x <= y

  axiom diff_gte_zero_is_lte is
   fa(x:Integer, y:Integer)
    y - x >= 0  => x <= y

  

  axiom reduction is
   fa(x:Integer,a:Integer, b:Integer)
       x + a <= x + b
    => a <= b

  conjecture reduction_left_zero is
   fa(x:Integer, b:Integer)
       x <= x + b
    => 0 <= b

  conjecture reduction_right_zero is
   fa(x:Integer,a:Integer)
       x + a <= x
    => a <= 0

  conjecture integer_minus_zero is
    fa(x:Integer) x - 0 = x

  conjecture minus_elimination is
   fa(x:Integer, y:Integer, z:Integer)
       (x - z <= y) =>  x <= y + z

  axiom chaining is
   fa(x:Integer,a:Integer, b:Integer, c:Integer, d:Integer)
          a <= b + x
        & c + x <= d 
     => a + c <= d + b

  conjecture chaining_left_zero is
   fa(x:Integer,a:Integer, c:Integer, d:Integer)
     a <= x &&
     c + x <= d =>
     a + c <= d

  %% Formerly in Nat.sw
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

endspec
