spec

%  import Integer
%  import Nat

%  axiom ge_reflexive is fa (i: Integer) (i >= i) = true

  %axiom nat_plus_nat is fa (n1: Nat, n2: Nat) n1 + n2 >= 0

%  axiom ge_le_to_equal is fa (i, j: Integer) (((i >= j) & (j >= i)) = (i = j))

%  axiom move_to_right is fa (i,j:Integer) ((i > j) = (i + (~ j) > 0))

%  axiom not_gt is fa (i, j: Integer) (~(i > j)) = (i <= j)

%  axiom gt_to_ge is fa (i,j:Integer) ((i > 0) = (i + (~ 1) >= 0))

%  axiom gt_def is fa (i: Integer) ((i > 0) = ((i >= 0) & ~(i = 0)))

%  axiom gt_def2 is fa (i: Integer) ((i >= 0) => (i + 1 > 0))

%  axiom ge_simp is fa (i,j:Integer) (i >= j = (i - j >= 0))

%  axiom nat_not_zero is fa (n: Nat) (~(n = 0) = (n > 0))

  %axiom lt_to_le is fa (i, j: Integer) (i < j <=> i <= j-1)

  %axiom le_to_ge is fa (i, j:Integer) (i >= j <=> j <= i)

%  axiom minus_zero is fa (i: Integer) (i + (~ i) = 0)

endspec