spec {

  import Integer
  import Nat

  axiom nat_ge_zero is fa (n: Nat) (n >= 0)

  %axiom posnat_gt_zero is fa (n:PosNat) (n > 0)

  axiom ge_reflexive is fa (i: Integer) (i >= i)

  axiom ge_le_to_equal is fa (i, j: Integer) (((i >= j) & (j >= i)) => i = j)

  axiom gt_to_ge is fa (i,j:Integer) (i > j => i >= j+1)

  axiom ge_simp is fa (i,j:Integer) (i >= j => i - j >= 0)

  axiom nat_not_zero is fa (n: Nat) (~(n = 0) => n > 0)

  axiom lt_to_le is fa (i, j: Integer) (i < j => i <= j-1)

  axiom le_to_ge is fa (i, j:Integer) (i >= j <=> j <= i)

  axiom minus_zero is fa (i: Integer) (i - i = 0)

}