spec

  import Integer
  import Nat
  import List
%  import NatPlus

  type ProverNat = {i: Integer | i >= 0}

  axiom plus_0 is fa (i) i = i + 0

  axiom geqs is fa (i) i >= i

  axiom minusii is fa (i) i - i = 0

  axiom geqminu1 is fa (i, k) i >= k+1 => i >= k

  axiom gm1 is fa (i, k) i >= k+1 => (i - k ~= 0)

  axiom gm1g is fa (i, k) i >= k+1 => (i - k >= 0)

  axiom m1m is fa (i, k, j) i - (k + j) = (i - k) - j

(*
  axiom not_gt is fa (i, j: Integer) ~(i <= j) => (i > j)

  axiom min_ax1 is fa(i: Integer, j: Integer) i >= min(i, j) && j >= min(i, j) 
  axiom min_ax2 is fa(i: Integer, j: Integer, k: Integer) i >= k && j >= k => min(i, j) >= k

  axiom geq is fa(i: Integer, j: Integer) i <= j <=> j >= i
*)
%  axiom listComp is[a] fa(l: List a) ex (hd, tl) l = Cons(hd, tl) || l = Nil

%  axiom arith1 is fa (i, j: Integer) i >= 0 && j = i + 1 => -1 < j
%  axiom arith2 is fa (i, j, k: Integer) i >= 0 && j >= 0 && k = i + j => -1 < k
%  axiom arith3 is fa (i, j, k, l: Integer) j + k <= l && i < k => j + i < l

%  axiom eqsub1 is fa (i, j, k: Integer) i = j && i <= k => j <= k
%  axiom chain is fa (i, j, k: Integer) (i >= j) && (j > k) => i > k



%  axiom ge_reflexive is fa (i: Integer) (i >= i) = true

  %axiom nat_plus_nat is fa (n1: Nat, n2: Nat) n1 + n2 >= 0

  %axiom ge_le_to_equal is fa (i, j: Integer) (((i >= j) && (j >= i)) = (i = j))

  %axiom gt_to_ge is fa (i,j:Integer) ((i > 0) = (i - 1 >= 0))

  %axiom gt_def is fa (i: Integer) ((i > 0) <=> ((i >= 0) && (i ~= 0)))

%  axiom gt_def2 is fa (i: Integer) ((i >= 0) => (i + 1 > 0))

%  axiom ge_simp is fa (i,j:Integer) (i >= j = (i - j >= 0))

%  axiom nat_not_zero is fa (n: Nat) ((n = 0) ~= (n > 0))

  %axiom lt_to_le is fa (i, j: Integer) (i < j <=> i <= j-1)

  %axiom le_to_ge is fa (i, j:Integer) (i >= j <=> j <= i)

%  axiom minus_zero is fa (i: Integer) (i - i = 0)

endspec
