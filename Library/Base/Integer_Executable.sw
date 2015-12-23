(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Integer qualifying spec

import Integer

refine def divides (x:Int, y:Int) : Bool =
  if x = 0 then y = 0  else y modF x = 0

refine def divR (i:Int, j:Int0): Int =
  if     2 * abs(i modF j) < abs j 
     || (2 * abs(i modF j) = abs j && 2 divides (i divF j))
    then i divF j
    else (i divF j) + 1

refine def divE (i:Int, j:Int0): Int = 
  (i divF abs j) * sign j

refine def modE (i:Int, j:Int0): Int = 
  i modF abs j

refine def divT (i:Int, j:Int0): Int =
  ((abs i) divF (abs j)) * sign (i*j)



% ------------------------------------------------------------------------------
% -----------------  The proofs ------------------------------------------------
% ------------------------------------------------------------------------------



proof isa Integer__divides__1__obligation_refine_def
  by (simp add: Integer__divides__1_def dvd_eq_mod_eq_0)
end-proof

proof isa Integer__divR__1__obligation_refine_def
  apply (simp only: Integer__divR__1_def transfer_nat_int_numerals(3) 
                    zabs_def nat_mult_distrib [symmetric] nat_less_eq_zless)
  apply (auto simp add: divR_def)
end-proof

proof isa Integer__divE__1__obligation_refine_def
  by (simp add: Integer__divE__1_def divE_def)
end-proof

proof isa Integer__modE__1__obligation_refine_def
  by (simp add: Integer__modE__1_def modE_def)
end-proof

proof isa Integer__divT__1__obligation_refine_def
  by (simp add: Integer__divT__1_def divT_def)
end-proof



endspec
