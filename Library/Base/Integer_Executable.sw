spec
import Integer

refine def divides (x:Int, y:Int) : Bool =
  y = 0 || x modF y = 0

refine def divR (i:Int, j:Int0): Int =
  if 2 * abs(i mod j) < abs j
    then i divF j
    else (i divF j) + 1

refine def divE (i:Int, j:Int0): Int = 
  (i divF abs j) * sign j

refine def modE (i:Int, j:Int0): Int = 
  i modF abs j

refine def divT (i:Int, j:Int0): Int =
  (abs i) divF (abs j) * sign i

proof isa Integer__divides__1__obligation_refine_def
sorry
end-proof

proof isa Integer__divR__1__obligation_refine_def
sorry
end-proof

proof isa Integer__divE__1__obligation_refine_def
sorry
end-proof

proof isa Integer__modE__1__obligation_refine_def
sorry
end-proof

proof isa Integer__divT__1_Obligation_subtype
sorry
end-proof

proof isa Integer__divT__1__obligation_refine_def
sorry
end-proof



endspec
