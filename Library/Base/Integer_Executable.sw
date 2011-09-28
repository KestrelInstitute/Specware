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

endspec
