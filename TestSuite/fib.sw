spec

op computeFib: Nat -> Nat
op computeFibH: Nat * Nat * Nat -> Nat
  def computeFIb(n) = 
    case n of
         | 0 -> 0
         | 1 -> 1
         | _ -> computeFibH(n-2,1,1)
  def computeFibH(n, fib1, fib2) = 
     if n = 0 then fib1 + fib2
     else computeFibH(n-1,fib1+fib2, fib1)     
endspec
