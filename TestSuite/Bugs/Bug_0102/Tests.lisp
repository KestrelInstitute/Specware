(test-directories ".")

(test 

 ("Bug 0102 : Extra variable in gnerated proof obligation"
  :show   "ObligationsOfInteger.sw" 
  :output ";;; Elaborating obligator at $TESTDIR/ObligationsOfInteger

spec  
 import /Library/Base/WFO
 conjecture Integer.abs_Obligation is fa(x : Integer) x >= 0 => natural? x
 conjecture Integer.abs_Obligation0 is 
    fa(x : Integer) ~(x >= 0) => natural?(- x)
 conjecture Integer.addition_def2_Obligation is 
    fa(n1 : PosNat, n2 : PosNat) 
     n1 + n2 = plus(n1, n2) 
     && - n1 + - n2 = -(plus(n1, n2)) && ~(lte(n1, n2)) => lte(n2, n1)
 conjecture Integer.addition_def2_Obligation0 is 
    fa(n1 : PosNat, n2 : PosNat) 
     n1 + n2 = plus(n1, n2) 
     && - n1 + - n2 = -(plus(n1, n2)) 
        && n1 + - n2 
           = (if lte(n1, n2) then -(minus(n2, n1)) else minus(n1, n2)) 
           && ~(lte(n1, n2)) => lte(n2, n1)
 conjecture Integer.division_def_Obligation is 
    fa(y : NonZeroInteger) natural?(abs y) => abs y ~= 0
 conjecture Integer.division_def_Obligation0 is 
    fa(x : Integer, y : NonZeroInteger) natural?(abs x div abs y)
endspec

")

 )
