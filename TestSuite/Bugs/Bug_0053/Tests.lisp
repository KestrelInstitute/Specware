(test-directories ".")

(test 

 ("Bug 0053 : Strange result is shown for result of spec-substitution"
  :show   "Subst#BB" 
  :output ";;; Elaborating spec-substitution at $TESTDIR/Subst#BB
;;; Elaborating spec at $TESTDIR/Subst#AA
;;; Elaborating spec at $TESTDIR/Subst#A
;;; Elaborating spec-morphism at $TESTDIR/Subst#M
;;; Elaborating spec at $TESTDIR/Subst#B

spec  
 import B
 type Interval = {start : Nat, stop : Nat}
 
 op  isEmptyInterval? : Interval -> Boolean
 def isEmptyInterval? {start = x, stop = y} = x = y
endspec

")

 )
