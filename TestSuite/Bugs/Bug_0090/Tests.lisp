(test-directories ".")

(test 

 ("Bug 0090 : Insufficient context to type-check case branches"
  :show   "caseContext#O"
  :output ";;; Elaborating obligator at $TESTDIR/caseContext#O
;;; Elaborating spec at $TESTDIR/caseContext#S

spec  
 import S
 import /Library/Base/WFO
 conjecture f_Obligation0 is [a] fa(P : List(a)) natural?(100 div length P)
endspec

")

 )
