(test-directories ".")

(test 

 ("Bug 0112 : Failure to translate when rule uses unqualified ref"
  :show   "Capture#Z"
  :output ";;; Elaborating spec-translation at $TESTDIR/Capture#Z
;;; Elaborating spec at $TESTDIR/Capture#S

spec
  type Z
  axiom foo is fa (x : Z) x = x
endspec

")
 
 )