(test-directories ".")

(test 
 ("Bug 0116 : Error in removeCurrying"
  :sw  "RemCurr#P"
  :output    '(
	       ";;; Elaborating spec at $TESTDIR/RemCurr#S"
	       ";;; Elaborating proof-term at $TESTDIR/RemCurr#P"
	       (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/RemCurr/P.log")
	       (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	       (:optional ";; Directory $TESTDIR/Snark/RemCurr/ does not exist, will create.")
	       "    Expanded spec file: $TESTDIR/Snark/RemCurr/P.sw"
	       "    Snark Log file: $TESTDIR/Snark/RemCurr/P.log"
	       "P: Conjecture TRUE in S is Proved! using simple inequality reasoning."
	       ""))

 )