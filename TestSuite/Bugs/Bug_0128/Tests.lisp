(test-directories ".")

(test ("Bug 0128 : Obligation shouldn't be proved if obligations generated in correct order"
       :sw "orderOblig#P"
       :output '(";;; Elaborating obligator at $TESTDIR/orderOblig#O"
		 ";;; Elaborating spec at $TESTDIR/orderOblig#S"
		 ";;; Elaborating proof-term at $TESTDIR/orderOblig#P"
		 (:optional
		  (:alternatives
		   (";; ensure-directories-exist: creating $TESTDIR/Snark/orderOblig/P.log")
		   (";; ensure-directories-exist: creating"
		    ";;   $TESTDIR/Snark/orderOblig/P.log")))
		 (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
		 (:optional
		  (:alternatives
		   (";; Directory $TESTDIR/Snark/orderOblig/ does not exist, will create.")
		   (";; Directory $TESTDIR/Snark/orderOblig/ does not exist, will"
		    ";;   create.")))
		 "    Expanded spec file: $TESTDIR/Snark/orderOblig/P.sw"
		 "    Snark Log file: $TESTDIR/Snark/orderOblig/P.log"
		 "P: Conjecture d_Obligation in O is NOT proved using Snark."
		 "")))