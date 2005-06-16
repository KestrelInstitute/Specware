(test-directories ".")

(test 

 ("Bug 0139 : Prover goes into debugger"
  :sw "Logic#Prove"
  :output '(";;; Elaborating spec at $TESTDIR/Logic#Logic"
	    ";;; Elaborating proof-term at $TESTDIR/Logic#Prove"
	    (:optional
	     ";; ensure-directories-exist: creating $TESTDIR/Snark/Logic/Prove.log")
	    (:optional
	     ";; ensure-directories-exist: creating"
	     ";;   $TESTDIR/Snark/Logic/Prove.log" )
	    (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	    (:optional ";; Directory $TESTDIR/Snark/Logic/ does not exist, will create.")
	    "    Expanded spec file: $TESTDIR/Snark/Logic/Prove.sw"
	    "    Snark Log file: $TESTDIR/Snark/Logic/Prove.log"
	    "Prove: Conjecture Logic.TRUE in Logic is Proved! using simple inequality reasoning."
	    ""))

 )