(test-directories ".")

(test 

 ("Bug 0139 : Prover goes into debugger"
  :sw "Logic#Prove"
  :output '(";;; Elaborating spec at $TESTDIR/Logic#Logic"
	    ";;; Elaborating proof-term at $TESTDIR/Logic#Prove"
	    (:alternatives
	     (";; ensure-directories-exist: creating $TESTDIR/Snark/Logic/Prove.log")
	     (";; ensure-directories-exist: creating"
	      ";;   $TESTDIR/Snark/Logic/Prove.log" ))
	    ";; Directory $TESTDIR/Snark/ does not exist, will create."
	    ";; Directory $TESTDIR/Snark/Logic/ does not exist, will create."
	    "    Expanded spec file: $TESTDIR/Snark/Logic/Prove.sw"
	    "    Snark Log file: $TESTDIR/Snark/Logic/Prove.log"
	    "Prove: Conjecture Logic.TRUE in Logic is Proved! using simple inequality reasoning."
	    ""))

 )