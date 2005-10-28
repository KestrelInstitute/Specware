(test-directories ".")

(test 

 ("Bug 0131 : Prover goes into debugger"
  :sw "Option#P"
  :output '(";;; Elaborating obligator at $TESTDIR/Option#P"
	    ";;; Elaborating spec at $TESTDIR/Option#O"
	    ";;; Elaborating proof-term at $TESTDIR/Option#P"
	    (:optional ";;; Elaborating spec at $SPECWARE/Provers/ProofChecker/Libs/Logic")
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/Option/P.log")
	    (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	    (:optional ";; Directory $TESTDIR/Snark/Option/ does not exist, will create.")
	    "    Expanded spec file: $TESTDIR/Snark/Option/P.sw"
	    "    Snark Log file: $TESTDIR/Snark/Option/P.log"
	    "P: Conjecture PFunctions.o_Obligation is Proved! using Snark*."
	    ""))

 )