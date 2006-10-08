(test-directories ".")

(test 

 ("Bug 0131 : Prover goes into debugger"
  :sw "Option#P"
  :output '(";;; Elaborating obligator at $TESTDIR/Option#P"
	    ";;; Elaborating spec at $TESTDIR/Option#O"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    (:optional ";;; Elaborating proof-term at $TESTDIR/.")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Option")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/String")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/System")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite")
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/..log")
	    (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
	    (:optional "    Expanded spec file: $TESTDIR/Snark/..sw")
	    (:optional "    Snark Log file: $TESTDIR/Snark/..log")
	    "Conjecture PFunctions.o_Obligation_fn_precond is Proved! using Snark in * seconds."
	    ""))

 )