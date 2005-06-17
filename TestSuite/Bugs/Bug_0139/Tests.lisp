(test-directories ".")

(test 

 ("Bug 0139 : Prover goes into debugger"
  :sw "Logic#Prove"
  :output '(";;; Elaborating spec at $TESTDIR/Logic#Logic"
	    ";;; Elaborating proof-term at $TESTDIR/Logic#Prove"
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
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/Logic/Prove.log")
	    (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	    (:optional ";; Directory $TESTDIR/Snark/Logic/ does not exist, will create.")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
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