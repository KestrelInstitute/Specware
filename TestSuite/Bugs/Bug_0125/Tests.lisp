(test-directories ".")

(test 

 ("Bug 0125 : Prover unsoundness when using PosNat"
  :sw "PosNat#p"
  :output '(";;; Elaborating spec at $TESTDIR/PosNat#s"
	    ";;; Elaborating proof-term at $TESTDIR/PosNat#p"
	    (:optional
	     ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top"
	     ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char"
	     ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare"
	     ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions"
	     ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer"
	     ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List"
	     ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat"
	     ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Option"
	     ";;; Elaborating spec at $SPECWARE/Library/ProverBase/String"
	     ";;; Elaborating spec at $SPECWARE/Library/ProverBase/System"
	     ";;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite"
	     ";; ensure-directories-exist: creating $TESTDIR/Snark/PosNat/p.log"
	     ";; Directory $TESTDIR/Snark/ does not exist, will create."
	     ";; Directory $TESTDIR/Snark/PosNat/ does not exist, will create."
	     ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/PosNat/p.log")
	    (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	    (:optional ";; Directory $TESTDIR/Snark/PosNat/ does not exist, will create.")
	    "    Expanded spec file: $TESTDIR/Snark/PosNat/p.sw"
	    "    Snark Log file: $TESTDIR/Snark/PosNat/p.log"
	    "p: Conjecture c in s is NOT proved using Snark."
	    ""))

 )