(test-directories ".")

(test 

 ("Bug 0125 : Prover unsoundness when using PosNat"
  :sw "PosNat#p"
  :output '(";;; Elaborating proof-term at $TESTDIR/PosNat#p"
	    ";;; Elaborating spec at $TESTDIR/PosNat#s"
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/PosNat/p.log")
	    (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	    (:optional ";; Directory $TESTDIR/Snark/PosNat/ does not exist, will create.")
	    "p: Conjecture c in s is NOT proved using Snark."
	    "    Snark Log file: $TESTDIR/Snark/PosNat/p.log"
	    ""))

 )