(test-directories ".")

(test 

 ("Bug 0131 : Prover goes into debugger"
  :sw "Logic#Prove"
  :output '(";;; Elaborating proof-term at $TESTDIR/Logic#Prove"
	    ";;; Elaborating spec at $TESTDIR/Logic#Logic"
	    ";; ensure-directories-exist: creating $TESTDIR/Snark/Logic/Prove.log"
	    ";; Directory $TESTDIR\\Snark\\ does not exist, will create."
	    ";; Directory $TESTDIR\\Snark\\Logic\\ does not exist, will create."
	    "Prove: Conjecture Logic.TRUE in Logic is Proved! using simple inequality reasoning."
	    "    Snark Log file: $TESTDIR/Snark/Logic/Prove.log"
	    ""))

 )