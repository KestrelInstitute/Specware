(test-directories ".")

(test 

 ("Bug 0099 : Extra 'let' in generated proof obligation"
  :show   "MinusOb#MinusProof" 
  :output '(
	    ";;; Elaborating proof-term at $TESTDIR/MinusOb#MinusProof"
	    ";;; Elaborating obligator at $TESTDIR/MinusOb#ONat"
	    "    Expanded spec file: $TESTDIR/Snark/MinusOb/MinusProof.sw"
	    "    Snark Log file: $TESTDIR/Snark/MinusOb/MinusProof.log"
	    "MinusProof: Conjecture minus_def2_Obligation in ONat is Proved! using Snark."
	    ""
	    ""
	    ""))

 )
