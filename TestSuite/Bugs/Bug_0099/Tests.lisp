(test-directories ".")

(test 

 ("Bug 0099 : Extra 'let' in generated proof obligation"
  :show   "MinusOb#MinusProof" 
  :output ";;; Elaborating proof-term at $TESTDIR/MinusOb#MinusProof
;;; Elaborating obligator at $TESTDIR/MinusOb#ONat
;; ensure-directories-exist: creating $TESTDIR/Snark/MinusOb/MinusProof.log
;; Directory $TESTDIR/Snark/ does not exist, will create.
;; Directory $TESTDIR/Snark/MinusOb/ does not exist, will create.
MinusProof: Conjecture minus_def2_Obligation in ONat is Proved! using Snark.
    Snark Log file: $TESTDIR/Snark/MinusOb/MinusProof.log


")

 )
