(test-directories ".")

(test 

 ("Bug 0093 : No check on clashing defs in colimit"
  :show   "IncompatColimit.sw" 
  :output ";;; Elaborating spec at $TESTDIR/IncompatColimit#I
;;; Elaborating spec at $TESTDIR/IncompatColimit#I1
;;; Elaborating spec at $TESTDIR/IncompatColimit#I2
;;; Elaborating diagram-colimit at $TESTDIR/IncompatColimit#NN1N2
;;; Elaborating diagram-term at $TESTDIR/IncompatColimit#NN1N2
;;; Elaborating spec-morphism at $TESTDIR/IncompatColimit#NN1N2
;;; Elaborating spec-morphism at $TESTDIR/IncompatColimit#NN1N2
Type error: 

Ambiguous ops:  op i : Nat
 (* Warning: Multiple definitions for following op *) 
 def i =
  2
 def i =
  1

 found in $TESTDIR/IncompatColimit.sw
13.16-19.0")

 )
