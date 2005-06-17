(test-directories ".")

(test 

 ("Bug 0093 : No check on clashing defs in colimit"
  :show   "IncompatColimit"
  :output '(";;; Elaborating spec at $TESTDIR/IncompatColimit#I"
	    ";;; Elaborating spec at $TESTDIR/IncompatColimit#I1"
	    ";;; Elaborating spec at $TESTDIR/IncompatColimit#I2"
	    ";;; Elaborating diagram-colimit at $TESTDIR/IncompatColimit#NN1N2"
	    ";;; Elaborating diagram-term at $TESTDIR/IncompatColimit#NN1N2"
	    ";;; Elaborating spec-morphism at $TESTDIR/IncompatColimit#NN1N2"
	    ";;; Elaborating spec-morphism at $TESTDIR/IncompatColimit#NN1N2"
	    "Type error: "
	    ""
	    "Ambiguous ops:"
	    ""
	    " (* Warning: Multiple definitions for following op *) "
	    " op  i : Nat"
	    " def i ="
	    "  2"
	    " def i ="
	    "  1"
	    ""
	    " found in $TESTDIR/IncompatColimit.sw"
	    "13.16-19.0"))

 )
