(test-directories ".")

(test 

 ("Bug 0093 : No check on clashing defs in colimit"
  :show   "IncompatColimit"
  :output '(

	    ";;; Elaborating diagram-colimit at $TESTDIR/IncompatColimit#IncompatColimit"
	    ";;; Elaborating diagram-term at $TESTDIR/IncompatColimit#D"
	    ";;; Elaborating spec at $TESTDIR/IncompatColimit#I"
	    ";;; Elaborating spec at $TESTDIR/IncompatColimit#I1"
	    ";;; Elaborating spec at $TESTDIR/IncompatColimit#I2"
	    ";;; Elaborating spec-morphism at $TESTDIR/IncompatColimit#D"
	    ";;; Elaborating spec-morphism at $TESTDIR/IncompatColimit#D"
	    ""
	    "Error in colimit: "
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
	    "21.26-21.26"))
 )
