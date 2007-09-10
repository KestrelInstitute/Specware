(test-directories ".")

(test 

 ("Bug 0018 : Cannot generate code from colimit"
  :sw "BBcol#K"
  :output '(";;; Elaborating diagram-colimit at $TESTDIR/BBcol#K"
	    ";;; Elaborating diagram-term at $TESTDIR/BBcol#K"
	    ";;; Elaborating spec at $TESTDIR/BBcol#A"
	    ";;; Generating lisp file $TESTDIR/lisp/BBcol.lisp"
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/lisp/BBcol.lisp")
	    (:optional "creating directory: $TESTDIR/lisp/")
	    (:optional ";; Directory $TESTDIR/lisp/ does not exist, will create.")
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::inverse-1-1")
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::surjective?")
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::injective?")
	    ""))

 )