(test-directories ".")

(test 

 ("Bug 0146 : Code for nonconstructive definitions is generated."
  :swl  "NonConstructive"
  :output '(";;; Elaborating spec at $TESTDIR/NonConstructive"
	    "<some kind of error message>"
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/lisp/NonConstructive.lisp")
	    (:optional ";; Directory $TESTDIR/lisp/ does not exist, will create.")
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::inverse-1-1")
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::surjective?")
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::injective?")
	    ""))

 )
