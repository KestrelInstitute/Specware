(test-directories ".")

(test 

 ("Bug 0146 : Erroneous code for non-constructive expression."
  :swl  "NonConstructive"
  :output '(";;; Code for nonconstructive definitions is generated."
	    "<some kind of error message>"
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/lisp/NonConstructive.lisp")
	    (:optional ";; Directory $TESTDIR/lisp/ does not exist, will create.")
	    ""))

 )
