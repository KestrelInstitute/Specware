(test-directories ".")

(test 

 ("Bug 0104 : Erroneous code for non-constructive expression."
  :swl  "NonConstructive"
  :output '(";;; Elaborating spec at $TESTDIR/NonConstructive"
	    "<some kind of error message>"
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/lisp/NonConstructive.lisp")
	    (:optional ";; Directory $TESTDIR/lisp/ does not exist, will create.")
	    ""))

 )
