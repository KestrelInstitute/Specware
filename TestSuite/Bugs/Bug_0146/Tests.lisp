(test-directories ".")

(test 

 ("Bug 0146 : Code for nonconstructive definitions is generated."
  :swl  "NonConstructive"
  :output '("<some kind of error message>"
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/lisp/NonConstructive.lisp")
	    (:optional ";; Directory $TESTDIR/lisp/ does not exist, will create.")
	    ""))

 )
