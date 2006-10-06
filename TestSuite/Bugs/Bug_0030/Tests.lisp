(test-directories ".")

(test 

 ("Bug 0030 : system crashes with seg. fault when compiling the following specs"
  :sw "WasCausingSegFault"
  :output '(";;; Elaborating spec at $TESTDIR/WasCausingSegFault#BinaryRel"
	    ";;; Elaborating spec at $TESTDIR/WasCausingSegFault#BinaryOp"
	    ";;; Generating lisp file $TESTDIR/lisp/WasCausingSegFault.lisp"
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/lisp/WasCausingSegFault.lisp")
	    (:optional ";; ensure-directories-exist: creating")
	    (:optional ";;   $TESTDIR/lisp/WasCausingSegFault.lisp")
	    (:optional "creating directory: $TESTDIR/lisp/")
	    (:optional ";; Directory $TESTDIR/lisp/ does not exist, will create.")
	    ";;; Generating lisp file $TESTDIR/lisp/WasCausingSegFault.lisp"
	    ""))

 )
