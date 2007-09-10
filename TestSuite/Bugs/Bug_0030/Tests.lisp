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
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::inverse-1-1")
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::surjective?")
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::injective?")
	    ";;; Generating lisp file $TESTDIR/lisp/WasCausingSegFault.lisp"
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::inverse-1-1")
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::surjective?")
	    (:optional "WARNING: Non-constructive def for FUNCTIONS::injective?")
	    ""))

 )
