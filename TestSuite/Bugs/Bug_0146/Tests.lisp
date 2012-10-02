(test-directories ".")

(test 

 ("Bug 0146 : Code for nonconstructive definitions is generated."
  :swl  "NonConstructive"
  :output '(";;; Elaborating spec at $TESTDIR/NonConstructive"
	    "<some kind of error message about loser>"
	    (:optional ";;; Generating lisp file $TESTDIR/lisp/NonConstructive.lisp")
	    (:optional "creating directory: $TESTDIR/lisp/")
            (:optional "WARNING: Non-constructive def for List-Spec::lengthOfListFunction")
	    (:optional "WARNING: Non-constructive def for List-Spec::definedOnInitialSegmentOfLength-2")
	    (:optional "WARNING: Non-constructive def for Function-Spec::wellFounded?")
	    (:optional "WARNING: Non-constructive def for Function-Spec::inverse-1-1")
	    (:optional "WARNING: Non-constructive def for Function-Spec::surjective?")
	    (:optional "WARNING: Non-constructive def for Function-Spec::injective?")
	    ""))

 )
