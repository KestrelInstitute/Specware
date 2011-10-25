(test-directories ".")

(test 

 ("Bug 0007 :Order of units in multiple-unit file matters."
  :show "ManySpecs#D"
  :output '(";;; Elaborating spec at $TESTDIR/ManySpecs#D"
	    ";;; Elaborating spec at $TESTDIR/ManySpecs#C"
	    ";;; Elaborating spec at $TESTDIR/ManySpecs#B"
	    ";;; Elaborating spec at $TESTDIR/ManySpecs#A"
	    (:optional "")
	    "spec"
	    (:optional "")
	    " import C"
	    (:optional "")
	    " type D"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))


 )
