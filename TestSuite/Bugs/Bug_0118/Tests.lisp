(test-directories ".")

(test 

 ("Bug 0118 : Equivalence of Pi types failing"
  :show   "EquivTypes#D"
  :output '(
	    ";;; Elaborating spec at $TESTDIR/EquivTypes#D"
	    ";;; Elaborating spec at $TESTDIR/EquivTypes#A"
	    ";;; Elaborating spec at $TESTDIR/EquivTypes#B"
	    ";;; Elaborating spec at $TESTDIR/EquivTypes#C"
	    (:optional "")
	    "spec  "
	    (:optional "")
	    " import A"
	    " import B"
	    " import C"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))

 )
