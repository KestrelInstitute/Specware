(test-directories ".")

(test 

 ("Bug 0148:  UnitId parsing error when # name includes a number."
  :show  "ImportNum#B2"
  :output '(
	    (:optional ";;; Elaborating spec at $TESTDIR/ImportNum#B2")
	    (:optional ";;; Elaborating spec at $TESTDIR/ImportNum#A1")
	    (:optional " ")
	    "spec  "
	    " import ImportNum#A1"
	    "endspec"
	    (:optional "")
	    (:optional "")
	    ))

 )
