(test-directories ".")

(test 

 ("Bug 0017 : Incorrect colimit computed"
  :show "AAcol#C"
  :output '(";;; Elaborating diagram-colimit at $TESTDIR/AAcol#C"
	    ";;; Elaborating diagram-term at $TESTDIR/AAcol#D"
	    ";;; Elaborating spec at $TESTDIR/AAcol#A"
	    (:optional "")
	    "spec  "
	    (:optional "")
            (:alternatives
             "op  X.fubaz: Nat = 12345"
             "op  X.fubaz : Nat = 12345"
             )
	    (:optional "")
            (:alternatives
             " op  Y.fubaz : Nat = 12345"
             " op  Y.fubaz: Nat = 12345")
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))


 )
