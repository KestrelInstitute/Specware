(test-directories ".")

(test 

 ("Bug 0017 : Incorrect colimit computed"
  :show "AAcol#C"
  :output '(";;; Elaborating diagram-colimit at $TESTDIR/AAcol#C"
	    ";;; Elaborating diagram-term at $TESTDIR/AAcol#D"
	    ";;; Elaborating spec at $TESTDIR/AAcol#A"
	    ""
	    "spec  "
	    " "
	    (:optional " op  X.fubaz : Nat")
	    " def X.fubaz = 12345"
	    " "
	    (:optional " op  Y.fubaz : Nat")
	    " def Y.fubaz = 12345"
	    "endspec"
	    ""
	    ""
	    ""))

 )
