(test-directories ".")

(test 

 ("Bug 0118 : Equivalence of Pi types failing"
  :show   "EquivSorts#C"
  :output '(
	    ";;; Elaborating spec at $TESTDIR/EquivSorts#C"
	    ";;; Elaborating spec at $TESTDIR/EquivSorts#A"
	    ";;; Elaborating spec at $TESTDIR/EquivSorts#B"
	    ""
	    "spec  "
	    " import B"
	    " import A"
	    "endspec"
	    ""
	    ""))

 )