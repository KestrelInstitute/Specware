(test-directories ".")

(test 

 ("Bug 0118 : Equivalence of Pi types failing"
  :show   "EquivSorts#D"
  :output '(
	    ";;; Elaborating spec at $TESTDIR/EquivSorts#D"
	    ";;; Elaborating spec at $TESTDIR/EquivSorts#A"
	    ";;; Elaborating spec at $TESTDIR/EquivSorts#B"
	    ";;; Elaborating spec at $TESTDIR/EquivSorts#C"
	    ""
	    "spec  "
	    " import C"
	    " import B"
	    " import A"
	    "endspec"
	    ""
	    ""))

 )