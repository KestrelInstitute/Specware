(test-directories ".")

(test 

 ("Bug 0007 :Order of units in multiple-unit file matters."
  :show "ManySpecs#D"
  :output '(";;; Elaborating spec at $TESTDIR/ManySpecs#D"
	    ";;; Elaborating spec at $TESTDIR/ManySpecs#C"
	    ";;; Elaborating spec at $TESTDIR/ManySpecs#B"
	    ";;; Elaborating spec at $TESTDIR/ManySpecs#A"
	    ""
	    "spec  "
	    " import C"
	    " type D"
	    "endspec"
	    ""
	    ""))


 )
