(test-directories ".")

(test 

 ("Bug 0057 : In elaborating unit in multiple-unit file, all other units get elaborated (possibly again) as well, even if not relevant"
  :show "UnusedSpecs#D"
  :output '(";;; Elaborating spec at $TESTDIR/UnusedSpecs#D"
	    ";;; Elaborating spec at $TESTDIR/UnusedSpecs#C"
	    ";;; Elaborating spec at $TESTDIR/UnusedSpecs#B"
	    ";;; Elaborating spec at $TESTDIR/UnusedSpecs#A"
	    ""
	    "spec  "
	    " import C"
	    " type D"
	    "endspec"
	    ""
	    ""))


 )
