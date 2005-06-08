(test-directories ".")

(test 
 ("Bug 0092 : Useless import of WFO"
  :show   "BogusImport#O" 
  :output '(";;; Elaborating obligator at $TESTDIR/BogusImport#O"
	    ";;; Elaborating spec at $TESTDIR/BogusImport#S"
	    ""
	    "spec  "
	    "endspec"
	    ""
	    ""))
 

