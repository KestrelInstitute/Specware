(test-directories ".")

(test 

 ("Bug 0003 : Some inconsistencies with using :sw command and with the # notation"
  :sw "ABC"
  :output '(";;; Elaborating spec at $TESTDIR/ABC#A"
	    ";;; Elaborating spec at $TESTDIR/ABC#B"
	    ";;; Elaborating spec at $TESTDIR/ABC#C"
	    ""))

 )
