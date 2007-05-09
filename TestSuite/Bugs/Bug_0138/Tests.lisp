(test-directories ".")

(test 

 ("Bug 0138 : Constructor called 'sub' causes type eror unless preceded by 'embed'"
  :sw "sub"
  :output '(";;; Elaborating spec at $TESTDIR/sub"
	    ""))

 )