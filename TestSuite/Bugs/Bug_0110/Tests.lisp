(test-directories ".")

(test 

 ("Bug 0110 : [] read as bogus Nil"
  :show   "BogusNil"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil"
	    "Errors in $TESTDIR/BogusNil.sw"
	    "3.18-3.19	: Could not match type constraint"
	    "                  [] of type  | Cons mtv%metafy%11 * List(mtv%metafy%11) | Nil"
	    "          with expected type AA"
	    ""))

 )
