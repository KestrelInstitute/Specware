(test-directories ".")

(test 

 ("Bug 0143 : Parentheses in prettyprinted output."
  :show "Pretty"
  :output '(";;; Elaborating spec at $TESTDIR/Pretty"
	    ""
	    "spec  "
	    " axiom A is (ex(x : Boolean) x) => false"
	    " axiom B is (let zero = 1 in "
	    "             zero) = zero"
	    " axiom C is (if true then 1 else 2) + 3 = 4"
	    "endspec"
	    ""
 	    ""))

 )