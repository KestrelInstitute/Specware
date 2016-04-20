(test-directories ".")

(test 

 ("Bug 0110 : [] read as bogus Nil [Winner]"
  :sw  "BogusNil#Winner"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil#Winner"
	    (:optional "")))

 ("Bug 0110 : [] read as bogus Nil [Loser]"
  :sw "BogusNil#Loser"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil#Loser"
	    "ERROR: Errors in $TESTDIR/BogusNil.sw"
	    "14.21-14.22	: Could not match type constraint"
	    "                  [] of type List(mtv*)"
	    "          with expected type Bogus"
	    (:optional "")))
	    

 ("Bug 0110 : [] read as bogus Nil [Loser2]"
  :sw "BogusNil#Loser2"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil#Loser2"
	    "ERROR: Errors in $TESTDIR/BogusNil.sw"
	    "20.*-20.14	: Incomplete type for op loser:"
	    "mtv*"
	    (:optional 
             "20.*-20.14	: Incomplete type for op loser:"
             "mtv*")
	    (:optional "")))

 )
