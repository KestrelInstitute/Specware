(test-directories ".")

(test 

 ("Bug 0110 : [] read as bogus Nil [Winner]"
  :sw  "BogusNil#Winner"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil#Winner"
	    ""))

 ("Bug 0110 : [] read as bogus Nil [Loser]"
  :sw "BogusNil#Loser"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil#Loser"
	    "Errors in $TESTDIR/BogusNil.sw"
	    "14.21-14.22	: Could not match type constraint"
	    "                  [] of type List(mtv%parser%12)"
	    "          with expected type Bogus"
	    ""))

 ("Bug 0110 : [] read as bogus Nil [Loser2]"
  :sw "BogusNil#Loser2"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil#Loser2"
	    "Errors in $TESTDIR/BogusNil.sw"
	    "20.1-20.14	: Incomplete type for op loser:"
	    "mtv%parser%14"
	    ""))

 )
