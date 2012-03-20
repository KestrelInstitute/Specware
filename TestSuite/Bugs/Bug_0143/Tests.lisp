(test-directories ".")

(test 

 ("Bug 0143 : Parentheses in prettyprinted output."
  :show "Pretty"
  :output '(";;; Elaborating spec at $TESTDIR/Pretty"
	    (:optional "")
	    "spec  "
	    (:optional "")
	    "axiom A is (ex(x: Bool) x) => false"
	    (:optional "")
	    "axiom B is (let zero = 1 in "
	    "             zero) = zero"
	    (:optional "")
	    "axiom C is (if true then 1 else 2) + 3 = 4"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
 	    ))

 )
