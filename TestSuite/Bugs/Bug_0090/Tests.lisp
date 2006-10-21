(test-directories ".")

(test 

 ("Bug 0090 : Insufficient context to type-check case branches"
  :show   "caseContext#O"
  :output '(";;; Elaborating obligator at $TESTDIR/caseContext#O"
	    ";;; Elaborating spec at $TESTDIR/caseContext#S"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    ""
	    "spec  "
	    " import /Library/Base/WFO"
	    " "
	    " op  f : [a] List(a) -> Nat"
	    " conjecture f_Obligation_subsort is [a] "
	    "    fa(l : List(a)) ~(l = []) && natural?(length l) => length l ~= 0"
	    " conjecture f_Obligation_subsort0 is [a] "
	    "    fa(l : List(a)) ~(l = []) => natural?(100 div length l)"
	    " "
	    " def f l = (case l"
	    "              of [] -> 0"
	    "               | _ -> 100 div length l)"
	    "endspec"
	    ""
	    ""))
 )

