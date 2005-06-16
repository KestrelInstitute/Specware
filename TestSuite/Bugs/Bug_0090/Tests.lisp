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
	    " conjecture f_Obligation is [a] "
	    "    fa(P : List(a)) natural?(length P) => length P ~= 0"
	    " conjecture f_Obligation0 is [a] fa(P : List(a)) natural?(100 div length P)"
	    " "
	    " def f l = (case l"
	    "              of [] -> 0"
	    "               | _ -> 100 div length l)"
	    "endspec"
	    ""
	    ""))
 )

