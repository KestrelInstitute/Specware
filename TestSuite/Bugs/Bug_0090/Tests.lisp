(test-directories ".")

(test 

 ("Bug 0090 : Insufficient context to type-check case branches"
  :show   "caseContext#O"
  :output '(";;; Elaborating obligator at $TESTDIR/caseContext#O"
	    ";;; Elaborating spec at $TESTDIR/caseContext#S"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    ""
	    "spec  "
	    (:optional " import /Library/Base/WFO")
	    " "
	    " op  f : [a] List(a) -> Nat"
            ""
	    " conjecture f_Obligation_subtype is [a] "
	    "    fa(l : List(a)) ~(l = []) && length l >= 0 => posNat?(length l)"
	    " "
	    " def f l = (case l"
	    "              of [] -> 0"
 	    "               | _ -> 100 div length l)"
 	    "endspec"
	    ""
	    ""))
 )

