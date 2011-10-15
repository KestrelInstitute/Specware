(test-directories ".")

(test 

 ("Bug 0090 : Insufficient context to type-check case branches"
  :show   "caseContext#O"
  :output '(";;; Elaborating obligator at $TESTDIR/caseContext#O"
	    ";;; Elaborating spec at $TESTDIR/caseContext#S"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    (:optional "")
	    "spec"
	    (:optional " import /Library/Base/WFO")
	    (:optional "")
	    " op  f : [a] List(a) -> Nat"
	    (:optional "")
	    " conjecture f_Obligation_subtype is [a] "
	    (:optional "")
            (:alternatives
             "    fa(l : List(a)) ~(l = []) => posNat?(length l)"
             ("  fa(l : List(a)) "
              "   ~(l = []) && length l >= 0 => posNat?(length l)"))
	    (:optional "")
            (:alternatives
             " def f l = (case l"
             (" def f (l : List(a)) : Nat"
              "   = case l"))
            "      of [] -> 0"
            "      | _ -> (100 div length l)"
	    (:optional "")
 	    "endspec"
	    (:optional "")
	    (:optional "")))
 )

