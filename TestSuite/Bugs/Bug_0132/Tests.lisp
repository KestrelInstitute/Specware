(test-directories ".")

(test 

 ("Bug 0132 : Obligation for the"
  :show "theOblig#O"
  :output '(";;; Elaborating obligator at $TESTDIR/theOblig#O"
	    ";;; Elaborating spec at $TESTDIR/theOblig#S"
            ""
            "spec  "
            " import S"
	    " import /Library/Base/WFO"
            " conjecture f_Obligation is "
	    "    fa(n : Nat) uniquelySatisfied?((fn m -> m = n))"
            "endspec"
	    ""
	    ""))

 )