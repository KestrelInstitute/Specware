(test-directories ".")

(test 

 ("Bug 0140 : Obligation of morphism into debugger"
  :sw "STO#O"
;  :show "STO#O"
  :output '(";;; Elaborating obligator at $TESTDIR/STO#O"
	    ";;; Elaborating spec-morphism at $TESTDIR/STO#O"
	    ";;; Elaborating spec at $TESTDIR/STO#S"
	    ";;; Elaborating spec at $TESTDIR/STO#T"
;            ""
;            "spec  "
;            " import $TESTDIR/STO#T"
;            " conjecture c_def is fa() c = c"
;            "endspec"
	    ""))

 )