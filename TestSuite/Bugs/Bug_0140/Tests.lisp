(test-directories ".")

(test 

 ("Bug 0140 : Obligation of morphism into debugger"
  :sw "STO#O"
  ;;  :show "STO#O"
  :output '(";;; Elaborating obligator at $TESTDIR/STO#O"
	    ";;; Elaborating spec-morphism at $TESTDIR/STO#O"
	    ";;; Elaborating spec at $TESTDIR/STO#S"
	    ";;; Elaborating spec at $TESTDIR/STO#T"
	    ;; new...
	    "Error in morphism: Inconsistent op def mapping for c +-> c"
	    "The domain op     c has a definition: c"
	    "but translates to c, which does not."
	    " found in $TESTDIR/STO.sw"
	    "21.25-21.25"
	    ;; old..
	    ;; ""
	    ;; "spec  "
	    ;; " import $TESTDIR/STO#T"
	    ;; " conjecture c_def is fa() c = c"
	    ;; "endspec"
	    ;; ""
	    ))

 )