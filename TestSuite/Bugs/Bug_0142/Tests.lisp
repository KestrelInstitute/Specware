(test-directories ".")

(test 

 ("Bug 0142 : Projections were printed out incorrectly"
  :show "Ob#BadObl1"
  :output '(";;; Elaborating obligator at $TESTDIR/Ob#BadObl1"
	    ";;; Elaborating spec-morphism at $TESTDIR/Ob#BadObl1"
	    ";;; Elaborating spec at $TESTDIR/Ob#S"
	    ";;; Elaborating spec at $TESTDIR/Ob#T"
	    (:optional "")
	    "spec  "
	    " import $TESTDIR/Ob#T"
	    ;; " conjecture pp is project b (project a (z)) = 0"
            ""
	    " conjecture pp is (z.a).b = 0"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
 	    ))

 )
