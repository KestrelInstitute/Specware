(test-directories ".")

(test 

 ("Bug 0134 : Unbound variable in proof Obligation"
  :show "fold#O"
  :output '(";;; Elaborating obligator at $TESTDIR/fold#O"
	    ";;; Elaborating spec at $TESTDIR/fold#S"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
            ""
            "spec  "
            " import S"
	    " import /Library/Base/WFO"
            " conjecture fold_Obligation is [a, b] "
	    "    uniquelySatisfied?"
	    "      ((fn fold -> "
	    "           (fa(c : b, f : b * a -> b) fold(empty, c, f) = c) "
	    "           && (fa(s : FSet(a), x : a, c_1 : b, f_1 : b * a -> b) "
	    "                (foldable?(s with x, c_1, f_1) "
	    "                => fold(s with x, c_1, f_1) "
	    "                   = f_1(fold(s wout x, c_1, f_1), x)))))"
	    " conjecture fold_Obligation0 is [a, b] "
	    "    fa(c : b, f : b * a -> b) foldable?(empty, c, f)"
	    " conjecture fold_Obligation1 is [a, b] "
	    "    fa(fold : ((FSet(a) * b * (b * a -> b)) | foldable?) -> b, s : FSet(a), "
	    "       x : a, c_1 : b, f_1 : b * a -> b) "
	    "     (fa(c : b, f : b * a -> b) fold(empty, c, f) = c) "
	    "     && foldable?(s with x, c_1, f_1) => foldable?(s wout x, c_1, f_1)"
            "endspec"
	    ""
	    ""))

 )