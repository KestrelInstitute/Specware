(test-directories ".")

(test 

 ("Bug 0021 : Ambiguous results from colimit operation"
  :sw "AmbiguousOp#E"
  :output '(";;; Elaborating spec at $TESTDIR/AmbiguousOp#E"
	    ";;; Elaborating diagram-colimit at $TESTDIR/AmbiguousOp#D"
	    ";;; Elaborating diagram-term at $TESTDIR/AmbiguousOp#D"
	    ";;; Elaborating spec-morphism at $TESTDIR/AmbiguousOp#D"
	    ";;; Elaborating spec at $TESTDIR/AmbiguousOp#B"
	    ";;; Elaborating spec at $TESTDIR/AmbiguousOp#A"
	    ";;; Elaborating spec-morphism at $TESTDIR/AmbiguousOp#D"
	    ";;; Elaborating spec at $TESTDIR/AmbiguousOp#C"
	    "ERROR: Errors in $TESTDIR/AmbiguousOp.sw"
	    (:alternatives
	     "24.7-24.7	: Type reference a is ambiguous among C.a, {C.b, A.a, e}"
	     "24.7-24.7	: Type reference a is ambiguous among {C.b, A.a, e}, C.a")
	    (:alternatives
	     "24.12-24.12	: Type reference b is ambiguous among A.b, {C.b, A.a, e}"
	     "24.12-24.12	: Type reference b is ambiguous among {C.b, A.a, e}, A.b")
	    ""))

 )
