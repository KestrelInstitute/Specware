(test-directories ".")

(test 

 ("Bug 0021 : Ambiguous results from colimit operation"
  :sw "AmbiguousOp#E"
  :output ";;; Elaborating spec at $TESTDIR/AmbiguousOp#E
;;; Elaborating diagram-colimit at $TESTDIR/AmbiguousOp#D
;;; Elaborating diagram-term at $TESTDIR/AmbiguousOp#D
;;; Elaborating spec-morphism at $TESTDIR/AmbiguousOp#D
;;; Elaborating spec at $TESTDIR/AmbiguousOp#B
;;; Elaborating spec at $TESTDIR/AmbiguousOp#A
;;; Elaborating spec-morphism at $TESTDIR/AmbiguousOp#D
;;; Elaborating spec at $TESTDIR/AmbiguousOp#C
Errors in $TESTDIR/AmbiguousOp.sw
24.7-24.7	: Type reference a is ambiguous among C.a, {e, A.a, C.b}
24.12-24.12	: Type reference b is ambiguous among A.b, {e, A.a, C.b}
")

 )
