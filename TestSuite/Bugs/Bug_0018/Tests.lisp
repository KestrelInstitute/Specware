(test-directories ".")

(test 

 ("Bug 0018 : Cannot generate code from colimit"
  :sw "BBcol#K"
  :output ";;; Elaborating diagram-colimit at $TESTDIR/BBcol#K
;;; Elaborating diagram-term at $TESTDIR/BBcol#K
;;; Elaborating spec at $TESTDIR/BBcol#A
;;; Generating lisp file $TESTDIR/lisp/BBcol.lisp
")

 )