(test-directories ".")

(test 

 ("Bug 0030 : system crashes with seg. fault when compiling the following specs"
  :sw "WasCausingSegFault"
  :output ";;; Elaborating spec at $TESTDIR/WasCausingSegFault#BinaryRel
;;; Elaborating spec at $TESTDIR/WasCausingSegFault#BinaryOp
;;; Generating lisp file $TESTDIR/lisp/WasCausingSegFault.lisp
;;; Generating lisp file $TESTDIR/lisp/WasCausingSegFault.lisp
")

 )
