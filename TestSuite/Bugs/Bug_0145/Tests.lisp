(test-directories ".")

(test ("Bug 145. Failure to disambiguate in op declaration without definition"
       :sw "ambigLt"
       :output ";;; Elaborating spec at $TESTDIR/ambigLt
"))