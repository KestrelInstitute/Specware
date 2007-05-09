(test-directories ".")

(test ("Bug 145. Unambiguous < in subtype becomes ambiguous by commenting out def"
       :sw "ambigLt"
       :output ";;; Elaborating spec at $TESTDIR/ambigLt
"))