(test-directories ".")

(test 
  ("Bug 0145 : Unambiguous < in subtype becomes ambiguous by commenting out def"
   :sw "ambigLt"
   :output '((:optional "")
             ";;; Elaborating spec at $TESTDIR/ambigLt"
             (:optional "")
             ))
 )
