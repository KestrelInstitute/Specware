(test-directories ".")

(test 

 ("Bug 0011 : Consider abbreviating printed path names."
  :show "abc"
  :output '(";;; Elaborating spec at $TESTDIR/abc"
            ";;; Elaborating spec at $TESTDIR/xyz"
            (:optional "")
            "spec  "
            (:optional "")
            " import xyz"
            (:optional "")
            (:alternatives "endspec" "end-spec")
            (:optional "")
            (:optional "")
            ))

 )
