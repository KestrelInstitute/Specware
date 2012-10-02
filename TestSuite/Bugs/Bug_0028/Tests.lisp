(test-directories ".")

(test 

 ("Bug 0028 : A few type names such as Filename are mysteriously problematic."
  :show "ProblematicTypes"
  :output '(";;; Elaborating spec at $TESTDIR/ProblematicTypes"
            (:optional "")
	    "spec  "
            (:optional "")
	    " type Filename = String"
            (:optional "")
	    " type LineColumn = Nat"
            (:optional "")
	    " type LineColumnByte = Nat"
            (:optional "")
	    " type Position = Nat"
            (:optional "")
            (:alternatives "endspec" "end-spec")
            (:optional "")
            (:optional "")
	    ))
 )
