(test-directories ".")

(test 

 ("Bug 0045 : Unambiguous op erroneously declared ambiguous [show]" 
  :sw  "Show"
  :output '((:optional "")
            ";;; Elaborating spec at $TESTDIR/Show"
            (:optional "")
            ))

 ("Bug 0045 : Unambiguous op erroneously declared ambiguous [FlipFlop]"
  :show   "Flop#FlipFlopImplementation" 
  :output '(";;; Elaborating spec-morphism at $TESTDIR/Flop#FlipFlopImplementation"
            ";;; Elaborating spec at $TESTDIR/Flop#Flip"
            ";;; Elaborating spec at $TESTDIR/Flop#Flop"
            ";;; Elaborating spec at $TESTDIR/Flop#FlipFlopImplementation"
            (:optional "")
            "morphism"
            "    spec  "
            " type Flip"
            " op flip : Flip -> Flip"
            (:optional "")
            (:alternatives "endspec" "end-spec")
            (:optional "")
            "    ->"
            "    spec  "
            (:optional "")
            " type A"
            (:optional "")
            " type B"
            (:optional "")
            " op A.flop : A -> A"
            (:optional "")
            " op B.flop : B -> B"
            (:alternatives "endspec" "end-spec")
            (:optional "")
            "    {type Flip"
            "     +->"
            "     A,"
            "     op flip"
            "     +->"
            "     flop}"
            (:optional "")
            (:optional "")
            ))
 )
