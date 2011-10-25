(test-directories ".")

(test 

 ("Bug 0045 : Unambiguous op erroneously declared ambiguous [toString]" 
  :sw  "ToString"
  :output '(";;; Elaborating spec at $TESTDIR/ToString"))

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
            (:alternatives "endspec" "end-spec")
            (:optional "")
            "    ->"
            "    spec  "
            " type A"
            " type B"
            " op A.flop : A -> A"
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
