(test-directories ".")

(test 

 ("Bug 0105 A: The new-style type quantifications in claim definitions are ambiguous"
  :show   "QuantifiedAxiom#A"
  :output '(";;; Elaborating spec at $TESTDIR/QuantifiedAxiom#A"
	    (:optional "")
	    "spec"
	    (:optional "")
	    " op  f infixl 22 : [a] List(a) * a -> Integer"
	    (:optional "")
	    " op i : Nat = 123"
	    (:optional "")
	    " axiom A is [i] f 3 = 0"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
            ))


 ("Bug 0105 B: The new-style type quantifications in claim definitions are ambiguous"
  :show   "QuantifiedAxiom#B"
  :output '(";;; Elaborating spec at $TESTDIR/QuantifiedAxiom#B"
	    "Errors in $TESTDIR/QuantifiedAxiom.sw"
            (:alternatives

             ("13.16-13.22	: Incomplete type for f (3) = 0:"
              "mtv%metafy%*"
              "13.18-13.18	: Could not match type constraint"
              "                   3 of type Nat"
              "          with expected type List(mtv%metafy%*) * mtv%metafy%*")

             ("13.16-13.16	: Could not match type constraint"
              "                   f of type List(mtv%metafy%7) * mtv%metafy%7 -> Integer"
              "          with expected type Nat -> Integer"
              "13.16-13.22	: Incomplete type for f (3) = 0:"
              "mtv%metafy%7")

             )
            (:optional "")
            ))


 ("Bug 0105 C: The new-style type quantifications in claim definitions are ambiguous"
  :show   "QuantifiedAxiom#C"
  :output '(";;; Elaborating spec at $TESTDIR/QuantifiedAxiom#C"
	    (:optional "")
	    "spec"
	    (:optional "")
	    " op  f infixl 22 : [a] a -> Integer"
	    (:optional "")
	    " op  i : Nat = 123"
	    (:optional "")
	    " axiom A is [i] f(3) = 0"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
            ))

 )
