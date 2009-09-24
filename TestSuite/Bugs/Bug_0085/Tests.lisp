(test-directories ".")

(test 
 ("Bug 0085 : Proof obligations for quotient pattern are now generated"
  :show   "quotpat#O" 
  :output '(";;; Elaborating obligator at $TESTDIR/quotpat#O"
	    ";;; Elaborating spec at $TESTDIR/quotpat#S"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    (:optional "")
	    "spec  "
	    (:optional " import /Library/Base/WFO")
	    " "
	    " op  eq_mod10 : Nat * Nat -> Boolean"
            " def eq_mod10 (n1, n2) = n1 rem 10 = n2 rem 10"
            " "
            " conjecture eq_mod10_transitive is "
            "    fa(x : Nat, y : Nat, z : Nat) "
            "     eq_mod10(x, y) && eq_mod10(y, z) => eq_mod10(x, z)"
            " "
            " conjecture eq_mod10_symmetric is "
            "    fa(x : Nat, y : Nat) eq_mod10(x, y) => eq_mod10(y, x)"
            " "
            " conjecture eq_mod10_reflexive is fa(x : Nat) eq_mod10(x, x)"
            " "
            " type Q = (Nat / eq_mod10)"
            " "
            " op f : Q -> Nat"
            " "
            " conjecture f_Obligation_subtype is "
	    (:alternatives
	     ("    fa(x : Q, y : Int) "
	      "     natural? y && x = quotient[Q]  y => natural?(y + 1)")
	     "    fa(x : Q, y : Int) y >= 0 && x = quotient[Q]  y => y + 1 >= 0")
            " "
            " conjecture f_Obligation_quotient is "
            "    fa(y__1 : Nat, y__2 : Nat) "
            "     quotient[Q]  y__1 = quotient[Q]  y__2 => y__1 + 1 = y__2 + 1"
            " "
            " def f x = let quotient[Q] y = x in "
            "           y + 1"
            " "
            " op g : Q -> Nat"
            " "
	    (:alternatives
	     " conjecture g_Obligation_subtype0 is fa(y : Nat) natural?(y + 1)"
	     " conjecture g_Obligation_subtype0 is fa(y : Nat) y + 1 >= 0")
            " "
            " conjecture g_Obligation_subtype is "
            "    fa(m : Nat, n : Nat) eq_mod10(m, n) => m + 1 = n + 1"
            " "
            " def g x = choose[Q] ((fn y : Nat -> y + 1)) x"
            " "
            " op f2 : Q -> List(Nat)"
            " "
            " conjecture f2_Obligation_subtype is "
	    (:alternatives
	     ("    fa(x : Q, y : Int) "
	      "     natural? y && x = quotient[Q]  y => natural?(y + 1)")
	     "    fa(x : Q, y : Int) y >= 0 && x = quotient[Q]  y => y + 1 >= 0")
            " "
            " conjecture f2_Obligation_quotient is "
            "    fa(y__1 : Nat, y__2 : Nat) "
            "     quotient[Q]  y__1 = quotient[Q]  y__2 => [y__1 + 1] = [y__2 + 1]"
            " "
            " def f2 x = let quotient[Q] y = x in "
            "            [y + 1]"
            " "
            " op g2 : Q -> List(Nat)"
            " "
	    (:alternatives
	     " conjecture g2_Obligation_subtype0 is fa(y : Nat) natural?(y + 1)"
	     " conjecture g2_Obligation_subtype0 is fa(y : Nat) y + 1 >= 0")
            " "
            " conjecture g2_Obligation_subtype is "
            "    fa(m : Nat, n : Nat) eq_mod10(m, n) => [m + 1] = [n + 1]"
            " "
            " def g2 x = choose[Q] ((fn y : Nat -> [y + 1])) x"

	    (:optional " ")
	    "endspec"
	    (:optional "")
	    (:optional "")
	    ))
 )
