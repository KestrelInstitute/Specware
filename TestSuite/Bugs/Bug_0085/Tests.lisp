(test-directories ".")

(test 

 ("Bug 0085 : Proof obligations for quotient pattern are not generated"
  :show   "quotpat#O" 
  :output '(";;; Elaborating obligator at $TESTDIR/quotpat#O"
	    ";;; Elaborating spec at $TESTDIR/quotpat#S"
	    ";;; Elaborating spec at $SPECWARE/Library/Base/WFO"
	    ""
	    "spec  "
	    " import /Library/Base/WFO"
	    " "
	    " op  eq_mod10 : Nat * Nat -> Boolean"
	    " def eq_mod10 (n1, n2) = n1 rem 10 = n2 rem 10"
	    " conjecture eq_mod10_reflexive is fa(x : Nat) eq_mod10(x, x)"
	    " conjecture eq_mod10_symmetric is "
	    "    fa(x : Nat, y : Nat) eq_mod10(x, y) => eq_mod10(y, x)"
	    " conjecture eq_mod10_transitive is "
	    "    fa(x : Nat, y : Nat, z : Nat) "
	    "     eq_mod10(x, y) && eq_mod10(y, z) => eq_mod10(x, z)"
	    " type Q = (Nat / eq_mod10)"
	    " "
	    " op  f : Q -> Nat"
	    " conjecture f_Obligation is "
	    "    fa(x : Q, y : Nat) x = quotient eq_mod10  y => natural?(y + 1)"
	    " conjecture f_Unique is "
	    "    fa(x : Q, y : Nat, z :Nat) x = quotient eq_mod10 y & x = quotient eq_mod10 z => (y + 1) = (z + 1)"
	    " "
	    " def f x = let quotient eq_mod10 y = x in "
	    "           y + 1"
	    "endspec"
	    ""
	    ""
	    ))

 )
