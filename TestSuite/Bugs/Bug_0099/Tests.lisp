(test-directories ".")

(test 
  ("Bug 0099 : Extra 'let' in generated proof obligation"
   :show   "MinusOb#ONat" 
   :output '(";;; Elaborating obligator at $TESTDIR/MinusOb#ONat"
	     (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	     (:optional "creating directory: $TESTDIR/Snark/")
	     (:optional "creating directory: $TESTDIR/Snark/MinusOb/")
	     (:optional "")
	     "spec  "
	     " import /Library/Base/WFO"
	     " type Nat"
	     " "
	     " op  zero : Nat"
	     " op  succ : Nat -> Nat"
	     " axiom Nat.zero_not_succ is ~(ex(n : Nat) zero = succ n)"
	     " axiom Nat.succ_injective is "
	     "    fa(n1 : Nat, n2 : Nat) succ n1 = succ n2 => n1 = n2"
	     " axiom Nat.induction is "
	     "    fa(p : Nat -> Boolean) "
	     "     p(zero) && (fa(n : Nat) (p n => p(succ n))) => (fa(n : Nat) p n)"
	     " "
	     " op  posNat? : Nat -> Boolean"
	     " def posNat? n = n ~= zero"
	     " type PosNat = {n : Nat | posNat? n}"
	     " "
	     " op  one : Nat"
	     " def one = succ(zero)"
	     " "
	     " op  two : Nat"
	     " def two = succ(succ(zero))"
	     " "
	     " op  plus : Nat * Nat -> Nat"
	     " axiom Nat.plus_def1 is fa(n : Nat) plus(n, zero) = n"
	     " axiom Nat.plus_def2 is "
	     "    fa(n : Nat, n0 : Nat) plus(n, succ n0) = succ(plus(n, n0))"
	     " "
	     " op  lte : Nat * Nat -> Boolean"
	     " axiom Nat.lte_def1 is fa(n : Nat) lte(zero, n)"
	     " axiom Nat.lte_def2 is fa(n : Nat) ~(lte(succ n, zero))"
	     " axiom Nat.lte_def3 is "
	     "    fa(n1 : Nat, n2 : Nat) lte(succ n1, succ n2) <=> lte(n1, n2)"
	     " "
	     " op  minus : {(n1, n2) : (Nat * Nat) | lte(n2, n1)} -> Nat"
	     " conjecture Nat.minus_def1_Obligation_subsort is fa(n : Nat) lte(zero, n)"
	     " axiom Nat.minus_def1 is fa(n : Nat) minus(n, zero) = n"
	     " conjecture Nat.minus_def2_Obligation_subsort is "
	     "    fa(n1 : Nat, n2 : Nat) lte(n2, n1) => lte(succ n2, succ n1)"
	     " axiom Nat.minus_def2 is "
	     "    fa(n1 : Nat, n2 : Nat) "
	     "     lte(n2, n1) => minus(succ n1, succ n2) = minus(n1, n2)"
	     " proof Isa Thy_Morphism"
	     "   type Nat.Nat -> nat"
	     "   Nat.zero -> 0"
	     "   Nat.one -> 1"
	     "   Nat.two -> 2"
	     "   Nat.succ -> Suc"
	     "   Nat.plus -> +  Left 25"
	     "   Nat.minus -> - Left 25"
	     "   Nat.lte -> \\<le> Left 20"
	     "   Integer.>= -> \\<ge>  Left 20"
	     "  end-proof"
	     "endspec"
	     (:optional "")
	     (:optional "")
	     ))

  ("Bug 0099 : Extra 'let' in generated proof obligation -- prove obligation using Snark"
   :show   "MinusOb#MinusProof" 
   :output '((:optional ";;; Elaborating obligator at $TESTDIR/MinusOb#ONat")
	     (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	     (:optional "creating directory: $TESTDIR/Snark/")
	     (:optional "creating directory: $TESTDIR/Snark/MinusOb/")
	     ";;; Elaborating proof-term at $TESTDIR/MinusOb#MinusProof"
	     (:optional
	      ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top"
	      ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char"
	      ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare"
	      ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions"
	      ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer"
	      ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List"
	      ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat"
	      ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Option"
	      ";;; Elaborating spec at $SPECWARE/Library/ProverBase/String"
	      ";;; Elaborating spec at $SPECWARE/Library/ProverBase/System"
	      ";;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite")
	     (:optional
	      ";; ensure-directories-exist: creating $TESTDIR/Snark/MinusOb/MinusProof.log"
	      ";; Directory $TESTDIR/Snark/ does not exist, will create."
	      ";; Directory $TESTDIR/Snark/MinusOb/ does not exist, will create.")
	     (:optional "creating directory: $TESTDIR/Snark/")
	     (:optional "creating directory: $TESTDIR/Snark/MinusOb/")
	     (:optional 
	      ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
	     "    Expanded spec file: $TESTDIR/Snark/MinusOb/MinusProof.sw"
	     "    Snark Log file: $TESTDIR/Snark/MinusOb/MinusProof.log"
	     (:optional 
	      ";; ensure-directories-exist: creating $TESTDIR/Snark/MinusOb/MinusProof.log"
	      ";; Directory $TESTDIR/Snark/ does not exist, will create."
	      ";; Directory $TESTDIR/Snark/MinusOb/ does not exist, will create.")
	     "MinusProof: Conjecture minus_def2_Obligation_subsort in ONat is Proved! using Snark*."
	     (:optional "")
	     (:optional "")
	     (:optional "")
	     ))

  )
