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
	    (:optional " import /Library/Base/WFO")
	    " import Integer"
	    " "
	    " op  natural? (i : Integer) : Boolean = i >= zero"
	    " type Nat = (Integer | natural?)"
	    " "
	    " op  posNat? (n : Nat) : Boolean = n > zero"
	    " type PosNat = (Nat | posNat?)"
	    " "
	    " op  succ : Nat -> Nat"
	    " conjecture Nat.succ_Obligation_subsort is fa(n : Nat) natural?(succ n)"
	    " "
	    " def succ n = succ n"
	    " proof Isa Thy_Morphism"
	    "   type Nat.Nat -> nat (int,nat) [+,*,div,rem,<=,<,>=,>,abs,min,max]"
	    "   Nat.succ     -> Suc"
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
