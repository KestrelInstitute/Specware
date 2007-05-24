(test-directories ".")

(test 
 ("Bug 0103 : WFO obligation not generated"
  :sw  "NeedWFO"
  :output '(";;; Elaborating spec at $TESTDIR/NeedWFO#S"
	    ";;; Elaborating obligator at $TESTDIR/NeedWFO#O"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    (:optional "")
	    "spec  "
	    (:optional " import /Library/Base/WFO")
	    " "
	    " op  f : [a] {(l, i) : (List(a) * Nat) | i < length l} -> a"
	    " conjecture f_Obligation_exhaustive is [a] "
	    "    fa(D : {(l, i) : (List(a) * Nat) | i < length l}) embed?(Cons)(D.1)"
	    " "
	    " def f (hd :: tl, i) = if i = 0 then hd else f(Cons(hd, tl), i)"
	    "endspec"
	    (:optional "")
	    (:optional "")
	    ";;; Elaborating proof-term at $TESTDIR/NeedWFO#P"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Option")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/String")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/System")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite")
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/NeedWFO/P.log")
	    (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	    (:optional ";; Directory $TESTDIR/Snark/NeedWFO/ does not exist, will create.")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
	    (:optional "creating directory: $TESTDIR/Snark/")
	    (:optional "creating directory: $TESTDIR/Snark/NeedWFO/")
	    "    Expanded spec file: $TESTDIR/Snark/NeedWFO/P.sw"
	    "    Snark Log file: $TESTDIR/Snark/NeedWFO/P.log"
	    "P: Conjecture f_Obligation_exhaustive in O is *"
	    (:optional "")
	    (:optional "")
	    ))
 )
