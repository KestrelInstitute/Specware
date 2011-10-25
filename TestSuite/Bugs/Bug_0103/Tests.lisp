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
	    (:optional "")
            (:alternatives
             " op f : [a] {(l, i) : (List(a) * Nat) | i < length l} -> a"
             " op f : [a] {l, i : (List(a) * Nat) | i < length l} -> a")
	    (:optional "")
	    " conjecture f_Obligation_exhaustive is [a] "
            (:alternatives
             "    fa(D : {(l, i) : (List(a) * Nat) | i < length l}) embed?(Cons)(D.1)"
             ("    fa(D : {l, i : (List(a) * Nat) | i < length l}) "
              "    ex(hd : a, tl : List(a), i : Nat) D = (Cons(hd, tl), i)"))
	    (:optional "")
            " conjecture f_Obligation_uniqueness is [a] "
            (:alternatives
             "    ex1(f : {(l, i) : (List(a) * Nat) | i < length l} -> a) "
             "    ex1(f : {l, i : (List(a) * Nat) | i < length l} -> a) ")
            (:alternatives
             "    fa(tl : List(a), hd : a, i : Nat) "
             "    fa(hd : a, tl : List(a), i : Nat) ")
            "      f (Cons(hd, tl), i) = (if i = 0 then hd else f (Cons(hd, tl), i))"
	    (:optional "")
            (:alternatives
             " def f (hd :: tl, i) = if i = 0 then hd else f(Cons(hd, tl), i)"
             (" def f "
              "     (hd : a :: tl : List(a), i : Nat"
              "        | fn (l : List(a), i : Nat) -> i < length l) : a"
              "   = if i = 0 then hd else f(Cons(hd, tl), i)"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ";;; Elaborating proof-term at $TESTDIR/NeedWFO#P"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List")
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
            "P: Conjecture f_Obligation_exhaustive in O is proved using Snark in * seconds."
	    (:optional "")
	    (:optional "")
	    ))
 )
