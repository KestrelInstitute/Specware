(test-directories ".")

(test 
 ("Bug 0103 : WFO obligation not generated"
  :sw  "NeedWFO"
  :output '(";;; Elaborating spec at $TESTDIR/NeedWFO#S"
	    ";;; Elaborating obligator at $TESTDIR/NeedWFO#O"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    ""
	    "spec  "
	    " import /Library/Base/WFO"
	    " "
	    " op  f : [a] {(l, i) : (List(a) * Nat) | i < length l} -> a"
	    " conjecture f_Obligation_fn_precond is [a] "
	    "    fa(D : {(l, i) : (List(a) * Nat) | i < length l}) embed?(Cons)(D.1)"
            " conjecture f_termination is ..."
	    " "
	    " def f (hd :: tl, i) = if i = 0 then hd else f(Cons(hd, tl), i)"
	    "endspec"
	    ""
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/NeedWFO/P.log")
	    (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	    (:optional ";; Directory $TESTDIR/Snark/NeedWFO/ does not exist, will create.")
	    ";;; Elaborating proof-term at $TESTDIR/NeedWFO#P"
	    "    Expanded spec file: $TESTDIR/Snark/NeedWFO/P.sw"
	    "    Snark Log file: $TESTDIR/Snark/NeedWFO/P.log"
	    "P: Conjecture f_Obligation_fn_precond in O is NOT proved using Snark*."
	    ""))
 )
