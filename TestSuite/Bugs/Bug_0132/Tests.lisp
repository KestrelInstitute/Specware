(test-directories ".")

(test 

 ("Bug 0132 : No proof obligation generated for 'the'"
  :show "theOblig#O"
  :output '(";;; Elaborating obligator at $TESTDIR/theOblig#O"
	    ";;; Elaborating spec at $TESTDIR/theOblig#S"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    ""
	    "spec  "
	    (:optional " import /Library/Base/WFO")
            ""
	    " type Predicate(a) = a -> Bool"
	    " "
	    " op  uniquelySatisfies? : [a] a * Predicate(a) -> Bool"
            ""
	    " axiom uniquelySatisfies?_def is [a] "
	    "    fa(x : a, p : Predicate(a)) "
	    "     uniquelySatisfies?(x, p) = (p x && (fa(y : a) (p y => y = x)))"
	    " "
	    " op  uniquelySatisfied? : [a] Predicate(a) -> Bool"
            ""
	    " axiom uniquelySatisfied?_def is [a] "
	    "    fa(p : Predicate(a)) "
	    "     uniquelySatisfied? p = (ex(x : a) uniquelySatisfies?(x, p))"
	    " "
	    " type UniquelySatisfiedPredicate(a) = (Predicate(a) | uniquelySatisfied?)"
	    " "
	    " op  The : [a] UniquelySatisfiedPredicate(a) -> a"
            ""
	    " axiom The_def is [a] "
	    "    fa(p : UniquelySatisfiedPredicate(a)) uniquelySatisfies?(The p, p)"
	    " "
	    " op  f : Nat -> Nat"
            ""
	    " conjecture f_Obligation_subtype is "
            (:alternatives
             "    fa(n : Nat) uniquelySatisfied?((fn m -> m = n))"
             "    fa(n : Nat) uniquelySatisfied?((fn m : Nat -> m = n))")
	    " "
            (:alternatives 
             " def f n = The((fn m -> m = n))"
             " def f n = The((fn m : Nat -> m = n))")
            "endspec"
	    ""
	    ""))
)

