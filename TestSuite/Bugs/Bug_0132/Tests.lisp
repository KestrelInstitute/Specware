(test-directories ".")

(test 

 ("Bug 0132 : No proof obligation generated for 'the'"
  :show "theOblig#O"
  :output '(";;; Elaborating obligator at $TESTDIR/theOblig#O"
	    ";;; Elaborating spec at $TESTDIR/theOblig#S"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    ""
	    "spec  "
	    " import /Library/Base/WFO"
	    " type Predicate(a) = a -> Boolean"
	    " "
	    " op  uniquelySatisfies? : [a] a * Predicate(a) -> Boolean"
	    " axiom uniquelySatisfies?_def is [a] "
	    "    fa(x : a, p : Predicate(a)) "
	    "     uniquelySatisfies?(x, p) = (p x && (fa(y : a) (p y => y = x)))"
	    " "
	    " op  uniquelySatisfied? : [a] Predicate(a) -> Boolean"
	    " axiom uniquelySatisfied?_def is [a] "
	    "    fa(p : Predicate(a)) "
	    "     uniquelySatisfied? p = (ex(x : a) uniquelySatisfies?(x, p))"
	    " type UniquelySatisfiedPredicate(a) = (Predicate(a) | uniquelySatisfied?)"
	    " "
	    " op  The : [a] UniquelySatisfiedPredicate(a) -> a"
	    " axiom The_def is [a] "
	    "    fa(p : UniquelySatisfiedPredicate(a)) uniquelySatisfies?(The p, p)"
	    " "
	    " op  f : Nat -> Nat"
	    " conjecture f_Obligation_subsort is "
	    "    fa(n : Nat) uniquelySatisfied?((fn m -> m = n))"
	    " "
	    " def f n = The((fn m -> m = n))"
            "endspec"
	    ""
	    ""))

 )