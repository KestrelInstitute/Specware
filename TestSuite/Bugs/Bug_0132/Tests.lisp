(test-directories ".")

(test 

 ("Bug 0132 : No proof obligation generated for 'the'"
  :show "theOblig#O"
  :output '(";;; Elaborating obligator at $TESTDIR/theOblig#O"
	    ";;; Elaborating spec at $TESTDIR/theOblig#S"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    (:optional "")
	    "spec"
	    (:optional "")
	    (:optional " import /Library/Base/WFO")
	    (:optional "")
	    " type Predicate(a) = a -> Bool"
	    (:optional "")
	    " op [a] uniquelySatisfies?: a * Predicate(a) -> Bool"
	    (:optional "")
	    " axiom uniquelySatisfies?_def is [a] "
	    "    fa(x: a, p: Predicate(a)) "
	    "     uniquelySatisfies?(x, p) = (p x && (fa(y: a) (p y => y = x)))"
	    (:optional "")
	    " op [a] uniquelySatisfied?: Predicate(a) -> Bool"
	    (:optional "")
	    " axiom uniquelySatisfied?_def is [a] "
	    "    fa(p: Predicate(a)) uniquelySatisfied? p = (ex(x: a) uniquelySatisfies?(x, p))"
	    (:optional "")
	    " type UniquelySatisfiedPredicate(a) = (Predicate(a) | uniquelySatisfied?)"
	    (:optional "")
	    " op  [a] The: UniquelySatisfiedPredicate(a) -> a"
	    (:optional "")
	    " axiom The_def is [a] fa(p: UniquelySatisfiedPredicate(a)) uniquelySatisfies?(The p, p)"
	    (:optional "")
	    " op  f: Nat -> Nat"
	    (:optional "")
	    " conjecture f_Obligation_subtype is fa(n: Nat) uniquelySatisfied?(fn (m: Nat) -> m = n)"
	    (:optional "")
            (:alternatives 
             " def f n = The((fn m -> m = n))"
             " def f n = The((fn m: Nat -> m = n))"
             " def f(n: Nat): Nat = The(fn (m: Nat) -> m = n)")
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))
)

