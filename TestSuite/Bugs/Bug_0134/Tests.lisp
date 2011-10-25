(test-directories ".")

(test 

 ("Bug 0134 : Unparseable proof obligation generated"
  :show "fold#O"
  :output '(";;; Elaborating obligator at $TESTDIR/fold#O"
	    ";;; Elaborating spec at $TESTDIR/fold#S"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
            (:optional "")
            "spec"
            (:optional "")
	    (:optional " import /Library/Base/WFO")
            (:optional "")
	    " type Predicate(a) = a -> Bool"
            (:optional "")
	    " op uniquelySatisfies? : [a] a * Predicate(a) -> Bool"
            (:optional "")
	    " axiom uniquelySatisfies?_def is [a] "
	    "    fa(x : a, p : Predicate(a)) "
	    "     uniquelySatisfies?(x, p) = (p x && (fa(y : a) (p y => y = x)))"
            (:optional "")
	    " op uniquelySatisfied? : [a] Predicate(a) -> Bool"
            (:optional "")
	    " axiom uniquelySatisfied?_def is [a] "
	    "    fa(p : Predicate(a)) "
	    "     uniquelySatisfied? p = (ex(x : a) uniquelySatisfies?(x, p))"
            (:optional "")
	    " type UniquelySatisfiedPredicate(a) = (Predicate(a) | uniquelySatisfied?)"
            (:optional "")
	    " op The : [a] UniquelySatisfiedPredicate(a) -> a"
            (:optional "")
	    " axiom The_def is [a] "
	    "    fa(p : UniquelySatisfiedPredicate(a)) uniquelySatisfies?(The p, p)"
            (:optional "")
	    " type FSet(a)"
            (:optional "")
	    " op in? infixl 20 : [a] a * FSet(a) -> Bool"
            (:optional "")
	    " op empty : [a] FSet(a)"
            (:optional "")
	    " op with infixl 30 : [a] FSet(a) * a -> FSet(a)"
            (:optional "")
	    " op wout infixl 30 : [a] FSet(a) * a -> FSet(a)"
            (:optional "")
	    " op foldable? : [a, b] FSet(a) * b * (b * a -> b) -> Bool"
            (:optional "")
            (:alternatives
             (" def foldable? (s, c, f) = "
              "   fa(x : a, y : a, z : b) ")
             ("def foldable? (s : FSet(a), c : b, f : b * a -> b) : Bool"
              "  = fa(x : a, y : a, z : b) "))
            "    x in? s && y in? s => f (f (z, x), y) = f (f (z, y), x)"
            (:optional "")
	    " op fold : [a, b] ((FSet(a) * b * (b * a -> b)) | foldable?) -> b"
            (:optional "")
	    " conjecture fold_Obligation_subtype1 is [a, b] "
            (:alternatives
             ("   fa(fold : ((FSet(a) * b * (b * a -> b)) | foldable?) -> b, s : FSet(a), "
              "      x : a, c_1 : b, f_1 : b * a -> b) "
              "    (fa(c : b, f : b * a -> b) fold (empty, c, f) = c) "
              "    && foldable?(s with x, c_1, f_1) => foldable?(s wout x, c_1, f_1)")
             ("   fa(f_1 : b * a -> b, c_1 : b, s : FSet(a), x : a) "
              "    foldable?(s with x, c_1, f_1) => foldable?(s wout x, c_1, f_1)"))
            (:optional "")
	    " conjecture fold_Obligation_subtype0 is [a, b] "
	    "    fa(c : b, f : b * a -> b) foldable?(empty, c, f)"
            (:optional "")
	    " conjecture fold_Obligation_subtype is [a, b] "
	    "    uniquelySatisfied?"
            (:alternatives
             ("      ((fn fold -> "
              "           (fa(c : b, f : b * a -> b) fold (empty, c, f) = c) "
              "           && (fa(s : FSet(a), x : a, c_1 : b, f_1 : b * a -> b) "
              "                (foldable?(s with x, c_1, f_1) "
              "                => fold (s with x, c_1, f_1) "
              "                   = f_1(fold (s wout x, c_1, f_1), x)))))")
             ("     (fn (fold : ((FSet(a) * b * (b * a -> b)) | foldable?) -> b) -> "
              "        (fa(c : b, f : b * a -> b) fold (empty, c, f) = c) "
              "         && (fa(s : FSet(a), x : a, c_1 : b, f_1 : b * a -> b) "
              "              (foldable?(s with x, c_1, f_1) "
              "               => fold (s with x, c_1, f_1) "
              "                   = f_1 (fold (s wout x, c_1, f_1), x)))) "))
            (:optional "")
            " def fold : ((FSet(a) * b * (b * a -> b)) | foldable?) -> b"
            "   = The"
            "       (fn (fold : ((FSet(a) * b * (b * a -> b)) | foldable?) -> b) -> "
            "           (fa(c : b, f : b * a -> b) fold (empty, c, f) = c) "
            "            && (fa(s : FSet(a), x : a, c : b, f : b * a -> b) "
            "                 (foldable?(s with x, c, f) "
            "                  => fold (s with x, c, f) = f (fold (s wout x, c, f), x))))"
            (:optional "")
            (:alternatives "endspec" "end-spec")
            (:optional "")
            (:optional "")
	    ))
 )

