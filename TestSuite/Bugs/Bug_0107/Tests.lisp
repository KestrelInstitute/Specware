(test-directories ".")

(test 

 ("Bug 0107 : Bogus Nil prints as []"
  :show   "BogusNil"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil"
	    (:optional "")
	    "spec"
	    " type NotList(a) =  | Cons a * NotList(a) | Nil"
	    (:optional "")
	    " op  bogus_nil : NotList(Nat) = Nil"
	    (:optional "")
	    " op  bogus_cons : NotList(Nat) = Cons(4, Cons(5, Cons(6, bogus_nil)))"
	    (:optional "")
	    " op  true_nil : List(Nat) = []"
	    (:optional "")
	    " op  true_cons : List(Nat) = [1, 2, 3]"
	    "endspec"
	    (:optional "")
	    (:optional "")))

 )
