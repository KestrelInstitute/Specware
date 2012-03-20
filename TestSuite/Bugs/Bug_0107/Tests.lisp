(test-directories ".")

(test 

 ("Bug 0107 : Bogus Nil prints as []"
  :show   "BogusNil"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil"
	    (:optional "")
	    "spec"
	    (:optional "")
	    "type NotList(a) = | Cons a * NotList(a) | Nil"
	    (:optional "")
	    "op bogus_nil: NotList(Nat) = Nil"
	    (:optional "")
            "op bogus_cons: NotList(Nat) = 4 :: 5 :: 6 :: bogus_nil"
	    (:optional "")
	    "op true_nil: List(Nat) = []"
	    (:optional "")
	    "op true_cons: List(Nat) = [1, 2, 3]"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))

 )
