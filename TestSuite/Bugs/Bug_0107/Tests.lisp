(test-directories ".")

(test 

 ("Bug 0107 : Bogus Nil prints as []"
  :show   "BogusNil"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil"
	    ""
	    "spec  "
	    " type NotList(a) =  | Cons a * NotList(a) | Nil"
	    " "
	    " op  bogus_nil : NotList(Nat)"
	    " def bogus_nil = Nil"
	    " "
	    " op  true_nil : List(Nat)"
	    " def true_nil = []"
	    " "
	    " op  true_cons : List(Nat)"
	    " def true_cons = [1, 2, 3]"
	    " "
	    " op  bogus_cons : NotList(Nat)"
	    " def bogus_cons = Cons(4, Cons(5, Cons(6, bogus_nil)))"
	    "endspec"
	    ""
	    ""))

 )
