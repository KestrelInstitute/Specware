(test-directories ".")

(test 

 ("Bug 0107 : Bogus Nil prints as []"
  :show   "BogusNil"
  :output '(";;; Elaborating spec at $TESTDIR/BogusNil"
	    ""
	    "spec  "
	    " type NotList(a) =  | Cons a * NotList(a) | Nil"
	    " "
	    " def bogus_nil = Nil"
	    " "
	    " def bogus_cons = Cons(4, Cons(5, Cons(6, bogus_nil)))"
	    " "
	    " def true_nil = []"
	    " "
	    " def true_cons = [1, 2, 3]"
	    "endspec"
	    ""
	    ""))

 )
