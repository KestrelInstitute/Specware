(test-directories ".")

(test 

 ("Bug 0140 : Merging of disparate sorts should not be allowed"
  :sw "subst_spec"
  :output '(
	    ";;; Elaborating spec-substitution at $TESTDIR/Bug_0160/subst_spec#subst_spec"
	    ";;; Elaborating spec at $TESTDIR/subst_spec#C"
	    ";;; Elaborating spec at $TESTDIR/subst_spec#A"
	    ";;; Elaborating spec-morphism at $TESTDIR/subst_spec#M"
	    ";;; Elaborating spec at $TESTDIR/subst_spec#B"
	    "Error in specification: Merged versions of Op foo have different sorts:"
	    " B -> B"
	    " List(Nat) -> List(Boolean)"
	    ""
	    " found in no position"
	    ""))
 )