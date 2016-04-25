(test-directories ".")

(test 

 ("Bug 0160 : Merging of disparate types should not be allowed"
  :sw "subst_spec"
  :output '(
	    ";;; Elaborating spec-substitution at $TESTDIR/subst_spec#subst_spec"
	    ";;; Elaborating spec at $TESTDIR/subst_spec#C"
	    ";;; Elaborating spec at $TESTDIR/subst_spec#A"
	    ";;; Elaborating spec-morphism at $TESTDIR/subst_spec#M"
	    ";;; Elaborating spec at $TESTDIR/subst_spec#B"
	    "ERROR: in specification: "
	    ""
	    "Ambiguous ops:"
	    ""
	    " (* Warning: Multiple declarations for following op *) "
	    " op  foo: (List Nat -> List Bool)"
	    " op  foo: (B -> B)"
	    " def foo ="
	    "  (fn nats ->"
	    "    ((map (fn n ->"
	    "      if (n = 0) then"
	    "        false"
	    "      else"
	    "        true)) nats))"
	    ""
	    " found in $TESTDIR/subst_spec.sw"
	    "*.13-*.16"
	    ))

 )
