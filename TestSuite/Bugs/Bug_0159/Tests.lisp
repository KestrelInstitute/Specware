(test-directories ".")

(test 

 ("Bug 0159 [a]: Substitution fails on imports of imports: wreaks havoc on Accord."
  :show  "subst_spec"
  :output '((:optional ";;; Elaborating spec-substitution at $TESTDIR/subst_spec#subst_spec")
	    (:optional ";;; Elaborating spec at $TESTDIR/subst_spec#C")
	    (:optional ";;; Elaborating spec at $TESTDIR/subst_spec#A2")
	    (:optional ";;; Elaborating spec at $TESTDIR/subst_spec#A")
	    (:optional ";;; Elaborating spec at $TESTDIR/subst_spec#S")
	    (:optional ";;; Elaborating spec at $TESTDIR/subst_spec#Z")
	    (:optional ";;; Elaborating spec-morphism at $TESTDIR/subst_spec#M")
	    (:optional ";;; Elaborating spec at $TESTDIR/subst_spec#B")
	    (:optional ";;; Elaborating spec at $TESTDIR/subst_spec#T")
	    ""
	    "spec  "
	    " import A2 [M]"
	    " type W"
	    " type Y"
	    " "
	    " op  bar : B -> B"
	    "endspec"
	    ""
	    ""))

 ("Bug 0159 [b]: Substitution fails on imports of imports: wreaks havoc on Accord."
  :showx  "subst_spec"
  :output '(
	    ""
	    "spec  "
	    " type A1"
	    " "
	    " op  foo : List(Nat) -> List(Boolean)"
	    " def foo nats = map((fn n -> if n = 0 then false else true)) nats"
	    " type B"
	    " "
	    " op  bar : B -> B"
	    " def bar nats = map((fn n -> if n = 0 then false else true)) nats"
	    " type Z"
	    " type A2"
	    " type W"
	    " type Y"
	    " "
	    " op  bar : B -> B"
	    "endspec"
	    ""
	    ""))

 )
