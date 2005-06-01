(test-directories ".")

(test 

 ("Bug 0159 [s1]: Substitution fails on imports of imports: wreaks havoc on Accord."
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

 ("Bug 0159 [s2]: Substitution fails on imports of imports: wreaks havoc on Accord."
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

 ("Bug 0159 [t1]: Substitution fails on imports of imports: wreaks havoc on Accord."
  :show  "trans_spec"
  :output '(
	    (:optional ";;; Elaborating spec-translation at $TESTDIR/trans_spec#trans_spec")
	    (:optional ";;; Elaborating spec at $TESTDIR/trans_spec#E")
	    (:optional ";;; Elaborating spec at $TESTDIR/trans_spec#A")
	    (:optional ";;; Elaborating spec at $TESTDIR/trans_spec#B")
	    (:optional ";;; Elaborating spec at $TESTDIR/trans_spec#S")
	    (:optional ";;; Elaborating spec at $TESTDIR/trans_spec#C")
	    ""
	    "spec  "
	    " import translate (A) by {A +-> A2}"
	    " type X"
	    " type Y"
	    " "
	    " op  bar : A2 -> A2"
	    "endspec"
	    ""
	    ""))

 ("Bug 0159 [t2]: Substitution fails on imports of imports: wreaks havoc on Accord."
  :showx  "trans_spec"
  :output '(
	    ""
	    "spec  "
	    " type A2"
	    " "
	    " op  foo : List(Nat) -> List(Boolean)"
	    " def foo nats = map((fn n -> if n = 0 then false else true)) nats"
	    " type B"
	    " type C"
	    " type D"
	    " type X"
	    " type Y"
	    " "
	    " op  bar : A2 -> A2"
	    "endspec"
	    ""
	    ""))

 ("Bug 0159 [q1]: Substitution fails on imports of imports: wreaks havoc on Accord."
  :show  "qualify_spec"
  :output '(
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#qualify_spec")
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#E")
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#A")
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#B")
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#S")
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#C")
	    ""
	    "spec  "
	    " import Q qualifying A"
	    " type Q.X"
	    " type Q.Y"
	    " "
	    " op  Q.bar : Q.A -> Q.A"
	    "endspec"
	    ""
	    ""))

 ("Bug 0159 [q2]: Substitution fails on imports of imports: wreaks havoc on Accord."
  :showx  "qualify_spec"
  :output '(
	    ""
	    "spec  "
	    " type Q.A"
	    " "
	    " op  Q.foo : List(Nat) -> List(Boolean)"
	    " def Q.foo nats = map((fn n -> if n = 0 then false else true)) nats"
	    " type Q.B"
	    " type Q.C"
	    " type Q.D"
	    " type Q.X"
	    " type Q.Y"
	    " "
	    " op  Q.bar : Q.A -> Q.A"
	    "endspec"
	    ""
	    ""))

 )
