(test-directories ".")

(test 

 ("Bug 0159 [s] : Substitution fails on imports of imports: wreaks havoc on Accord."
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
	    (:optional "")
	    "spec"
	    " import A2 [M]"
	    (:optional "")
	    " type W"
	    (:optional "")
	    " type Y"
	    (:optional "")
	    " op  bar : B -> B"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))

 ("Bug 0159 [sx]: Substitution fails on imports of imports: wreaks havoc on Accord."
  :showx  "subst_spec"
  :output '((:optional "")
	    "spec"
	    (:optional "")
	    " type A1"
	    (:optional "")
	    " op  foo : List(Nat) -> List(Bool)"
            (:alternatives
             " def foo nats = map((fn n -> if n = 0 then false else true)) nats"
             (" def foo nats = "
              "  map((fn n : Nat -> if n = 0 then false else true)) nats")
             (" def foo (nats : List(Nat)) : List(Bool)"
              "  = map(fn (n : Nat) -> if n = 0 then false else true) nats"))
	    (:optional "")
	    " type B"
	    (:optional "")
	    " op  baz : List(Nat) -> List(Bool)"
            (:alternatives
             " def baz nats = map((fn n -> if n = 0 then false else true)) nats"
             (" def baz nats = "
              "   map((fn n : Nat -> if n = 0 then false else true)) nats")
             (" def baz (nats : List(Nat)) : List(Bool)"
              "   = map(fn (n : Nat) -> if n = 0 then false else true) nats"))
	    (:optional "")
	    " type Z"
	    (:optional "")
	    " type A2"
	    (:optional "")
	    " type W"
	    (:optional "")
	    " type Y"
	    (:optional "")
	    " op  bar : B -> B"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))

 ("Bug 0159 [t] : Substitution fails on imports of imports: wreaks havoc on Accord."
  :show  "trans_spec"
  :output '((:optional ";;; Elaborating spec-translation at $TESTDIR/trans_spec#trans_spec")
	    (:optional ";;; Elaborating spec at $TESTDIR/trans_spec#E")
	    (:optional ";;; Elaborating spec at $TESTDIR/trans_spec#A")
	    (:optional ";;; Elaborating spec at $TESTDIR/trans_spec#B")
	    (:optional ";;; Elaborating spec at $TESTDIR/trans_spec#S")
	    (:optional ";;; Elaborating spec at $TESTDIR/trans_spec#C")
            (:optional ";;; Elaborating spec-translation at $TESTDIR/trans_spec#trans_spec")
	    (:optional "")
	    "spec"
	    " import translate A by {A +-> A2}"
	    (:optional "")
	    " type X"
	    (:optional "")
	    " type Y"
	    (:optional "")
	    " op  bar : A2 -> A2"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))

 ("Bug 0159 [tx]: Substitution fails on imports of imports: wreaks havoc on Accord."
  :showx  "trans_spec"
  :output '((:optional "")
	    "spec"
	    (:optional "")
	    " type A2"
	    (:optional "")
	    " op  foo : List(Nat) -> List(Bool)"
            (:alternatives
             " def foo nats = map((fn n -> if n = 0 then false else true)) nats"
             (" def foo nats = "
              "   map((fn n : Nat -> if n = 0 then false else true)) nats")
             (" def foo (nats : List(Nat)) : List(Bool)"
              "   = map(fn (n : Nat) -> if n = 0 then false else true) nats"))
	    (:optional "")
	    " type B"
	    (:optional "")
	    " type C"
	    (:optional "")
	    " type D"
	    (:optional "")
	    " type X"
	    (:optional "")
	    " type Y"
	    (:optional "")
	    " op  bar : A2 -> A2"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))

 ("Bug 0159 [q] : Substitution fails on imports of imports: wreaks havoc on Accord."
  :show  "qualify_spec"
  :output '((:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#qualify_spec")
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#E")
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#A")
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#B")
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#S")
	    (:optional ";;; Elaborating spec at $TESTDIR/qualify_spec#C")
	    (:optional "")
	    "spec"
	    (:optional "")
	    " import Q qualifying A"
	    (:optional "")
	    " type Q.X"
	    (:optional "")
	    " type Q.Y"
	    (:optional "")
	    " op  Q.bar : Q.A -> Q.A"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))

 ("Bug 0159 [qx]: Substitution fails on imports of imports: wreaks havoc on Accord."
  :showx  "qualify_spec"
  :output '((:optional "")
	    "spec"
	    (:optional "")
	    " type Q.A"
	    (:optional "")
	    " op  Q.foo : List(Nat) -> List(Bool)"
	    (:optional "")
            (:alternatives
             " def Q.foo nats = map((fn n -> if n = 0 then false else true)) nats"
             (" def Q.foo nats = "
              "  map((fn n : Nat -> if n = 0 then false else true)) nats")
             ("def Q.foo (nats : List(Nat)) : List(Bool)"
              "  = map(fn (n : Nat) -> if n = 0 then false else true) nats"))
	    (:optional "")
	    " type Q.B"
	    (:optional "")
	    " type Q.C"
	    (:optional "")
	    " type Q.D"
	    (:optional "")
	    " type Q.X"
	    (:optional "")
	    " type Q.Y"
	    (:optional "")
	    " op  Q.bar : Q.A -> Q.A"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))
 )
