(test-directories ".")

(test 

 ("Bug 0074 : Similarity of definitions often missed."
  :show   "EquivalentTypes#XX" 
  :output '(";;; Elaborating diagram-colimit at $TESTDIR/EquivalentTypes#XX"
	    ";;; Elaborating diagram-term at $TESTDIR/EquivalentTypes#DD"
	    ";;; Elaborating spec-morphism at $TESTDIR/EquivalentTypes#MM"
	    ";;; Elaborating spec at $TESTDIR/EquivalentTypes#AA"
	    ";;; Elaborating spec at $TESTDIR/EquivalentTypes#BB"
	    ";;; Elaborating spec at $TESTDIR/EquivalentTypes#Foo"
	    ";;; Elaborating spec-morphism at $TESTDIR/EquivalentTypes#NN"
	    ";;; Elaborating spec at $TESTDIR/EquivalentTypes#CC"
            (:optional "")
            (:optional "")
	    "spec"
            (:optional "")
            (:optional "")
            (:alternatives 
             "import Foo"
             "type Foo(x) = List(x * x)")
            (:optional "")
            (:optional " type {A, B, C}")
            (:optional " type {A, C, B}")
            (:optional " type {B, A, C}")
            (:optional " type {B, C, A}")
            (:optional " type {C, A, B}")
            (:optional " type {C, B, A}")
            (:optional "")
	    (:alternatives 
             " type {A, B, C} = List(Nat * Nat)"
             " type {A, B, C} = Foo(Nat)"
             " type {A, C, B} = List(Nat * Nat)"
             " type {A, C, B} = Foo(Nat)"
             " type {B, A, C} = List(Nat * Nat)"
             " type {B, A, C} = Foo(Nat)"
             " type {B, C, A} = List(Nat * Nat)"
             " type {B, C, A} = Foo(Nat)"
             " type {C, A, B} = List(Nat * Nat)"
             " type {C, A, B} = Foo(Nat)"
             " type {C, B, A} = List(Nat * Nat)"
             " type {C, B, A} = Foo(Nat)")
            (:optional "")
	    (:alternatives "endspec" "end-spec")
            (:optional "")
            (:optional "")
            ))
 )
