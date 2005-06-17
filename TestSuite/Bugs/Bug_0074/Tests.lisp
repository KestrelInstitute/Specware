(test-directories ".")

(test 

 ("Bug 0074 : Similarity of definitions often missed."
  :show   "EquivalentSorts#XX" 
  :output '(";;; Elaborating diagram-colimit at $TESTDIR/EquivalentSorts#XX"
	    ";;; Elaborating diagram-term at $TESTDIR/EquivalentSorts#DD"
	    ";;; Elaborating spec-morphism at $TESTDIR/EquivalentSorts#MM"
	    ";;; Elaborating spec at $TESTDIR/EquivalentSorts#AA"
	    ";;; Elaborating spec at $TESTDIR/EquivalentSorts#BB"
	    ";;; Elaborating spec at $TESTDIR/EquivalentSorts#Foo"
	    ";;; Elaborating spec-morphism at $TESTDIR/EquivalentSorts#NN"
	    ";;; Elaborating spec at $TESTDIR/EquivalentSorts#CC"
	    ""
	    "spec  "
	    (:alternatives
	     " type {A, B, C}"
	     " type {A, C, B}"
	     " type {B, A, C}"
	     " type {B, C, A}"
	     " type {C, A, B}"
	     " type {C, B, A}"
	     )
	    " import Foo"
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
	     " type {C, B, A} = Foo(Nat)"
	     )
	    "endspec"
	    ""
	    ""))

 )
