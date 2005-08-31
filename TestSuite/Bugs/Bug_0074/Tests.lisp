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
	    ;; :optional  :alternatives doesn't work yet, 
	    ;;  so this is the clumsy workaround:
	    (:alternatives 
	     (" type {A, B, C}" " import Foo")
	     (" type {A, C, B}" " import Foo")
	     (" type {B, A, C}" " import Foo")
	     (" type {B, C, A}" " import Foo")
	     (" type {C, A, B}" " import Foo")
	     (" type {C, B, A}" " import Foo")
	     (" import Foo"))
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
