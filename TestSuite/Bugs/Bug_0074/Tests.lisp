(test-directories ".")

(test 

 ("Bug 0074 : Similarity of definitions often missed."
  :show   "EquivalentSorts#XX" 
  :output ";;; Elaborating diagram-colimit at $TESTDIR/EquivalentSorts#XX
;;; Elaborating diagram-term at $TESTDIR/EquivalentSorts#DD
;;; Elaborating spec at $TESTDIR/EquivalentSorts#AA
;;; Elaborating spec at $TESTDIR/EquivalentSorts#BB
;;; Elaborating spec at $TESTDIR/EquivalentSorts#Foo
;;; Elaborating spec at $TESTDIR/EquivalentSorts#CC
;;; Elaborating spec-morphism at $TESTDIR/EquivalentSorts#MM
;;; Elaborating spec-morphism at $TESTDIR/EquivalentSorts#NN

spec  
 type {A, B, C}
 type {A, B, C} = List(Nat * Nat)
endspec

")

 )
