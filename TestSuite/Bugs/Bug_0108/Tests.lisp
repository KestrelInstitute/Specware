(test-directories ".")

(test 

 ("Bug 0108 : Printing of diagram is atrocious"
  :show   "Diagram#D"
  :output ";;; Elaborating diagram-term at $TESTDIR/Diagram#D
;;; Elaborating spec-morphism at $TESTDIR/Diagram#M
;;; Elaborating spec at $TESTDIR/Diagram#R
;;; Elaborating spec at $TESTDIR/Diagram#S
;;; Elaborating spec-morphism at $TESTDIR/Diagram#N
;;; Elaborating spec at $TESTDIR/Diagram#T

diagram {a : x -> y
         +->
         morphism R -> S 
          {type A1 +-> B1,
           type A2 +-> B2,
           type A3 +-> B3,
           op f +-> g},
         b : x -> z
         +->
         morphism R -> T 
          {type A1 +-> C1,
           type A2 +-> C2,
           type A3 +-> C3,
           op f +-> h}}
")

 )
