(test-directories ".")

(test 

 ("Bug 0105 A: The new-style type quantifications in claim definitions are ambiguous"
  :show   "QuantifiedAxiom#A"
  :output ";;; Elaborating spec at $TESTDIR/QuantifiedAxiom#A

spec  
 
 op  i : Nat
 def i = 123
 
 op  f infixl 22 : [a] List(a) * a -> Integer
 axiom A is [i] f 3 = 0
endspec

")

 ("Bug 0105 B: The new-style type quantifications in claim definitions are ambiguous"
  :show   "QuantifiedAxiom#B"
  :output ";;; Elaborating spec at $TESTDIR/QuantifiedAxiom#B
Errors in $TESTDIR/QuantifiedAxiom.sw
13.18-13.18	: Could not match type constraint
                   3 of type Nat
          with expected type List(mtv%metafy%5) * mtv%metafy%5
")

 ("Bug 0105 C: The new-style type quantifications in claim definitions are ambiguous"
  :show   "QuantifiedAxiom#C"
  :output ";;; Elaborating spec at $TESTDIR/QuantifiedAxiom#C

spec  
 
 op  i : Nat
 def i = 123
 
 op  f infixl 22 : [a] a -> Integer
 axiom A is [i] f(3) = 0
endspec

")

 )
