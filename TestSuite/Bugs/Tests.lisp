(cl-user::sw-init)

(test-directories ".")

(test 

 ("Bug 0043 : Snark doesn't like Booleans"
  :show "Bug_0043/Change#ShouldBeProvable" 
  :output "??")

 ("Bug 0045 : Unambiguous op erroneously declared ambiguous [toString]" 
  :show   "Bug_0045/ToString"
  :output ";;; Elaborating spec at $TESTDIR/Bug_0045/ToString

spec
  op b : Nat -> String
  def b = toString
endspec
")


 ("Bug 0045 : Unambiguous op erroneously declared ambiguous [FlipFlop]"
  :show   "Bug_0045/Flop#FlipFlopImplementation" 
  :output ";;; Elaborating spec-morphism at $TESTDIR/Bug_0045/Flop#FlipFlopImplementation
;;; Elaborating spec at $TESTDIR/Bug_0045/Flop#Flipflop
;;; Elaborating spec at $TESTDIR/Bug_0045/Flop#FlipFlopImplementation

morphism
    spec  
 type Flip
 op flop : Flip -> Flip
endspec

    ->
    spec  
endspec

    {type Flip
     +->
     Boolean.Boolean,
     op flop
     +->
     ~}
")

 ("Bug 0053 : Strange result is shown for result of spec-substitution"
  :show   "Bug_0053/Subst#BB" 
  :output ";;; Elaborating spec-substitution at $TESTDIR/Bug_0053/Subst#BB
;;; Elaborating spec at $TESTDIR/Bug_0053/Subst#AA
;;; Elaborating spec at $TESTDIR/Bug_0053/Subst#A
;;; Elaborating spec-morphism at $TESTDIR/Bug_0053/Subst#M
;;; Elaborating spec at $TESTDIR/Bug_0053/Subst#B

spec  
 import B
 type Interval = {start:Nat, stop:Nat}
 def isEmptyInterval? {start = x, stop = y} = x = y
endspec

")

 ("Bug 0074 : Similarity of definitions often missed."
  :show   "Bug_0074/EquivalentSorts#XX" 
  :output ";;; Elaborating diagram-colimit at $TESTDIR/Bug_0074/EquivalentSorts#XX
;;; Elaborating diagram-term at $TESTDIR/Bug_0074/EquivalentSorts#DD
;;; Elaborating spec at $TESTDIR/Bug_0074/EquivalentSorts#AA
;;; Elaborating spec at $TESTDIR/Bug_0074/EquivalentSorts#BB
;;; Elaborating spec at $TESTDIR/Bug_0074/EquivalentSorts#Foo
;;; Elaborating spec at $TESTDIR/Bug_0074/EquivalentSorts#CC
;;; Elaborating spec-morphism at $TESTDIR/Bug_0074/EquivalentSorts#MM
;;; Elaborating spec-morphism at $TESTDIR/Bug_0074/EquivalentSorts#NN

spec  
 type {A, B, C}
 type {A, B, C} = List(Nat * Nat)
endspec

")

 ("Bug 0069 : Translate from base"
  :show   "Bug_0069/TranslateFromBase#M" 
  :output ";;; Elaborating spec-translation at $TESTDIR/Bug_0069/TranslateFromBase#M
;;; Elaborating spec at $TESTDIR/Bug_0069/TranslateFromBase#S
Errors in $TESTDIR/Bug_0069/TranslateFromBase.sw
3.21-3.37	: Error in translation: Illegal to translate from base type : Integer
")

 ("Bug 0069 : Translate into base"
  :show   "Bug_0069/TranslateIntoBase#M" 
  :output ;; Got:
";;; Elaborating spec-translation at $TESTDIR/Bug_0069/TranslateIntoBase#M
;;; Elaborating spec at $TESTDIR/Bug_0069/TranslateIntoBase#S
Errors in $TESTDIR/Bug_0069/TranslateIntoBase.sw
3.20-3.34	: Error in translation: Illegal to translate into base type or op: Char
")

 ("Bug 0069 : Morphism from base"
  :show   "Bug_0069/MorphismFromBase#M" 
  :output ";;; Elaborating spec-morphism at $TESTDIR/Bug_0069/MorphismFromBase#M
;;; Elaborating spec at $TESTDIR/Bug_0069/MorphismFromBase#S
;;; Elaborating spec at $TESTDIR/Bug_0069/MorphismFromBase#T
Errors in $TESTDIR/Bug_0069/MorphismFromBase.sw
5.21-5.36	: Error in morphism: Illegal to translate from base type: Integer
")

 ("Bug 0083 : Ambiguous op not detected"
  :show   "Bug_0083/Ambop#C" 
  :output ";;; Elaborating spec at $TESTDIR/Bug_0083/Ambop#C
;;; Elaborating spec at $TESTDIR/Bug_0083/Ambop#A
;;; Elaborating spec at $TESTDIR/Bug_0083/Ambop#B
Error in specification: 

Ambiguous ops: 
 (* Warning: Multiple definitions for following op *) 
 def f =
  (fn n ->
    (n + 1))
 def f =
  (fn n ->
    (n + 2))

 found in $TESTDIR/Bug_0083/Ambop.sw
3.4-3.43")

 ("Bug 0085 : Proof obligations for quotient pattern are not generated"
  :show   "Bug_0085/quotpat#O" 
  :output ";;; Elaborating obligator at $TESTDIR/Bug_0085/quotpat#O
;;; Elaborating spec at $TESTDIR/Bug_0085/quotpat#S
;;; Elaborating spec at $SPECWARE/Library/Base/WFO

spec  
 import S
 import /Library/Base/WFO
 conjecture f_Obligation is 
    fa(x : Q, y : Nat) x = quotient eq_mod10  y => natural?(y + 1)
 conjecture f_Unique is 
    fa(x : Q, y : Nat, z :Nat) x = quotient eq_mod10 y & x = quotient eq_mod10 z => (y + 1) = (z + 1)
 conjecture eq_mod10_Obligation is natural?(10) => true
 conjecture eq_mod10_Obligation0 is natural?(10) => true
 conjecture eq_mod10_reflexive is fa(x : Nat) eq_mod10(x, x)
 conjecture eq_mod10_symmetric is 
    fa(x : Nat, y : Nat) eq_mod10(x, y) => eq_mod10(y, x)
 conjecture eq_mod10_transitive is 
    fa(x : Nat, y : Nat, z : Nat) 
     eq_mod10(x, y) && eq_mod10(y, z) => eq_mod10(x, z)
endspec
")

 ("Bug 0093 : No check on clashing defs in colimit"
  :show   "Bug_0093/IncompatColimit.sw" 
  :output ";;; Elaborating spec at $TESTDIR/Bug_0093/IncompatColimit#I
;;; Elaborating spec at $TESTDIR/Bug_0093/IncompatColimit#I1
;;; Elaborating spec at $TESTDIR/Bug_0093/IncompatColimit#I2
;;; Elaborating diagram-colimit at $TESTDIR/Bug_0093/IncompatColimit#NN1N2
;;; Elaborating diagram-term at $TESTDIR/Bug_0093/IncompatColimit#NN1N2
;;; Elaborating spec-morphism at $TESTDIR/Bug_0093/IncompatColimit#NN1N2
;;; Elaborating spec-morphism at $TESTDIR/Bug_0093/IncompatColimit#NN1N2
Type error: 

Ambiguous ops:  op i : Nat
 (* Warning: Multiple definitions for following op *) 
 def i =
  2
 def i =
  1

 found in $TESTDIR/Bug_0093/IncompatColimit.sw
13.16-19.0")

 ("Bug 0102 : Extra variable in gnerated proof obligation"
  :show   "Bug_0102/ObligationsOfInteger.sw" 
  :output ";;; Elaborating obligator at $TESTDIR/Bug_0102/ObligationsOfInteger

spec  
 import /Library/Base/WFO
 conjecture Integer.abs_Obligation is fa(x : Integer) x >= 0 => natural? x
 conjecture Integer.abs_Obligation0 is 
    fa(x : Integer) ~(x >= 0) => natural?(Integer_.- x)
 conjecture Integer.addition_def2_Obligation is 
    fa(n1 : PosNat, n2 : PosNat) 
     n1 + n2 = plus(n1, n2) 
     && Integer_.- n1 + Integer_.- n2 = Integer_.-(plus(n1, n2)) 
        && ~(lte(n1, n2)) => lte(n2, n1)
 conjecture Integer.addition_def2_Obligation0 is 
    fa(n1 : PosNat, n2 : PosNat) 
     n1 + n2 = plus(n1, n2) 
     && Integer_.- n1 + Integer_.- n2 = Integer_.-(plus(n1, n2)) 
        && n1 + Integer_.- n2 
           = if lte(n1, n2)
              then Integer_.-(minus(n2, n1)) 
             else minus(n1, n2) && ~(lte(n1, n2)) => lte(n2, n1)
 conjecture Integer.division_def_Obligation is 
    fa(y : NonZeroInteger) natural?(abs y) => abs y ~= 0
 conjecture Integer.division_def_Obligation0 is 
    fa(x : Integer, y : NonZeroInteger) natural?(abs x div abs y)
endspec

")

 ("Bug 0105 A: The new-style type quantifications in claim definitions are ambiguous"
  :show   "Bug_0105/QuantifiedAxiom#A"
  :output ";;; Elaborating spec at $TESTDIR/Bug_0105/QuantifiedAxiom#A

spec  
 op f infixl 22 : [a] List(a) * a -> Integer
 def i = 123
 axiom A is [i] f 3 = 0
endspec

")

 ("Bug 0105 B: The new-style type quantifications in claim definitions are ambiguous"
  :show   "Bug_0105/QuantifiedAxiom#B"
  :output ";;; Elaborating spec at $TESTDIR/Bug_0105/QuantifiedAxiom#B
Errors in $TESTDIR/Bug_0105/QuantifiedAxiom.sw
13.18-13.18	: Could not match type constraint
                   3 of type Nat
          with expected type List(mtv%metafy%5) * mtv%metafy%5
")

 ("Bug 0105 C: The new-style type quantifications in claim definitions are ambiguous"
  :show   "Bug_0105/QuantifiedAxiom#C"
  :output ";;; Elaborating spec at $TESTDIR/Bug_0105/QuantifiedAxiom#C

spec  
 op f infixl 22 : [a] a -> Integer
 def i = 123
 axiom A is [i] f(3) = 0
endspec

")

 ;; end of tests
 )
