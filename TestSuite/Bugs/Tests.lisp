(cl-user::sw-init)

(test-directories ".")

(test 

 ("Bug 0003 : Some inconsistencies with using :sw command and with the # notation"
  :sw "Bug_0003/ABC"
  :output ";;; Elaborating spec at $TESTDIR/Bug_0003/ABC#A
;;; Elaborating spec at $TESTDIR/Bug_0003/ABC#B
;;; Elaborating spec at $TESTDIR/Bug_0003/ABC#C
")

 ("Bug_0011 : Consider abbreviating printed path names."
  :show "Bug_0011/abc"
  :output ";;; Elaborating spec at $TESTDIR/Bug_0011/abc
;;; Elaborating spec at $TESTDIR/Bug_0011/xyz

spec  
 import xyz
endspec

")

 ("Bug 0012 : The tutorial does not work anymore."
  :sw "/UserDoc/tutorial/example/MatchingRefinements"
  :output ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#Symbols
;;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#Symbols_Ref
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Symbols
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching0
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Words
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Messages
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#SymbolMatching
;;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching_Ref0
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#WordMatching
;;; Elaborating spec-substitution at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching
;;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching_Ref
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches0
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Matches
;;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref0
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#FindMatches
;;; Elaborating spec-substitution at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches
;;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref
")
 
 ("Bug 0015 : Substitute and Translate fail to update the localSorts and localOps"
  :show "Bug_0015/subsExample#BB"
  :output ";;; Elaborating spec-substitution at $TESTDIR/Bug_0015/subsExample#BB
;;; Elaborating spec at $TESTDIR/Bug_0015/subsExample#AA
;;; Elaborating spec at $TESTDIR/Bug_0015/subsExample#A
;;; Elaborating spec-morphism at $TESTDIR/Bug_0015/subsExample#M
;;; Elaborating spec at $TESTDIR/Bug_0015/subsExample#B

spec  
 import B
 type Interval = {start:Integer, stop:Integer}
 op isEmptyInterval? : Interval -> Boolean
 def isEmptyInterval? {start = x, stop = y} = x = y
endspec

")

 ("Bug 0016 : An incorrect SWPATH produces no error or warning"
  :path "/loser/loser/loser"
  :output "Warning: Directory does not exist: /loser/loser/loser
Keeping old path:
$SPECWARE:.:$SPECWARE/")

 ("Bug 0017 : Incorrect colimit computed"
  :show "Bug_0017/AAcol#C"
  :output ";;; Elaborating diagram-colimit at $TESTDIR/Bug_0017/AAcol#C
;;; Elaborating diagram-term at $TESTDIR/Bug_0017/AAcol#D
;;; Elaborating spec at $TESTDIR/Bug_0017/AAcol#A

spec  
 def Y.fubaz = 12345
 def X.fubaz = 12345
endspec

")

 ("Bug 0018 : Cannot generate code from colimit"
  :sw "Bug_0018/BBcol#K"
  :output ";;; Elaborating diagram-colimit at $TESTDIR/Bug_0018/BBcol#K
;;; Elaborating diagram-term at $TESTDIR/Bug_0018/BBcol#K
;;; Elaborating spec at $TESTDIR/Bug_0018/BBcol#A
;;; Generating lisp file $TESTDIR/Bug_0018/lisp/BBcol.lisp
")

 ("Bug 0043 : Snark doesn't like Booleans"
  :show "Bug_0043/Change#ShouldBeProvable" 
  :output ";;; Elaborating proof-term at $TESTDIR/Bug_0043/Change#ShouldBeProvable
;;; Elaborating obligator at $TESTDIR/Bug_0043/Change#ShouldBeProvable
;;; Elaborating spec-morphism at $TESTDIR/Bug_0043/Change#FlipFlopImplementation
;;; Elaborating spec at $TESTDIR/Bug_0043/Change#Flipflop
;;; Elaborating spec at $TESTDIR/Bug_0043/Change#GiveNameToTilde
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Top
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Char
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer
;;; Elaborating spec at $SPECWARE/Library/ProverBase/List
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Option
;;; Elaborating spec at $SPECWARE/Library/ProverBase/String
;;; Elaborating spec at $SPECWARE/Library/ProverBase/System
;;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite
;; ensure-directories-exist: creating $TESTDIR/Bug_0043/Both/Change/ShouldBeProvable.log
;; Directory $TESTDIR/Bug_0043/Both/ does not exist, will create.
;; Directory $TESTDIR/Bug_0043/Both/Change/ does not exist, will create.
;;; Elaborating spec at $SPECWARE/Library/Base/ProverBase
ShouldBeProvable: Conjecture change is Proved! using Snark.
    Snark Log file: $TESTDIR/Bug_0043/Both/Change/ShouldBeProvable.log


")

 ("Bug 0045 : Unambiguous op erroneously declared ambiguous [toString]" 
  :sw  "Bug_0045/ToString"
  :output ";;; Elaborating spec at $TESTDIR/Bug_0045/ToString
")


 ("Bug 0045 : Unambiguous op erroneously declared ambiguous [FlipFlop]"
  :show   "Bug_0045/Flop#FlipFlopImplementation" 
  :output ";;; Elaborating spec-morphism at $TESTDIR/Bug_0045/Flop#FlipFlopImplementation
;;; Elaborating spec at $TESTDIR/Bug_0045/Flop#Flip
;;; Elaborating spec at $TESTDIR/Bug_0045/Flop#Flop
;;; Elaborating spec at $TESTDIR/Bug_0045/Flop#FlipFlopImplementation

morphism
    spec  
 type Flip
 op flip : Flip -> Flip
endspec

    ->
    spec  
 type A
 type B
 op A.flop : A -> A
 op B.flop : B -> B
endspec

    {type Flip
     +->
     A,
     op flip
     +->
     flop}
")

 ("Bug 0047 : prep -- process Aa"
  :swll  "Bug_0047/UpLo#Aa" 
  :output ";;; Elaborating spec at $TESTDIR/Bug_0047/UpLo#Aa
;;; Generating lisp file /tmp/cl-current-file.lisp
")
 
 ("Bug 0047 : prep -- process aA"
  :swll  "Bug_0047/UpLo#aA" 
  :output ";;; Elaborating spec at $TESTDIR/Bug_0047/UpLo#aA
;;; Generating lisp file /tmp/cl-current-file.lisp
")

 ("Bug 0047 : prep -- gen lisp for C"
  :swll  "Bug_0047/UpLo#C" 
  :output ";;; Elaborating spec at $TESTDIR/Bug_0047/UpLo#C
;;; Generating lisp file /tmp/cl-current-file.lisp
")

 ("Bug 0047 : Case insensitivity of Lisp considered harmful"
  :lisp "(print SW-USER::result_0047)"
  :output "
123 ")

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

 ("Bug 0067 : Signature constraints in spec morphism are not checked"
  :show   "Bug_0067/CheckSignature#M" 
  :output ";;; Elaborating spec-morphism at $TESTDIR/Bug_0067/CheckSignature#M
;;; Elaborating spec at $TESTDIR/Bug_0067/CheckSignature#S1
;;; Elaborating spec at $TESTDIR/Bug_0067/CheckSignature#S2
Error in morphism: Inconsistent op type mapping for f +-> g
The domain type A
  translates to B
   which is not C
 found in $TESTDIR/Bug_0067/CheckSignature.sw
14.13-14.14")

 ("Bug 0068 : Even numbers can be refined to odd numbers"
  :show   "Bug_0068/EvenToOdd#O" 
  :output ";;; Elaborating obligator at $TESTDIR/Bug_0068/EvenToOdd#O
;;; Elaborating spec-morphism at $TESTDIR/Bug_0068/EvenToOdd#M
;;; Elaborating spec at $TESTDIR/Bug_0068/EvenToOdd#S1
;;; Elaborating spec at $TESTDIR/Bug_0068/EvenToOdd#S2
Error in morphism: Inconsistent type def mapping for Even +-> Odd
The domain type {n : Nat | ex(m : Integer) n = 2 * m}
  translates to {n : Nat | ex(m : Integer) n = 2 * m}
   which is not {n : Nat | ex(m : Integer) n = 2 * m + 1}
 found in $TESTDIR/Bug_0068/EvenToOdd.sw
9.13-9.14")

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

 ("Bug 0069 : Morphism to base"
  :show   "Bug_0069/MorphismToBase#M" 
  :output ";;; Elaborating spec-morphism at $TESTDIR/Bug_0069/MorphismToBase#M
;;; Elaborating spec at $TESTDIR/Bug_0069/MorphismToBase#S
;;; Elaborating spec at $TESTDIR/Bug_0069/MorphismToBase#T

morphism
    spec  
 type SS
endspec

    ->
    spec  
endspec

    {type SS
     +->
     Char}
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


 ("Bug 0090 : Insufficient context to type-check case branches"
  :show   "Bug_0090/caseContext#O"
  :output ";;; Elaborating obligator at $TESTDIR/Bug_0090/caseContext#O
;;; Elaborating spec at $TESTDIR/Bug_0090/caseContext#S

spec  
 import S
 import /Library/Base/WFO
 conjecture f_Obligation0 is [a] fa(P : List(a)) natural?(100 div length P)
endspec

")

 ("Bug 0092 : Useless import of WFO"
  :show   "Bug_0092/BogusImport#O" 
  :output ";;; Elaborating obligator at $TESTDIR/Bug_0092/BogusImport#O
;;; Elaborating spec at $TESTDIR/Bug_0092/BogusImport#S

spec  
 import S
 import /Library/Base/WFO
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
    fa(x : Integer) ~(x >= 0) => natural?(- x)
 conjecture Integer.addition_def2_Obligation is 
    fa(n1 : PosNat, n2 : PosNat) 
     n1 + n2 = plus(n1, n2) 
     && - n1 + - n2 = -(plus(n1, n2)) && ~(lte(n1, n2)) => lte(n2, n1)
 conjecture Integer.addition_def2_Obligation0 is 
    fa(n1 : PosNat, n2 : PosNat) 
     n1 + n2 = plus(n1, n2) 
     && - n1 + - n2 = -(plus(n1, n2)) 
        && n1 + - n2 
           = if lte(n1, n2) then -(minus(n2, n1)) else minus(n1, n2) 
           && ~(lte(n1, n2)) => lte(n2, n1)
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

 ("Bug 0106 : Names not disambiguated when printing"
  :show   "Bug_0106/AmbiguousRef"
  :output ";;; Elaborating spec at $TESTDIR/Bug_0106/AmbiguousRef

spec  
 def b = Nat.toString
endspec

")

 ("Bug 0107 : Bogus Nil prints as []"
  :show   "Bug_0107/BogusNil"
  :output ";;; Elaborating spec at $TESTDIR/Bug_0107/BogusNil

spec  
 type NotList =  | Nil | Whatever
 def b : NotList = Nil
endspec

")

 ("Bug 0109 : Declarations not printed"
  :show   "Bug_0109/DeclsRequired"
  :output ";;; Elaborating spec at $TESTDIR/Bug_0109/DeclsRequired

spec  
 type YesNo =  | No | Yes
 type Affirm =  | Ok | Sure | Yes
 op y : List String
 op x : List Char
 op z : Affirm
 op g : Nat
 op f : Integer

 def y = []
 def x = []
 def z = Yes
 def g = 3
 def f = 3
endspec

")
 ;; end of tests
 )
