; (cl-user::sw-init)

;;; Bug 45 : "Unambiguous op erroneously declared ambiguous"
(test-directories ".")
(test 

 ("Bug 0045 A (toString)" 
  :show   "Bug_0045_A" 
  :output ";;; Elaborating spec at $TESTDIR/Bug_0045_A

spec  
 def b = Nat.toString
endspec

")


 ("Bug 0045 B (FlipFlop)" 
  :show   "Bug_0045_B#FlipFlopImplementation" 
  :output ";;; Elaborating spec-morphism at $TESTDIR/Bug_0045_B#FlipFlopImplementation
;;; Elaborating spec at $TESTDIR/Bug_0045_B#Flipflop
;;; Elaborating spec at $TESTDIR/Bug_0045_B#FlipFlopImplementation

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
 
 )
