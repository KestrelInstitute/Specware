(test-directories ".")

(test 

 ("Bug 0111 : Capture of translated ops by var bindings [T]"
  :show   "Capture#T"
  :output ";;; Elaborating spec-translation at $TESTDIR/Capture#T
;;; Elaborating spec at $TESTDIR/Capture#S

spec  
 
 op  f : Nat -> Integer
 def f x1 = x1 + x
 
 op  x : Nat
endspec

")

 ("Bug 0111 : Capture of translated ops by var bindings [W]"
  :show   "Capture#W"
  :output ";;; Elaborating spec-translation at $TESTDIR/Capture#W

spec  
 
 op  f : Nat -> Integer
 def f x = x + w
 
 op  w : Nat
endspec

")

 )