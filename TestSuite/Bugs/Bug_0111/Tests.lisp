(test-directories ".")

(test 

 ("Bug 0111 : Capture of translated ops by var bindings [Once]"
  :show   "Capture#T"
  :output ";;; Elaborating spec-translation at $TESTDIR/Capture#T
;;; Elaborating spec at $TESTDIR/Capture#S

spec  
 
 op  g : Nat -> Integer
 def g n = let xx0 = n in 
           xx0 + xx
 
 op  h : Integer -> Integer
 def h n = let def ww0 n = n
           in 
           ww0 n + ww n
 
 op  ff : Nat -> Integer
 def ff xx0 = xx0 + xx
 
 op  ww : Nat -> Nat
 
 op  xx : Nat
 axiom foo is fa(xx0 : Nat) xx0 = xx0 + xx
endspec

")

 ("Bug 0111 : Capture of translated ops by var bindings [Repeated]"
  :show   "Capture#W"
  :output ";;; Elaborating spec-translation at $TESTDIR/Capture#W

spec  
 
 op  g : Nat -> Integer
 def g n = let xx0 = n in 
           xx0 + aa
 
 op  h : Integer -> Integer
 def h n = let def ww0 n = n
           in 
           ww0 n + bb n
 
 op  ff : Nat -> Integer
 def ff xx0 = xx0 + aa
 
 op  aa : Nat
 
 op  bb : Nat -> Nat
 axiom foo is fa(xx0 : Nat) xx0 = xx0 + aa
endspec

")

 )