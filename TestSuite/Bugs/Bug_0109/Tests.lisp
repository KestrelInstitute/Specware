(test-directories ".")

(test 

 ("Bug 0109 : Declarations not printed"
  :show   "DeclsRequired"
  :output ";;; Elaborating spec at $TESTDIR/DeclsRequired

spec  
 type YesNo =  | No | Yes
 type Affirm =  | Ok | Sure | Yes
 
 op  y : List(String)
 def y = []
 
 op  x : List(Char)
 def x = []
 
 op  z : Affirm
 def z = Yes
 
 op  g : Nat
 def g = 3
 
 op  f : Integer
 def f = 3
endspec

")

 )
