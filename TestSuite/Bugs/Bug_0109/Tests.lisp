(test-directories ".")

(test 

 ("Bug 0109 : Declarations not printed"
  :show   "DeclsRequired"
  :output ";;; Elaborating spec at $TESTDIR/DeclsRequired

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

 )
