(test-directories ".")

(test 

 ("Bug 0107 : Bogus Nil prints as []"
  :show   "BogusNil"
  :output ";;; Elaborating spec at $TESTDIR/BogusNil

spec  
 type NotList =  | Nil | Whatever
 
 op  b : NotList
 def b = Nil
endspec

")

 )
