(test-directories ".")

(test 

 ("Bug 0107 : Bogus Nil prints as []"
  :show   "BogusNil"
  :output ";;; Elaborating spec at $TESTDIR/BogusNil

spec  
 type NotList =  | Nil | Whatever
 def b : NotList = Nil
endspec

")

 )
