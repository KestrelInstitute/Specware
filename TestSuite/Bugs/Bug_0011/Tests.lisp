(test-directories ".")

(test 

 ("Bug 0011 : Consider abbreviating printed path names."
  :show "abc"
  :output ";;; Elaborating spec at $TESTDIR/abc
;;; Elaborating spec at $TESTDIR/xyz

spec  
 import xyz
endspec

")

 )
