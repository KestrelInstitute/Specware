(test-directories ".")

(test 

 ("Bug 0106 : Names not disambiguated when printing"
  :show   "AmbiguousRef"
  :output ";;; Elaborating spec at $TESTDIR/AmbiguousRef

spec  
 def b = Nat.toString
endspec

")

 )
