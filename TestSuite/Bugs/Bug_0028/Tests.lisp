(test-directories ".")

(test 

 ("Bug 0028 : A few sort names such as Filename are mysteriously problematic."
  :show "ProblematicTypes"
  :output ";;; Elaborating spec at $TESTDIR/ProblematicTypes

spec  
 type LineColumn = Nat
 type Filename = String
 type LineColumnByte = Nat
 type Position = Nat
endspec

")

 )
