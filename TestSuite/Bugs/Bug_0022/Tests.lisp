(test-directories ".")

(test 

 ("Bug 0022 : Redefined ops processed without giving error message [OpDef]."
  :show "RedefinedOp#OpDef"
  :output ";;; Elaborating spec at $TESTDIR/RedefinedOp#OpDef

spec  
 
 op  f : Nat
 def f = 3
endspec

")

 ("Bug 0022 : Redefined ops processed without giving error message [DefOp]"
  :sw "RedefinedOp#DefOp"
  :output ";;; Elaborating spec at $TESTDIR/RedefinedOp#DefOp
Error in specification: Operator f has been redeclared
 from 3
   to <anyterm>: Nat
 found in $TESTDIR/RedefinedOp.sw
8.1-8.10")

 ("Bug 0022 : Redefined ops processed without giving error message [DefDef]"
  :sw "RedefinedOp#DefDef"
  :output ";;; Elaborating spec at $TESTDIR/RedefinedOp#DefDef
Error in specification: Operator f has been redefined
 from 3
   to 3
 found in $TESTDIR/RedefinedOp.sw
13.1-13.9")

 ("Bug 0022 : Redefined ops processed without giving error message [OpOp]"
  :sw "RedefinedOp#OpOp"
  :output ";;; Elaborating spec at $TESTDIR/RedefinedOp#OpOp
Error in specification: Operator f has been redeclared
 from Nat
   to Nat
 found in $TESTDIR/RedefinedOp.sw
18.1-18.10")

 ("Bug 0022 : Redefined ops processed without giving error message [OpDefOp]"
  :sw "RedefinedOp#OpDefOp"
  :output ";;; Elaborating spec at $TESTDIR/RedefinedOp#OpDefOp
Error in specification: Operator f has been redeclared
 from 3: Nat
   to <anyterm>: Nat
 found in $TESTDIR/RedefinedOp.sw
24.1-24.10")

 ("Bug 0022 : Redefined ops processed without giving error message [OpDefDef]"
  :sw "RedefinedOp#OpDefDef"
  :output ";;; Elaborating spec at $TESTDIR/RedefinedOp#OpDefDef
Error in specification: Operator f has been redefined
 from 3: Nat
   to 3
 found in $TESTDIR/RedefinedOp.sw
30.1-30.9")

 )
