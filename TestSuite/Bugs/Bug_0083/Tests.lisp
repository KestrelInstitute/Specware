(test-directories ".")

(test 

 ("Bug 0083 : Ambiguous op not detected"
  :show   "Ambop#C" 
  :output ";;; Elaborating spec at $TESTDIR/Ambop#C
;;; Elaborating spec at $TESTDIR/Ambop#A
;;; Elaborating spec at $TESTDIR/Ambop#B
Error in specification: 

Ambiguous ops: 
 (* Warning: Multiple definitions for following op *) 
 def f =
  (fn n ->
    (n + 1))
 def f =
  (fn n ->
    (n + 2))

 found in $TESTDIR/Ambop.sw
3.4-3.43")

 )
