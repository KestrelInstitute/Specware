; (cl-user::sw-init)

;;; Bug 83: "Ambiguous op not detected"
(test-directories ".")
(test ("Bug 0083" :show "Bug_0083#C" 
		  :output 
";;; Elaborating spec at $TESTDIR/Bug_0083#C
;;; Elaborating spec at $TESTDIR/Bug_0083#A
;;; Elaborating spec at $TESTDIR/Bug_0083#B
ERROR: in specification: 

Ambiguous ops: 
 (* Warning: Multiple definitions for following op *) 
 def f =
  (fn n ->
    (n + 1))
 def f =
  (fn n ->
    (n + 2))

 found in $TESTDIR/Bug_0083.sw
3.4-3.43"))
