(test-directories ".")

(test 

 ("Bug 0047 : prep -- process Aa"
  :swll  "UpLo#Aa" 
  :output ";;; Elaborating spec at $TESTDIR/UpLo#Aa
;;; Generating lisp file /tmp/lgen_lisp_tmp.lisp
")
 
 ("Bug 0047 : prep -- process aA"
  :swll  "UpLo#aA" 
  :output ";;; Elaborating spec at $TESTDIR/UpLo#aA
;;; Generating lisp file /tmp/lgen_lisp_tmp.lisp
")

 ("Bug 0047 : prep -- gen lisp for C"
  :swll  "UpLo#C" 
  :output ";;; Elaborating spec at $TESTDIR/UpLo#C
;;; Generating lisp file /tmp/lgen_lisp_tmp.lisp
")

 ("Bug 0047 : Case insensitivity of Lisp considered harmful"
  :lisp "(let () (declare (special SW-USER::high_low  SW-USER::low_high)) (print (list SW-USER::high_low SW-USER::low_high)))"
  :output '((:optional "")
	    "(123 456)"
	    (:optional "")))
	    
 )
