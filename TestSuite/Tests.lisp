;;;(test-files "proveOblig.sw" "simple.sw" "fib.sw"
;;;	    "colimit.sw"
;;;	    "tw-0103-1.sw" "tw-0103-2.sw" "tw-0103-3.sw"
;;;	    "players.sw")

(test-directories ".")

(test ("NormalFib" :sw "fib"
		  :output ";;; Processing spec at $TESTDIR/fib
")
      ("CompileFib" :swll "fib"
		  :output ";;; Generating lisp file /tmp/cl-current-file.lisp
;;; Compiling file /tmp/cl-current-file.lisp
;;; Writing fasl file /tmp/cl-current-file.fasl
;;; Fasl write complete
; Fast loading /tmp/cl-current-file.fasl
")
      ("RunFib" :swe "computeFib 10"
		:swe-spec "fib"
		:value 89)
      ("twk message 1/10/03 Reused name leading to circularity."
       :sw "players#twoPlayersLisp"
       :file-goto-error '("$TESTDIR/players.sw" 43 13)
       :output "Error in specification: Name \"twoPlayers\" defined twice in file.
  found in $TESTDIR/players.sw
43.13-44.52")
      ("Colimit with no sharing"
       :sw "colimit"
       :output ";;; Processing spec at $TESTDIR/colimit#A
;;; Processing spec diagram at $TESTDIR/colimit#D
;;; Processing colimit at $TESTDIR/colimit#C
;;; Processing spec at $TESTDIR/colimit#E
")
      ("libtest":swll "libtest"
		:output ";;; Processing spec at $TESTDIR/libtest
;;; Generating lisp file /tmp/cl-current-file.lisp
;;; Compiling file /tmp/cl-current-file.lisp
;;; Writing fasl file /tmp/cl-current-file.fasl
;;; Fasl write complete
; Fast loading /tmp/cl-current-file.fasl
")
      )