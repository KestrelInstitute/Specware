;;;(test-files "proveOblig.sw" "simple.sw" "fib.sw"
;;;	    "colimit.sw"
;;;	    "tw-0103-1.sw" "tw-0103-2.sw" "tw-0103-3.sw"
;;;	    "players.sw")

(test-directories ".")

(test ("NormalFib" :sw "fib"
		   :output ";;; Elaborating spec-form at $TESTDIR/fib
")
      ("CompileFib" :swll "fib"
		    :output ";;; Generating lisp file /tmp/cl-current-file.lisp
;;; Compiling file /tmp/cl-current-file.lisp
;;; Writing fasl file /tmp/cl-current-file.fasl
;;; Fasl write complete
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
       :output ";;; Elaborating spec-form at $TESTDIR/colimit#A
;;; Elaborating diagram-term at $TESTDIR/colimit#D
;;; Elaborating diagram-colimit at $TESTDIR/colimit#C
;;; Elaborating spec-form at $TESTDIR/colimit#E
")
      ("libtest" :swll "libtest"
		 :output ";;; Elaborating spec-form at $TESTDIR/libtest
;;; Generating lisp file /tmp/cl-current-file.lisp
;;; Compiling file /tmp/cl-current-file.lisp
;;; Writing fasl file /tmp/cl-current-file.fasl
;;; Fasl write complete
")
      )
