;;;(test-files "proveOblig.sw" "simple.sw" "fib.sw"
;;;	    "colimit.sw"
;;;	    "tw-0103-1.sw" "tw-0103-2.sw" "tw-0103-3.sw"
;;;	    "players.sw")

(test-directories ".")

(test ("NormalFib" :sw "fib"
		  :output ";;; Processing spec at $TESTDIR/fib
")
      ("twk message 1/10/03 Reused name leading to circularity."
       :sw "players#twoPlayersLisp"
       :files '("lisp/players.lisp")
       :output ";;; Processing spec at $TESTDIR/players#players
;;; Processing spec at $TESTDIR/players#twoPlayers
;;; Processing spec at $TESTDIR/players#twoPlayersImpl
;;; Processing spec morphism at $TESTDIR/players#twoPlayers
;; ensure-directories-exist: creating
;;   $TESTDIR/lisp/players.lisp
;; Directory $TESTDIR/lisp/ does not exist, will create.
;;; Generating lisp file $TESTDIR/lisp/players.lisp
")
      ("twk message 1/10/03 Reused name leading to circularity. Repetition gives error?"
       :sw "players#twoPlayersLisp"
       :output "")
      ("Colimit with no sharing"
       :sw "colimit"
       :output ";;; Processing spec at $TESTDIR/colimit#A
;;; Processing spec diagram at $TESTDIR/colimit#D
;;; Processing colimit at $TESTDIR/colimit#C
;;; Processing spec at $TESTDIR/colimit#E
")
      )