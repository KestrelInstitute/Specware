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
      )