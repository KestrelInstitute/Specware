;;;(test-files "proveOblig.sw" "simple.sw" "fib.sw"
;;;	    "colimit.sw"
;;;	    "t0103_1.sw" "t0103_2.sw" "t0103_3.sw"
;;;	    "players.sw")

(test-directories ".")

(test ("twk message 1/8/03" :sw "t0103_1"
			:output ";;; Elaborating spec at $TESTDIR/t0103_1#player
;;; Elaborating spec at $TESTDIR/t0103_1#position
;;; Elaborating spec at $TESTDIR/t0103_1#move
Errors in $TESTDIR/t0103_1.sw
40.33-40.38	: Could not match type constraint
              legal? of type move -> Boolean
          with expected type Boolean
")
      ("twk message 1/8/03 fix 1"
       :sw "t0103_2"
       :output ";;; Elaborating spec at $TESTDIR/t0103_2#player
;;; Elaborating spec at $TESTDIR/t0103_2#position
;;; Elaborating spec at $TESTDIR/t0103_2#move
")
      ("twk message 1/8/03 fix 2"
       :sw "t0103_3"
       :output ";;; Elaborating spec at $TESTDIR/t0103_3#player
;;; Elaborating spec at $TESTDIR/t0103_3#position
;;; Elaborating spec at $TESTDIR/t0103_3#move
")
      )
