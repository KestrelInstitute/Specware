;;;(test-files "proveOblig.sw" "simple.sw" "fib.sw"
;;;	    "colimit.sw"
;;;	    "tw-0103-1.sw" "tw-0103-2.sw" "tw-0103-3.sw"
;;;	    "players.sw")

(test-directories ".")

(test ("twk message 1/8/03" :sw "tw-0103-1"
			:output ";;; Processing spec at $TESTDIR/tw-0103-1#player
;;; Processing spec at $TESTDIR/tw-0103-1#position
;;; Processing spec at $TESTDIR/tw-0103-1#move
in $TESTDIR/tw-0103-1.sw
40.33-40.38 :  Could not match sort constraint
              legal? of sort move -> Boolean
          with expected sort Boolean
")
      ("twk message 1/8/03 fix 1"
       :sw "tw-0103-2"
       :output ";;; Processing spec at $TESTDIR/tw-0103-2#player
;;; Processing spec at $TESTDIR/tw-0103-2#position
;;; Processing spec at $TESTDIR/tw-0103-2#move
")
      ("twk message 1/8/03 fix 2"
       :sw "tw-0103-3"
       :output ";;; Processing spec at $TESTDIR/tw-0103-3#player
;;; Processing spec at $TESTDIR/tw-0103-3#position
;;; Processing spec at $TESTDIR/tw-0103-3#move
")
      )