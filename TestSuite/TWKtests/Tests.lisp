;;;(test-files "proveOblig.sw" "simple.sw" "fib.sw"
;;;	    "colimit.sw"
;;;	    "t0103_1.sw" "t0103_2.sw" "t0103_3.sw"
;;;         "Tuples.sw"
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
      ("twk_message 6/2/04"
       :sw "Switch"
       :output ";;; Elaborating spec at $TESTDIR/Switch#aspec
;;; Elaborating obligator at $TESTDIR/Switch#aspecobs
;;; Elaborating proof-term at $TESTDIR/Switch#p1
;; ensure-directories-exist: creating $TESTDIR/Snark/Switch/p1.log
;; Directory $TESTDIR/Snark/ does not exist, will create.
;; Directory $TESTDIR/Snark/Switch/ does not exist, will create.
p1: Conjecture doubleswitchidentity in aspec is Proved! using Snark.
    Snark Log file: $TESTDIR/Snark/Switch/p1.log
"
)

      ("twk_message 6/18/04"
       :sw "ThreeValue"
       :output ";;; Elaborating spec at $TESTDIR/ThreeValue#ThreeValues
;;; Elaborating spec at $TESTDIR/ThreeValue#ThreeValuesDef
;;; Elaborating spec-morphism at $TESTDIR/ThreeValue#ThreeM
;;; Elaborating obligator at $TESTDIR/ThreeValue#ThreeObs
;;; Elaborating proof-term at $TESTDIR/ThreeValue#ThreeP
;; ensure-directories-exist: creating $TESTDIR/Snark/ThreeValue/ThreeP.log
;; Directory $TESTDIR/Snark/ThreeValue/ does not exist, will create.
ThreeP: Theorem threedifferent in ThreeValuesDef is Proved! using Snark.
    Snark Log file: $TESTDIR/Snark/ThreeValue/ThreeP.log
")

      ("twk_message 8/2/04"
       :sw "MathFact"
       :output ";;; Elaborating spec at $TESTDIR/MathFact#mathfacts
;;; Elaborating spec at $TESTDIR/MathFact#sum_spec
;;; Elaborating obligator at $TESTDIR/MathFact#sum_spec_obs
;;; Elaborating proof-term at $TESTDIR/MathFact#sum_spec_p1
;; ensure-directories-exist: creating $TESTDIR/Snark/MathFact/sum_spec_p1.log
;; Directory $TESTDIR/Snark/MathFact/ does not exist, will create.
sum_spec_p1: Conjecture sum_zero in sum_spec_obs is NOT proved using Snark.
    Snark Log file: $TESTDIR/Snark/MathFact/sum_spec_p1.log
"
)
      ("twk_message 8/13/04"
       :sw "Tuples"
       :output ";;; Elaborating spec at $TESTDIR/Tuples#X1
;;; Elaborating obligator at $TESTDIR/Tuples#O1
;;; Elaborating proof-term at $TESTDIR/Tuples#P1
;; ensure-directories-exist: creating $TESTDIR/Snark/Tuples/P1.log
;; Directory $TESTDIR/Snark/Tuples/ does not exist, will create.
P1: Conjecture twoMakesMakeAMatch1 in O1 is Proved! using Snark.
    Snark Log file: $TESTDIR/Snark/Tuples/P1.log
;;; Elaborating proof-term at $TESTDIR/Tuples#P2
P2: Conjecture twoMakesMakeAMatch2 in O1 is Proved! using simple inequality reasoning.
    Snark Log file: $TESTDIR/Snark/Tuples/P2.log
"
)



      )
