(test-directories ".")

(test 

 ("Bug 0043 : Snark doesn't like Booleans"
  :show "Change#ShouldBeProvable" 
  :output ";;; Elaborating proof-term at $TESTDIR/Change#ShouldBeProvable
;;; Elaborating obligator at $TESTDIR/Change#ShouldBeProvable
;;; Elaborating spec-morphism at $TESTDIR/Change#FlipFlopImplementation
;;; Elaborating spec at $TESTDIR/Change#Flipflop
;;; Elaborating spec at $TESTDIR/Change#GiveNameToTilde
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Top
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Char
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer
;;; Elaborating spec at $SPECWARE/Library/ProverBase/List
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Option
;;; Elaborating spec at $SPECWARE/Library/ProverBase/String
;;; Elaborating spec at $SPECWARE/Library/ProverBase/System
;;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite
;; ensure-directories-exist: creating $TESTDIR/Snark/Change/ShouldBeProvable.log
;; Directory $TESTDIR/Snark/ does not exist, will create.
;; Directory $TESTDIR/Snark/Change/ does not exist, will create.
;;; Elaborating spec at $SPECWARE/Library/Base/ProverBase
ShouldBeProvable: Conjecture change is Proved! using Snark.
    Snark Log file: $TESTDIR/Snark/Change/ShouldBeProvable.log


")

 )
