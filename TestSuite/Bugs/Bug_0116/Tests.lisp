(test-directories ".")

(test 
 ("Bug 0116 : Error in removeCurrying"
  :sw  "RemCurr#P"
  :output    '(
	       (:optional "")
	       ";;; Elaborating spec at $TESTDIR/RemCurr#S"
	       ";;; Elaborating proof-term at $TESTDIR/RemCurr#P"
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top")
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char")
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare")
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions")
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer")
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List")
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat")
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Option")
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/String")
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/System")
	       (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite")
	       (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/RemCurr/P.log")
	       (:optional "creating directory: $TESTDIR/Snark/")
	       (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	       (:optional "creating directory: $TESTDIR/Snark/RemCurr/")
	       (:optional ";; Directory $TESTDIR/Snark/RemCurr/ does not exist, will create.")
	       "    Expanded spec file: $TESTDIR/Snark/RemCurr/P.sw"
	       "    Snark Log file: $TESTDIR/Snark/RemCurr/P.log"
	       "P: Conjecture TRUE in S is Proved! using simple inequality reasoning."
	       (:optional "")
	       (:optional "")
	       ))

 )