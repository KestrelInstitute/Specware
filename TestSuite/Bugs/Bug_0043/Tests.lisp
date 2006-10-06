(test-directories ".")

(test 

 ("Bug 0043 : Snark doesn't like Booleans"
  :show "Change#ShouldBeProvable" 
  :output '(";;; Elaborating obligator at $TESTDIR/Change#ShouldBeProvable"
	    ";;; Elaborating spec-morphism at $TESTDIR/Change#FlipFlopImplementation"
	    ";;; Elaborating spec at $TESTDIR/Change#Flipflop"
	    ";;; Elaborating spec at $TESTDIR/Change#GiveNameToTilde"
	    ";;; Elaborating proof-term at $TESTDIR/Change#ShouldBeProvable"
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
	    (:optional ";; ensure-directories-exist: creating")
	    (:optional ";;   $TESTDIR/Snark/Change/ShouldBeProvable.log")
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/Change/ShouldBeProvable.log")
	    (:optional "creating directory: $TESTDIR/Snark/")
	    (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	    (:optional "creating directory: $TESTDIR/Snark/Change/")
	    (:optional ";; Directory $TESTDIR/Snark/Change/ does not exist, will create.")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
	    "    Expanded spec file: $TESTDIR/Snark/Change/ShouldBeProvable.sw"
	    "    Snark Log file: $TESTDIR/Snark/Change/ShouldBeProvable.log"
	    "ShouldBeProvable: Conjecture change is Proved! using Snark*."
	    ""
	    ""
	    ""))

 )
