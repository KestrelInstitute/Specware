(test-directories ".")

;; Test is now moot -- obligation is no longer generated
'(test 

 ("Bug 0131 : Attempting to prove simple Option obligation breaks into Lisp"
  :sw "Option#P"
  :output '(
	    ";;; Elaborating obligator at $TESTDIR/Option#P"
	    ";;; Elaborating spec at $TESTDIR/Option#O"
	    (:optional ";;; Elaborating spec at $SPECWARE/Provers/ProofChecker/Libs")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General/FiniteStructures")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General/FiniteSequences")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General/Order")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General/EndoRelation")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General/Relation")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General/Set")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General/FiniteMap")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General/FiniteSet")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General/Map")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/General/Assert")

            (:optional ";;; Elaborating spec at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist")
            (:optional ";;; Elaborating spec at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist#SimpleAsAlist")

            (:optional ";;; Elaborating spec-substitution at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist")
            (:optional ";;; Elaborating spec-substitution at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist#SimpleAsAlist")

            (:optional ";;; Elaborating spec at $SPECWARE/Library/Structures/Data/Maps/Simple")
            (:optional ";;; Elaborating spec at $SPECWARE/Library/Structures/Data/Maps/Simple#Simple")

            (:optional ";;; Elaborating spec at $SPECWARE/Library/Structures/Data/Maps/Simple#Map")

            (:optional ";;; Elaborating spec-morphism at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist")
            (:optional ";;; Elaborating spec-morphism at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist#SimpleAsAlist")

            (:optional ";;; Elaborating spec at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist#MapList")
            (:optional ";;; Elaborating spec at $SPECWARE/Library/Legacy/Utilities/System")

            (:optional ";;; Elaborating spec-substitution at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist")
            (:optional ";;; Elaborating spec-substitution at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist#SimpleAsAlist")

            (:optional ";;; Elaborating spec-morphism at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist")
            (:optional ";;; Elaborating spec-morphism at $SPECWARE/Library/Structures/Data/Maps/SimpleAsAlist#SimpleAsAlist")

            (:optional ";;; Elaborating spec at $SPECWARE/Provers/ProofChecker/IntegerExt")
            (:optional ";;; Elaborating spec at $SPECWARE/Provers/ProofChecker/StateAndExceptionMonads")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    (:optional ";;; Elaborating proof-term at $TESTDIR/Option#P")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Option")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/String")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/ProverBase/System")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite")
	    (:optional ";; ensure-directories-exist: creating $TESTDIR/Snark/..log")
	    (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	    (:optional "creating directory: $TESTDIR/Snark/")
	    (:optional "creating directory: $TESTDIR/Snark/Option/")
	    (:optional "    Expanded spec file: $TESTDIR/Snark/Option/P.sw")
	    (:optional "    Snark Log file: $TESTDIR/Snark/Option/P.log")
            "P: Conjecture PFunction.o_Obligation_exhaustive is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 )
