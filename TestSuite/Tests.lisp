;;;(test-files "proveOblig.sw" "simple.sw" "fib.sw"
;;;	    "colimit.sw"
;;;	    "tw-0103-1.sw" "tw-0103-2.sw" "tw-0103-3.sw"
;;;	    "players.sw")

(cl-user::sw-init)

(test-directories ".")

(test ("NormalFib" :sw "fib"
		   :output ";;; Elaborating spec at $TESTDIR/fib
")
      ("CompileFib" :swll "fib"
		    :output ";;; Generating lisp file /tmp/cl-current-file.lisp
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
       :output ";;; Elaborating spec at $TESTDIR/colimit#A
;;; Elaborating diagram-term at $TESTDIR/colimit#D
;;; Elaborating diagram-colimit at $TESTDIR/colimit#C
;;; Elaborating spec at $TESTDIR/colimit#E
")
      ("libtest" :swll "libtest"
		 :output ";;; Elaborating spec at $TESTDIR/libtest
;;; Generating lisp file /tmp/cl-current-file.lisp
")
      )

;;; Tutorial example
(test ("FindMatches" :sw "$SPECWARE/UserDoc/tutorial/example/MatchingSpecs#FindMatches"
                     :output ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Symbols
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Words
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Messages
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#SymbolMatching
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#WordMatching
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Matches
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#FindMatches
")
      ("FindMatches_Ref" :sw "$SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref"
                         :output ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#Symbols
;;; Elaborating spec morphism-term at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#Symbols_Ref
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching0
;;; Elaborating spec morphism-term at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching_Ref0
;;; Elaborating spec-substitution at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching
;;; Elaborating spec morphism-term at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching_Ref
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches0
;;; Elaborating spec morphism-term at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref0
;;; Elaborating spec-substitution at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches
;;; Elaborating spec morphism-term at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref
")
      ("MatchingProofs" :sw "$SPECWARE/UserDoc/tutorial/example/MatchingProofs"
                       :output ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p1
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#SymbolMatching_Oblig
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching_Oblig
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#Symbols_Ref_Oblig
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching0_Oblig
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching_Ref0_Oblig
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches0_Oblig
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches_Ref0_Oblig
;;; Elaborating spec at $SPECWARE/Library/Base/ProverBase
p1: Conjecture symb_matches? in MatchingObligations#SymbolMatching_Oblig is Proved!
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/snark/MatchingProofs/p1.log
")
      ("swl find-matches" :swl "$SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches find-matches"
                       :output ";;; Generating lisp file find-matches.lisp
"
		       :files '("$TESTDIR/find-matches.lisp"))
      ("Load find-matches.lisp" :lisp "(load \"$TESTDIR/find-matches.lisp\")")
      ("swll MatchingTest#Test" :swll "$SPECWARE/UserDoc/tutorial/example/MatchingTest#Test"
                       :output ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingTest#Test
;;; Generating lisp file /tmp/cl-current-file.lisp
")
      ("test_find_matches" :swe "test_find_matches(\"**V*ALN**EC*E*S\",
                                                   [\"CERAMIC\", \"CHESS\", \"DECREE\", \"FOOTMAN\",
                                                    \"INLET\", \"MOLOCH\", \"OCELOT\", \"PROFUSE\",
                                                    \"RESIDE\", \"REVEAL\", \"SECRET\", \"SODIUM\",
                                                    \"SPECIES\", \"VESTIGE\", \"WALNUT\", \"YOGURT\"])"
			   :swe-spec "$SPECWARE/UserDoc/tutorial/example/MatchingTest#Test"
			   :value '((3 . "WALNUT") (7 . "SPECIES") (8 . "SECRET")
				    (0 . "REVEAL") (8 . "DECREE") (10 . "CHESS")))
)
