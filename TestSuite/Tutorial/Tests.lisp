(cl-user::sw-init)

;;; Tutorial example
(test ("FindMatches" :sw "$SPECWARE/UserDoc/tutorial/example/MatchingSpecs#FindMatches"
                     :output ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#FindMatches
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#WordMatching
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Words
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Symbols
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Messages
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#SymbolMatching
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Matches
")
      ("FindMatches_Ref" :sw "$SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref"
                         :output ";;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref
;;; Elaborating spec-substitution at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches0
;;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching_Ref
;;; Elaborating spec-substitution at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching0
;;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#Symbols_Ref
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#Symbols
")
      ("MatchingProofs" :sw "$SPECWARE/UserDoc/tutorial/example/MatchingProofs"
                       :output ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p1
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#SymbolMatching_Oblig
;;; Elaborating spec at $SPECWARE/Library/Base/WFO
;;; Elaborating spec at $SPECWARE/Library/Base/ProverBase
p1: Conjecture symb_matches?_Obligation in MatchingObligations#SymbolMatching_Oblig is Proved!
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/snark/MatchingProofs/p1.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches0_Oblig
p3: Conjecture find_matches_aux_Obligation in MatchingObligations#FindMatches0_Oblig is NOT proved.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/snark/MatchingProofs/p3.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p4
p4: Conjecture word_matching_Obligation in MatchingObligations#FindMatches0_Oblig is Proved!
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/snark/MatchingProofs/p4.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p5
p5: Conjecture word_matching_Obligation0 in MatchingObligations#FindMatches0_Oblig is NOT proved.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/snark/MatchingProofs/p5.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p6
p6: Conjecture word_matching_Obligation1 in MatchingObligations#FindMatches0_Oblig is NOT proved.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/snark/MatchingProofs/p6.log
")
      ("swl find-matches" :swl "$SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches find-matches"
                       :output ";;; Generating lisp file find-matches.lisp
"
		       :files '("$TESTDIR/find-matches.lisp"))
      ("Load find-matches.lisp" :lisp "(let (#+allegro excl:*redefinition-warnings*)
                                         (specware::compile-and-load-lisp-file \"$TESTDIR/find-matches.lisp\"))")
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
