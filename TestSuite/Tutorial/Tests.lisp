(cl-user::sw-init)

;;; Tutorial example
(test ("FindMatches" :sw "/UserDoc/tutorial/example/MatchingSpecs#FindMatches"
                     :output ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#FindMatches
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#WordMatching
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Words
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Symbols
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Messages
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#SymbolMatching
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Matches
")
      ("FindMatches_Ref" :sw "/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref"
                         :output ";;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref
;;; Elaborating spec-substitution at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches0
;;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching_Ref
;;; Elaborating spec-substitution at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching0
;;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#Symbols_Ref
;;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#Symbols
")
      ("MatchingProofs" :sw "/UserDoc/tutorial/example/MatchingProofs"
                       :output ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p1
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#SymbolMatching_Oblig
;;; Elaborating spec at $SPECWARE/Library/Base/WFO
;;; Elaborating spec at $SPECWARE/Library/Base/ProverBase
;;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite
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
      ("swl find-matches" :swl "/UserDoc/tutorial/example/MatchingRefinements#FindMatches $TESTDIR/find-matches"
                       :output ";;; Generating lisp file $TESTDIR/find-matches.lisp
"
		       :files '("$TESTDIR/find-matches.lisp"))
      ("Load find-matches.lisp" :lisp "(let (#+allegro excl:*redefinition-warnings*)
                                         (specware::compile-and-load-lisp-file \"$TESTDIR/find-matches.lisp\"))")
      ("swll MatchingTest#Test" :swll "/UserDoc/tutorial/example/MatchingTest#Test"
				:output ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingTest#Test
;;; Generating lisp file /tmp/cl-current-file.lisp
")
      ("test_find_matches" :swe "test_find_matches(\"**V*ALN**EC*E*S\",
                                                   [\"CERAMIC\", \"CHESS\", \"DECREE\", \"FOOTMAN\",
                                                    \"INLET\", \"MOLOCH\", \"OCELOT\", \"PROFUSE\",
                                                    \"RESIDE\", \"REVEAL\", \"SECRET\", \"SODIUM\",
                                                    \"SPECIES\", \"VESTIGE\", \"WALNUT\", \"YOGURT\"])"
			   :swe-spec "$SPECWARE/UserDoc/tutorial/example/MatchingTest#Test"
			   :value '(:|Constructor| "Cons" :|RecordVal|
				    ("1" :|RecordVal| ("position" :|Int| . 3) ("word" :|String| . "WALNUT"))
				    ("2" :|Constructor| "Cons" :|RecordVal|
				     ("1" :|RecordVal| ("position" :|Int| . 7) ("word" :|String| . "SPECIES"))
				     ("2" :|Constructor| "Cons" :|RecordVal|
				      ("1" :|RecordVal| ("position" :|Int| . 8) ("word" :|String| . "SECRET"))
				      ("2" :|Constructor| "Cons" :|RecordVal|
				       ("1" :|RecordVal| ("position" :|Int| . 0) ("word" :|String| . "REVEAL"))
				       ("2" :|Constructor| "Cons" :|RecordVal|
					    ("1" :|RecordVal| ("position" :|Int| . 8) ("word" :|String| . "DECREE"))
					    ("2" :|Constructor| "Cons" :|RecordVal|
						 ("1" :|RecordVal| ("position" :|Int| . 10) ("word" :|String| . "CHESS"))
						 ("2" :|Constant| . "Nil"))))))))
      ("test_find_matches="
       :swe "test_find_matches(\"**V*ALN**EC*E*S\",
                               [\"CERAMIC\", \"CHESS\", \"DECREE\", \"FOOTMAN\",
				\"INLET\", \"MOLOCH\", \"OCELOT\", \"PROFUSE\",
				\"RESIDE\", \"REVEAL\", \"SECRET\", \"SODIUM\",
				\"SPECIES\", \"VESTIGE\", \"WALNUT\", \"YOGURT\"])
	       = [{position=3,word=\"WALNUT\"},
		  {position=7,word=\"SPECIES\"},
		  {position=8,word=\"SECRET\"},
		  {position=0,word=\"REVEAL\"},
		  {position=8,word=\"DECREE\"},
		  {position=10,word=\"CHESS\"}]"
       :swe-spec "$SPECWARE/UserDoc/tutorial/example/MatchingTest#Test"
       :value '(:|Bool| . T))
)
