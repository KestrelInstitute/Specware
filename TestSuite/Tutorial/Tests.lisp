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
;;; Elaborating spec at $SPECWARE/Library/Base/ProverBase
p1: Conjecture symb_matches?_Obligation in MatchingObligations#SymbolMatching_Oblig is Proved! using Snark.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p1.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p2
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching_Oblig
p2: Conjecture word_matches_at?_Obligation in MatchingObligations#WordMatching_Oblig is Proved! using simple inequality reasoning.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3
p3: Conjecture word_matches_at?_Obligation0 in MatchingObligations#WordMatching_Oblig is Proved! using simple inequality reasoning.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p5
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching0_Oblig
p5: Conjecture word_matches_at?_Obligation in MatchingObligations#WordMatching0_Oblig is Proved! using simple inequality reasoning.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p6
p6: Conjecture word_matches_at?_Obligation0 in MatchingObligations#WordMatching0_Oblig is Proved! using simple inequality reasoning.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p6.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p7
p7: Conjecture word_matches_at?_Obligation1 in MatchingObligations#WordMatching0_Oblig is NOT proved using Snark.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p7.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p8
p8: Conjecture word_matches_aux?_Obligation in MatchingObligations#WordMatching0_Oblig is NOT proved using Snark.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p8.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p9
p9: Conjecture word_matches_aux?_Obligation0 in MatchingObligations#WordMatching0_Oblig is NOT proved using Snark.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p9.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p10
p10: Conjecture word_matches_aux?_Obligation1 in MatchingObligations#WordMatching0_Oblig is Proved! using Snark.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p10.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p12
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches0_Oblig
p12: Conjecture find_matches_Obligation in MatchingObligations#FindMatches0_Oblig is Proved! using Snark.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p12.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p13
p13: Conjecture find_matches_aux_Obligation in MatchingObligations#FindMatches0_Oblig is Proved! using simple inequality reasoning.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p13.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p14
p14: Conjecture find_matches_aux_Obligation0 in MatchingObligations#FindMatches0_Oblig is NOT proved using Snark.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p14.log
;;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p15
;;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches_Ref0_Oblig
;;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref0
p15: Conjecture match_finding in MatchingObligations#FindMatches_Ref0_Oblig is NOT proved using Snark.
    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p15.log
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
