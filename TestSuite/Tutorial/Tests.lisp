(cl-user::sw-init)

(let ((common-lisp::*print-level* 12))
;;; Tutorial example
  (test 

   ("Tutorial: FindMatches" 
    :sw "/UserDoc/tutorial/example/MatchingSpecs#FindMatches"
    :output '(";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#FindMatches"
	      ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#WordMatching"
	      ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Words"
	      ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Symbols"
	      ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Messages"
	      ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#SymbolMatching"
	      ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Matches"
	      (:optional "")
	      (:optional "")
	      ))

   ("Tutorial: FindMatches_Ref" 
    :sw "/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref"
    :output '(";;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref"
	      ";;; Elaborating spec-substitution at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches"
	      ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches0"
	      ";;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching_Ref"
	      ";;; Elaborating spec-substitution at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching"
	      ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching0"
	      ";;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#Symbols_Ref"
	      ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#Symbols"
	      (:optional "")
	      (:optional "")
	      ))

   ("Tutorial: prwb" 
    :swprb t
    :output '((:optional "T")
              (:optional "t")
	      (:optional "")
	      (:optional "")
	      ))
   ("Tutorial: MatchingProofs p2A (subtype)" 
    :sw "/UserDoc/tutorial/example/MatchingProofs#p2A"
    :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching_Oblig"
	      ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p2A"
              (:optional 
               ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top"
               ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char"
               ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare"
               ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions"
               ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer"
               ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List"
               ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Option"
               ";;; Elaborating spec at $SPECWARE/Library/ProverBase/String")
	      "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2A.sw"
	      "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2A.log"
	      "p2A: Conjecture word_matches_at?_Obligation_subtype in MatchingObligations#WordMatching_Oblig is Proved! *"
	      (:optional "")
	      (:optional "")
	      ))

   ("Tutorial: MatchingProofs p2B (subtype)" 
    :sw "/UserDoc/tutorial/example/MatchingProofs#p2B"
    :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p2B"
	      "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2B.sw"
	      "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2B.log"
	      "p2B: Conjecture word_matches_at?_Obligation_subtype0 in MatchingObligations#WordMatching_Oblig is Proved! *"
	      (:optional "")
	      (:optional "")
	      ))
      
   ("Tutorial: MatchingProofs p3A (subtype)"
    :sw "/UserDoc/tutorial/example/MatchingProofs#p3A"
    :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching0_Oblig"
	      ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3A"
	      "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3A.sw"
	      "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3A.log"
	      "p3A: Conjecture word_matches_at?_Obligation_subtype in MatchingObligations#WordMatching0_Oblig is Proved! *"
	      (:optional "")
	      (:optional "")
	      ))

   ("Tutorial: MatchingProofs p3B (subtype)" 
    :sw "/UserDoc/tutorial/example/MatchingProofs#p3B"
    :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3B"
	      "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3B.sw"
	      "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3B.log"
	      "p3B: Conjecture word_matches_at?_Obligation_subtype0 in MatchingObligations#WordMatching0_Oblig is Proved! *"
	      (:optional "")
	      (:optional "")
	      ))

   ("Tutorial: MatchingProofs p3C (subtype)" 
    :sw "/UserDoc/tutorial/example/MatchingProofs#p3C"
    :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3C"
	      "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3C.sw"
	      "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3C.log"
	      ;; Sigh.  "C:" becomes "" in test output processing   
	      "p3C: Conjecture word_matches_aux?_Obligation_subtype in MatchingObligations#WordMatching0_Oblig is Proved! *"
	      (:optional "")
	      (:optional "")
	      ))

					; fails
   ("Tutorial: MatchingProofs p3D (uniqueness)" 
    :sw "/UserDoc/tutorial/example/MatchingProofs#p3D"
    :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3D"
	      "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3D.sw"
	      "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3D.log"
	      "p3D: Conjecture word_matches_aux?_Obligation_uniqueness in MatchingObligations#WordMatching0_Oblig is Proved! *"
	      (:optional "")
	      (:optional "")
	      ))

					; fails
   ("Tutorial: MatchingProofs p4A (def)"
    :sw "/UserDoc/tutorial/example/MatchingProofs#p4A"
    :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching_Ref0_Oblig"
	      ";;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#WordMatching_Ref0"
	      ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p4A"
	      "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p4A.sw"
	      "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p4A.log"
	      "p4A: Conjecture word_matches_at?_def in MatchingObligations#WordMatching_Ref0_Oblig is Proved! *"
	      (:optional "")
	      (:optional "")
	      ))

   ("Tutorial: MatchingProofs p5B (subtype)"
    :sw "/UserDoc/tutorial/example/MatchingProofs#p5B"
    :output '((:optional ";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches0_Oblig")
              ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p5B"
	      "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5B.sw"
	      "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5B.log"
	      "p5B: Conjecture find_matches_aux_Obligation_subtype in MatchingObligations#FindMatches0_Oblig is Proved! *"
	      (:optional "")
	      (:optional "")
	      ))

					; fails
   ("Tutorial: MatchingProofs p5C (uniqueness)"
    :sw "/UserDoc/tutorial/example/MatchingProofs#p5C"
    :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p5C"
	      "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5C.sw"
	      "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5C.log"
	      ;; Sigh.  "C:" becomes "" in test output processing   
	      "p5 Conjecture find_matches_aux_Obligation_uniqueness in MatchingObligations#FindMatches0_Oblig is Proved! *"
	      (:optional "")
	      (:optional "")
	      ))
      
					; fails
   ("Tutorial: MatchingProofs p6 (explicit)"
    :sw "/UserDoc/tutorial/example/MatchingProofs#p6"
    :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches_Ref0_Oblig"
	      ";;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref0"
	      ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p6"
	      "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p6.sw"
	      "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p6.log"
	      "p6: Conjecture match_finding in MatchingObligations#FindMatches_Ref0_Oblig is Proved! *"
	      (:optional "")
	      (:optional "")
	      ))
 
   ("Tutorial: swl find-matches" 
    :swl "/UserDoc/tutorial/example/MatchingRefinements#FindMatches $TESTDIR/find-matches"
    :output '(";;; Generating lisp file $TESTDIR/find-matches.lisp"
              "WARNING: Non-constructive def for List-Spec::lengthOfListFunction"
	      "WARNING: Non-constructive def for List-Spec::definedOnInitialSegmentOfLength-2"
	      "WARNING: Non-constructive def for Function-Spec::inverse-1-1"
	      "WARNING: Non-constructive def for Function-Spec::surjective?"
	      "WARNING: Non-constructive def for Function-Spec::injective?"
	      "")
    :files '("$TESTDIR/find-matches.lisp"))

   ("Tutorial: Load find-matches.lisp" 
    :lisp "(let (#+allegro excl:*redefinition-warnings*)
           (Specware::compile-and-load-lisp-file \"$TESTDIR/find-matches.lisp\"))")

   ("Tutorial: swll MatchingTest#Test" 
    :swll "/UserDoc/tutorial/example/MatchingTest#Test"
    :output '(";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingTest#Test"
	      ";;; Generating lisp file /tmp*/lgen_lisp_tmp.lisp"
	      (:optional "")
	      (:optional "")
	      ))

;; As of version 1.56 for Interpreter.sw, there is a new syntax for Constructor that includes types.
;; Since these include position fields which vary from user to user, it is hard to construct an 
;; appropriate structure to match against.
;; Perhaps we could run some more abstract equality test...
;; At any rate, the test below somewhat obviates the need for this test...
;;
;;   ("Tutorial: test_find_matches" 
;;    :swe "test_find_matches(\"**V*ALN**EC*E*S\",
;;                          [\"CERAMIC\", \"CHESS\", \"DECREE\", \"FOOTMAN\",
;;                           \"INLET\", \"MOLOCH\", \"OCELOT\", \"PROFUSE\",
;;                           \"RESIDE\", \"REVEAL\", \"SECRET\", \"SODIUM\",
;;                           \"SPECIES\", \"VESTIGE\", \"WALNUT\", \"YOGURT\"])"
;;    :swe-spec "$SPECWARE/UserDoc/tutorial/example/MatchingTest#Test"
;;    :value '(:|Constructor| "Cons" :|RecordVal|
;;	      ("1" :|RecordVal| ("position" :|Int| . 3) ("word" :|String| . "WALNUT"))
;;	      ("2" :|Constructor| "Cons" :|RecordVal|
;;	       ("1" :|RecordVal| ("position" :|Int| . 7) ("word" :|String| . "SPECIES"))
;;	       ("2" :|Constructor| "Cons" :|RecordVal|
;;		("1" :|RecordVal| ("position" :|Int| . 8) ("word" :|String| . "SECRET"))
;;		("2" :|Constructor| "Cons" :|RecordVal|
;;		 ("1" :|RecordVal| ("position" :|Int| . 0) ("word" :|String| . "REVEAL"))
;;		 ("2" :|Constructor| "Cons" :|RecordVal|
;;		  ("1" :|RecordVal| ("position" :|Int| . 8) ("word" :|String| . "DECREE"))
;;		  ("2" :|Constructor| "Cons" :|RecordVal|
;;		   ("1" :|RecordVal| ("position" :|Int| . 10) ("word" :|String| . "CHESS"))
;;		   ("2" :|Constant| . "Nil"))))))))

   ("Tutorial: test_find_matches="
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
    :value '(:|Bool| . t))

   )
  )
