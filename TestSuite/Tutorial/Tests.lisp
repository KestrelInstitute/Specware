(cl-user::sw-init)

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
  :swprb T
  :output '((:optional "T") 
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p1A"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p1A"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#SymbolMatching_Oblig"
	    (:optional ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#SymbolMatching")
	    (:optional ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Symbols")
	    ";;; Elaborating spec at $SPECWARE/Library/Base/WFO"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p1A"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Option"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/String"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/System"
	    ";;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite"
	    (:optional ";; ensure-directories-exist: creating $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p1A.log")
	    (:optional ";; Directory $SPECWARE/UserDoc/tutorial/example/Snark/ does not exist, will create.")
	    (:optional ";; Directory $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/ does not exist, will create.")
 	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p1A.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p1A.log"
	    "p1A: Conjecture symb_matches?_Obligation_exhaustive in MatchingObligations#SymbolMatching_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p2A" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p2A"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching_Oblig"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p2A"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2A.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2A.log"
	    "p2A: Conjecture word_matches_at?_Obligation_subsort in MatchingObligations#WordMatching_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p2B" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p2B"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p2B"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2B.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2B.log"
	    "p2B: Conjecture word_matches_at?_Obligation_subsort0 in MatchingObligations#WordMatching_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))
      
 ("Tutorial: MatchingProofs p3A"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p3A"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching0_Oblig"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3A"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3A.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3A.log"
	    "p3A: Conjecture word_matches_at?_Obligation_subsort in MatchingObligations#WordMatching0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p3B" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p3B"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3B"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3B.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3B.log"
	    "p3B: Conjecture word_matches_at?_Obligation_subsort0 in MatchingObligations#WordMatching0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p3C" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p3C"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3C"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3C.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3C.log"
	    ;; Sigh.  "C:" becomes "" in test output processing   
	    "p3 Conjecture word_matches_aux?_Obligation_subsort in MatchingObligations#WordMatching0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ; fails
 ("Tutorial: MatchingProofs p3D" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p3D"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3D"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3D.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3D.log"
	    "p3D: Conjecture word_matches_aux?_Obligation_termination in MatchingObligations#WordMatching0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p3E"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p3E"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3E"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3E.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3E.log"
	    "p3E: Conjecture word_matches_aux?_Obligation_exhaustive in MatchingObligations#WordMatching0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ; fails
 ("Tutorial: MatchingProofs p4A"
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

 ("Tutorial: MatchingProofs p5A"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p5A"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches0_Oblig"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p5A"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5A.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5A.log"
	    "p5A: Conjecture find_matches_Obligation_exhaustive in MatchingObligations#FindMatches0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p5B"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p5B"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p5B"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5B.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5B.log"
	    "p5B: Conjecture find_matches_aux_Obligation_subsort in MatchingObligations#FindMatches0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ; fails
 ("Tutorial: MatchingProofs p5C"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p5C"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p5C"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5C.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5C.log"
	    ;; Sigh.  "C:" becomes "" in test output processing   
	    "p5 Conjecture find_matches_aux_Obligation_termination in MatchingObligations#FindMatches0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))
      
 ; fails
 ("Tutorial: MatchingProofs p6"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p6"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches_Ref0_Oblig"
	    ";;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref0"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p6"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p6.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p6.log"
	    "p6: Conjecture match_finding_lr1 in MatchingObligations#FindMatches_Ref0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))
 
 ("Tutorial: swl find-matches" 
  :swl "/UserDoc/tutorial/example/MatchingRefinements#FindMatches $TESTDIR/find-matches"
  :output '(";;; Generating lisp file $TESTDIR/find-matches.lisp"
	    "")
  :files '("$TESTDIR/find-matches.lisp"))

 ("Tutorial: Load find-matches.lisp" 
  :lisp "(let (#+allegro excl:*redefinition-warnings*)
           (specware::compile-and-load-lisp-file \"$TESTDIR/find-matches.lisp\"))")

 ("Tutorial: swll MatchingTest#Test" 
  :swll "/UserDoc/tutorial/example/MatchingTest#Test"
  :output '(";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingTest#Test"
	    ";;; Generating lisp file /tmp/lgen_lisp_tmp.lisp"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: test_find_matches" 
  :swe "test_find_matches(\"**V*ALN**EC*E*S\",
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
  :value '(:|Bool| . T))

 )
