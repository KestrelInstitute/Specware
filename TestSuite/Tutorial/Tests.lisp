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
	    ""))

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
	    ""))

 ("Tutorial: MatchingProofs p1"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p1"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#SymbolMatching_Oblig"
	    ";;; Elaborating spec at $SPECWARE/Library/Base/WFO"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p1"
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
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
	    (:optional ";; ensure-directories-exist: creating $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p1.log")
	    (:optional ";; Directory $SPECWARE/UserDoc/tutorial/example/Snark/ does not exist, will create.")
	    (:optional ";; Directory $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/ does not exist, will create.")
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p1.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p1.log"
	    "p1: Conjecture symb_matches?_Obligation in MatchingObligations#SymbolMatching_Oblig is Proved! using Snark."
	    ""))

 ("Tutorial: MatchingProofs p2" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p2"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching_Oblig"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p2"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2.log"
	    "p2: Conjecture word_matches_at?_Obligation in MatchingObligations#WordMatching_Oblig is Proved! using simple inequality reasoning."
	    ""))

 ("Tutorial: MatchingProofs p3" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p3"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3.log"
	    "p3: Conjecture word_matches_at?_Obligation0 in MatchingObligations#WordMatching_Oblig is Proved! using simple inequality reasoning."
	    ""))
      
 ("Tutorial: MatchingProofs p5"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p5"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p5"
	    ";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching0_Oblig"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5.log"
	    "p5: Conjecture word_matches_at?_Obligation in MatchingObligations#WordMatching0_Oblig is Proved! using simple inequality reasoning."
	    ""))

 ("Tutorial: MatchingProofs p6" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p6"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p6"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p6.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p6.log"
	    "p6: Conjecture word_matches_at?_Obligation0 in MatchingObligations#WordMatching0_Oblig is Proved! using simple inequality reasoning."
	    ""))

 ("Tutorial: MatchingProofs p7" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p7"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p7"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p7.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p7.log"
	    "p7: Conjecture word_matches_at?_Obligation1 in MatchingObligations#WordMatching0_Oblig is NOT proved using Snark."
	    ""))

 ("Tutorial: MatchingProofs p8" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p8"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p8"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p8.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p8.log"
	    "p8: Conjecture word_matches_aux?_Obligation in MatchingObligations#WordMatching0_Oblig is NOT proved using Snark."
	    ""))

 ("Tutorial: MatchingProofs p9" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p9"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p9"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p9.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p9.log"
	    "p9: Conjecture word_matches_aux?_Obligation0 in MatchingObligations#WordMatching0_Oblig is NOT Proved using Snark."
	    ""))

 ("Tutorial: MatchingProofs p10"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p10"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p10"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p10.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p10.log"
	    "p10: Conjecture word_matches_aux?_Obligation1 in MatchingObligations#WordMatching0_Oblig is Proved! using Snark."
	    ""))

 ("Tutorial: MatchingProofs p12"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p12"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches0_Oblig"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p12"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p12.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p12.log"
	    "p12: Conjecture find_matches_Obligation in MatchingObligations#FindMatches0_Oblig is Proved! using Snark."
	    ""))

 ("Tutorial: MatchingProofs p13"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p13"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p13"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p13.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p13.log"
	    "p13: Conjecture find_matches_aux_Obligation in MatchingObligations#FindMatches0_Oblig is Proved! using simple inequality reasoning."
	    ""))

 ("Tutorial: MatchingProofs p14"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p14"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p14"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p14.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p14.log"
	    "p14: Conjecture find_matches_aux_Obligation0 in MatchingObligations#FindMatches0_Oblig is NOT Proved using Snark."
	    ""))
      
 ("Tutorial: MatchingProofs p15"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p15"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches_Ref0_Oblig"
	    ";;; Elaborating spec-morphism at $SPECWARE/UserDoc/tutorial/example/MatchingRefinements#FindMatches_Ref0"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p15"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p15.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p15.log"
	    "p15: Conjecture match_finding in MatchingObligations#FindMatches_Ref0_Oblig is NOT Proved using Snark."
	    ""))
      	    
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
	    ""))

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
