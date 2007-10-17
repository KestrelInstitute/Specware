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

 ("Tutorial: MatchingProofs p1A (exhaustive)"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p1A"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#SymbolMatching_Oblig"
	    (:optional ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#SymbolMatching")
	    (:optional ";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingSpecs#Symbols")
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
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
	    (:optional "creating directory: $SPECWARE/UserDoc/tutorial/example/Snark/")
	    (:optional ";; Directory $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/ does not exist, will create.")
	    (:optional "creating directory: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/")
 	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p1A.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p1A.log"
	    "p1A: Conjecture symb_matches?_Obligation_exhaustive in MatchingObligations#SymbolMatching_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p2A (subtype)" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p2A"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching_Oblig"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p2A"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2A.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2A.log"
	    "p2A: Conjecture word_matches_at?_Obligation_subsort in MatchingObligations#WordMatching_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p2B (subtype)" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p2B"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p2B"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2B.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p2B.log"
	    "p2B: Conjecture word_matches_at?_Obligation_subsort0 in MatchingObligations#WordMatching_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))
      
 ("Tutorial: MatchingProofs p3A (subtype)"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p3A"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#WordMatching0_Oblig"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3A"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3A.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3A.log"
	    "p3A: Conjecture word_matches_at?_Obligation_subsort in MatchingObligations#WordMatching0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p3B (subtype)" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p3B"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3B"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3B.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3B.log"
	    "p3B: Conjecture word_matches_at?_Obligation_subsort0 in MatchingObligations#WordMatching0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p3C (subtype)" 
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
 ("Tutorial: MatchingProofs p3D (termination)" 
  :sw "/UserDoc/tutorial/example/MatchingProofs#p3D"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3D"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3D.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3D.log"
	    "p3D: Conjecture word_matches_aux?_Obligation_termination in MatchingObligations#WordMatching0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p3E (exhaustive)"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p3E"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p3E"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3E.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p3E.log"
	    "p3E: Conjecture word_matches_aux?_Obligation_exhaustive in MatchingObligations#WordMatching0_Oblig is Proved! *"
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

 ("Tutorial: MatchingProofs p5A (exhausive)"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p5A"
  :output '(";;; Elaborating obligator at $SPECWARE/UserDoc/tutorial/example/MatchingObligations#FindMatches0_Oblig"
	    ";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p5A"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5A.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5A.log"
	    "p5A: Conjecture find_matches_Obligation_exhaustive in MatchingObligations#FindMatches0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ("Tutorial: MatchingProofs p5B (subtype)"
  :sw "/UserDoc/tutorial/example/MatchingProofs#p5B"
  :output '(";;; Elaborating proof-term at $SPECWARE/UserDoc/tutorial/example/MatchingProofs#p5B"
	    "    Expanded spec file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5B.sw"
	    "    Snark Log file: $SPECWARE/UserDoc/tutorial/example/Snark/MatchingProofs/p5B.log"
	    "p5B: Conjecture find_matches_aux_Obligation_subsort in MatchingObligations#FindMatches0_Oblig is Proved! *"
	    (:optional "")
	    (:optional "")
	    ))

 ; fails
 ("Tutorial: MatchingProofs p5C (termination)"
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
	    (:optional
	     "WARNING: Non-constructive def for STRING-SPE:explode"
	     "WARNING: Non-constructive def for FUNCTIONS::injective?"
	     "WARNING: Non-constructive def for FUNCTIONS::surjective?"
	     "WARNING: Non-constructive def for FUNCTIONS::inverse-1-1"
	     "WARNING: Non-constructive def for INTEGER-SPE:pred"
	     "WARNING: Non-constructive def for INTEGER-SPE:positive?"
	     "WARNING: Non-constructive def for INTEGERAUX::|!-|"
	     "WARNING: Non-constructive def for INTEGER-SPE:+-2"
	     "WARNING: Non-constructive def for INTEGER-SPE:*-2"
	     "WARNING: Non-constructive def for INTEGER-SPE:div-2"
	     "WARNING: Non-constructive def for INTEGER-SPE:divides-2"
	     "WARNING: Non-constructive def for INTEGER-SPE:gcd-2"
	     "WARNING: Non-constructive def for INTEGER-SPE:lcm-2"
	     "WARNING: Non-constructive def for CHAR-SPE:ord"
	     )
	    (:optional
	     ";;; Suppressing generated def for BOOLEAN-SPE:show"
	     ";;; Suppressing generated def for CHAR-SPE:ord"
	     ";;; Suppressing generated def for INTEGERAUX::|!-|"
	     ";;; Suppressing generated def for INTEGER-SPE:+-2"
	     ";;; Suppressing generated def for INTEGER-SPE:--2"
	     ";;; Suppressing generated def for INTEGER-SPE:positive?"
	     ";;; Suppressing generated def for INTEGER-SPE:<-2"
	     ";;; Suppressing generated def for INTEGER-SPE:<=-2"
	     ";;; Suppressing generated def for CHAR-SPE:isLowerCase"
	     ";;; Suppressing generated def for CHAR-SPE:isUpperCase"
	     ";;; Suppressing generated def for CHAR-SPE:isAlpha"
	     ";;; Suppressing generated def for CHAR-SPE:isNum"
	     ";;; Suppressing generated def for CHAR-SPE:isAlphaNum"
	     ";;; Suppressing generated def for CHAR-SPE:isAscii"
	     ";;; Suppressing generated def for CHAR-SPE:show"
	     ";;; Suppressing generated def for CHAR-SPE:toLowerCase"
	     ";;; Suppressing generated def for CHAR-SPE:toString"
	     ";;; Suppressing generated def for CHAR-SPE:toUpperCase"
	     ";;; Suppressing generated def for INTEGER-SPE:*-2"
	     ";;; Suppressing generated def for INTEGER-SPE:div-2"
	     ";;; Suppressing generated def for INTEGER-SPE:div"
	     ";;; Suppressing generated def for INTEGER-SPE:divides-2"
	     ";;; Suppressing generated def for INTEGER-SPE:divides"
	     ";;; Suppressing generated def for INTEGER-SPE:gcd-2"
	     ";;; Suppressing generated def for STRING-SPE:explode"
	     ";;; Suppressing generated def for INTEGER-SPE:rem-2"
	     ";;; Suppressing generated def for STRING-SPE:concat-2"
	     ";;; Suppressing generated def for STRING-SPE:^-2"
	     ";;; Suppressing generated def for NAT-SPE:natToString"
	     ";;; Suppressing generated def for INTEGER-SPE:intToString"
	     ";;; Suppressing generated def for INTEGER-SPE:lcm-2"
	     ";;; Suppressing generated def for INTEGER-SPE:multipleOf-2"
	     ";;; Suppressing generated def for INTEGER-SPE:multipleOf"
	     ";;; Suppressing generated def for INTEGER-SPE:pred"
	     ";;; Suppressing generated def for STRING-SPE:|!length|"
	     ";;; Suppressing generated def for STRING-SPE:substring-3"
	     ";;; Suppressing generated def for NAT-SPE:stringToNat"
	     ";;; Suppressing generated def for INTEGER-SPE:stringToInt"
	     ";;; Suppressing generated def for INTEGER-SPE:toString"
	     ";;; Suppressing generated def for INTEGER-SPE:|!*|"
	     ";;; Suppressing generated def for INTEGER-SPE:|!+|"
	     ";;; Suppressing generated def for INTEGER-SPE:|!-|"
	     ";;; Suppressing generated def for INTEGER-SPE:|!<=|"
	     ";;; Suppressing generated def for INTEGER-SPE:|!<|"
	     ";;; Suppressing generated def for INTEGER-SPE:|!gcd|"
	     ";;; Suppressing generated def for INTEGER-SPE:|!lcm|"
	     ";;; Suppressing generated def for INTEGER-SPE:|!rem|"
	     ";;; Suppressing generated def for NAT-SPE:toString"
	     ";;; Suppressing generated def for STRING-SPE:++-2"
	     ";;; Suppressing generated def for STRING-SPE:compare-2"
	     ";;; Suppressing generated def for STRING-SPE:<-2"
	     ";;; Suppressing generated def for STRING-SPE:<=-2"
	     ";;; Suppressing generated def for STRING-SPE:^"
	     ";;; Suppressing generated def for STRING-SPE:all-1-1"
	     ";;; Suppressing generated def for STRING-SPE:all"
	     ";;; Suppressing generated def for STRING-SPE:compare"
	     ";;; Suppressing generated def for STRING-SPE:concat"
	     ";;; Suppressing generated def for STRING-SPE:concatList"
	     ";;; Suppressing generated def for STRING-SPE:exists-1-1"
	     ";;; Suppressing generated def for STRING-SPE:leq-2"
	     ";;; Suppressing generated def for STRING-SPE:leq"
	     ";;; Suppressing generated def for STRING-SPE:lt-2"
	     ";;; Suppressing generated def for STRING-SPE:lt"
	     ";;; Suppressing generated def for STRING-SPE:map-1-1"
	     ";;; Suppressing generated def for STRING-SPE:newline"
	     ";;; Suppressing generated def for STRING-SPE:sub-2"
	     ";;; Suppressing generated def for STRING-SPE:sub"
	     ";;; Suppressing generated def for STRING-SPE:substring"
	     ";;; Suppressing generated def for STRING-SPE:toScreen"
	     ";;; Suppressing generated def for STRING-SPE:translate-1-1"
	     ";;; Suppressing generated def for STRING-SPE:translate"
	     ";;; Suppressing generated def for STRING-SPE:writeLine"
	     ";;; Suppressing generated def for STRING-SPE:|!<=|"
	     ";;; Suppressing generated def for STRING-SPE:|!<|"
	     ";;; Suppressing generated def for STRING-SPE:|!exists|"
	     ";;; Suppressing generated def for STRING-SPE:|!map|"
	     )
	    "")
  :files '("$TESTDIR/find-matches.lisp"))

 ("Tutorial: Load find-matches.lisp" 
  :lisp "(let (#+allegro excl:*redefinition-warnings*)
           (specware::compile-and-load-lisp-file \"$TESTDIR/find-matches.lisp\"))")

 ("Tutorial: swll MatchingTest#Test" 
  :swll "/UserDoc/tutorial/example/MatchingTest#Test"
  :output '(";;; Elaborating spec at $SPECWARE/UserDoc/tutorial/example/MatchingTest#Test"
	    ";;; Generating lisp file /tmp*/lgen_lisp_tmp.lisp"
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
