p1 = prove symb_matches?_Obligation in MatchingObligations#SymbolMatching_Oblig
(*
p2 = prove word_matching in
     MatchingObligations#WordMatching_Ref0_Oblig
       [morphism MatchingSpecs#SymbolMatching ->
                 MatchingObligations#SymbolMatching_Oblig {}]
     using symb_matches?
*)
p3 = prove find_matches_aux_Obligation in MatchingObligations#FindMatches0_Oblig
p4 = prove word_matching_Obligation in MatchingObligations#FindMatches0_Oblig
p5 = prove word_matching_Obligation0 in MatchingObligations#FindMatches0_Oblig
p6 = prove word_matching_Obligation1 in MatchingObligations#FindMatches0_Oblig
