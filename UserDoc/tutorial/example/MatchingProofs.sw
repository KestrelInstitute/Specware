% only p2 gets proved:

p1 = prove symb_matches?_Obligation in MatchingObligations#SymbolMatching_Oblig

p2 = prove word_matches_at?_Obligation  in MatchingObligations#WordMatching_Oblig
p3 = prove word_matches_at?_Obligation0 in MatchingObligations#WordMatching_Oblig
p4 = prove word_matches_at?_Obligation1 in MatchingObligations#WordMatching_Oblig

p5  = prove word_matches_at?_Obligation   in MatchingObligations#WordMatching0_Oblig
p6  = prove word_matches_at?_Obligation0  in MatchingObligations#WordMatching0_Oblig
p7  = prove word_matches_at?_Obligation1  in MatchingObligations#WordMatching0_Oblig
p8  = prove word_matches_aux?_Obligation  in MatchingObligations#WordMatching0_Oblig
p9  = prove word_matches_aux?_Obligation0 in MatchingObligations#WordMatching0_Oblig
p10 = prove word_matches_aux?_Obligation1 in MatchingObligations#WordMatching0_Oblig

% currently missing from generated obligations:
% p11 = prove ... in MatchingObligations#WordMatching_Ref0_Oblig

p12 = prove find_matches_Obligation      in MatchingObligations#FindMatches0_Oblig
p13 = prove find_matches_aux_Obligation  in MatchingObligations#FindMatches0_Oblig
p14 = prove find_matches_aux_Obligation0 in MatchingObligations#FindMatches0_Oblig

p15 = prove match_finding in MatchingObligations#FindMatches_Ref0_Oblig
