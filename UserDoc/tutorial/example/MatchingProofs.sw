
p1 = prove symb_matches?_Obligation_fn_precond in MatchingObligations#SymbolMatching_Oblig

%% One of the word_matches_at?_Obligation is no longer generated because it is trivially true
p2 = prove word_matches_at?_Obligation_subsort  in MatchingObligations#WordMatching_Oblig
p3 = prove word_matches_at?_Obligation_subsort0 in MatchingObligations#WordMatching_Oblig

p5  = prove word_matches_at?_Obligation_subsort   in MatchingObligations#WordMatching0_Oblig
p6  = prove word_matches_at?_Obligation_subsort0  in MatchingObligations#WordMatching0_Oblig
%p7  = prove word_matches_at?_Obligation_subsort1  in MatchingObligations#WordMatching0_Oblig
p8  = prove word_matches_aux?_Obligation_subsort  in MatchingObligations#WordMatching0_Oblig
p9  = prove word_matches_aux?_Obligation_termination in MatchingObligations#WordMatching0_Oblig
p10 = prove word_matches_aux?_Obligation_fn_precond in MatchingObligations#WordMatching0_Oblig

% currently missing from generated obligations:
% p11 = prove ... in MatchingObligations#WordMatching_Ref0_Oblig

p12 = prove find_matches_Obligation_fn_precond   in MatchingObligations#FindMatches0_Oblig
p13 = prove find_matches_aux_Obligation_subsort  in MatchingObligations#FindMatches0_Oblig
p14 = prove find_matches_aux_Obligation_termination in MatchingObligations#FindMatches0_Oblig

p15 = prove match_finding in MatchingObligations#FindMatches_Ref0_Oblig
