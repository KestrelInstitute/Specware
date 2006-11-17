%% increasing the time limit to 30 seconds doesn't seem to help

 p1  = prove symb_matches?_Obligation_exhaustive      in MatchingObligations#SymbolMatching_Oblig     % options "(run-time-limit 30)"

 %% One of the word_matches_at?_Obligation is no longer generated because it is trivially true

 p2  = prove word_matches_at?_Obligation_subsort      in MatchingObligations#WordMatching_Oblig       % options "(run-time-limit 30)"
 p3  = prove word_matches_at?_Obligation_subsort0     in MatchingObligations#WordMatching_Oblig       % options "(run-time-limit 30)"

 p5  = prove word_matches_at?_Obligation_subsort      in MatchingObligations#WordMatching0_Oblig      % options "(run-time-limit 30)"
 p6  = prove word_matches_at?_Obligation_subsort0     in MatchingObligations#WordMatching0_Oblig      % options "(run-time-limit 30)"
%p7  = prove word_matches_at?_Obligation_subsort1     in MatchingObligations#WordMatching0_Oblig      % options "(run-time-limit 30)"
 p8  = prove word_matches_aux?_Obligation_subsort     in MatchingObligations#WordMatching0_Oblig      % options "(run-time-limit 30)"
 p9  = prove word_matches_aux?_Obligation_termination in MatchingObligations#WordMatching0_Oblig      % options "(run-time-limit 30)"
 p10 = prove word_matches_aux?_Obligation_exhaustive  in MatchingObligations#WordMatching0_Oblig      % options "(run-time-limit 30)"

% currently missing from generated obligations:
%p11 = prove ...                                      in MatchingObligations#WordMatching_Ref0_Oblig  % options "(run-time-limit 30)"

 p12 = prove find_matches_Obligation_exhaustive       in MatchingObligations#FindMatches0_Oblig       % options "(run-time-limit 30)"
 p13 = prove find_matches_aux_Obligation_subsort      in MatchingObligations#FindMatches0_Oblig       % options "(run-time-limit 30)"
 p14 = prove find_matches_aux_Obligation_termination  in MatchingObligations#FindMatches0_Oblig       % options "(run-time-limit 30)"

 p15 = prove match_finding                            in MatchingObligations#FindMatches_Ref0_Oblig   % options "(run-time-limit 30)"
  