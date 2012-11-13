%%  MatchingProofs.sw

 %% obligations from MatchingSpecs.sw :

p2A =  prove word_matches_at?_Obligation_subtype       in MatchingObligations#WordMatching_Oblig
p2B =  prove word_matches_at?_Obligation_subtype0      in MatchingObligations#WordMatching_Oblig

 %% obligations from MatchingRefinements.sw :

p3A =  prove word_matches_at?_Obligation_subtype       in MatchingObligations#WordMatching0_Oblig
p3B =  prove word_matches_at?_Obligation_subtype0      in MatchingObligations#WordMatching0_Oblig
p3C =  prove word_matches_aux?_Obligation_subtype      in MatchingObligations#WordMatching0_Oblig
p3D =  prove word_matches_aux?_Obligation_uniqueness  in MatchingObligations#WordMatching0_Oblig      % fails

p4A =  prove word_matches_at?_def                      in MatchingObligations#WordMatching_Ref0_Oblig  % fails

p5B =  prove find_matches_aux_Obligation_subtype       in MatchingObligations#FindMatches0_Oblig
p5C =  prove find_matches_aux_Obligation_uniqueness   in MatchingObligations#FindMatches0_Oblig       % fails

p6  =  prove match_finding                             in MatchingObligations#FindMatches_Ref0_Oblig   % fails

