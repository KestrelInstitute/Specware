%%  MatchingProofs.sw

 %% obligations from MatchingSpecs.sw :

p1A =  prove symb_matches?_Obligation_exhaustive       in MatchingObligations#SymbolMatching_Oblig

p2A =  prove word_matches_at?_Obligation_subsort       in MatchingObligations#WordMatching_Oblig
p2B =  prove word_matches_at?_Obligation_subsort0      in MatchingObligations#WordMatching_Oblig

 %% obligations from MatchingRefinements.sw :

p3A =  prove word_matches_at?_Obligation_subsort       in MatchingObligations#WordMatching0_Oblig
p3B =  prove word_matches_at?_Obligation_subsort0      in MatchingObligations#WordMatching0_Oblig
p3C =  prove word_matches_aux?_Obligation_subsort      in MatchingObligations#WordMatching0_Oblig
p3D =  prove word_matches_aux?_Obligation_termination  in MatchingObligations#WordMatching0_Oblig      % fails
p3E =  prove word_matches_aux?_Obligation_exhaustive   in MatchingObligations#WordMatching0_Oblig     

p4A =  prove word_matches_at?_def                      in MatchingObligations#WordMatching_Ref0_Oblig  % fails

p5A =  prove find_matches_Obligation_exhaustive        in MatchingObligations#FindMatches0_Oblig
p5B =  prove find_matches_aux_Obligation_subsort       in MatchingObligations#FindMatches0_Oblig
p5C =  prove find_matches_aux_Obligation_termination   in MatchingObligations#FindMatches0_Oblig       % fails

p6  =  prove match_finding                             in MatchingObligations#FindMatches_Ref0_Oblig   % fails

