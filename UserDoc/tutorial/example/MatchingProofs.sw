%%  MatchingProofs.sw

 %%  do not use prover base;
 %%  call 
 %%    prwb nil 
 %%  in specware shell
 %%  or call (cl-user::swprb nil) in Tests.lisp

 %% obligations from MatchingSpecs.sw :

 p1A =  prove symb_matches?_Obligation_exhaustive       in MatchingObligations#SymbolMatching_Oblig

 p2A =  prove word_matches_at?_Obligation_subsort       in MatchingObligations#WordMatching_Oblig
 p2B =  prove word_matches_at?_Obligation_subsort0      in MatchingObligations#WordMatching_Oblig

 %% obligations from MatchingRefinements.sw :

 p3A =  prove word_matches_at?_Obligation_subsort       in MatchingObligations#WordMatching0_Oblig        options use_support
 p3B =  prove word_matches_at?_Obligation_subsort0      in MatchingObligations#WordMatching0_Oblig        options use_support_list
 p3C =  prove word_matches_aux?_Obligation_subsort      in MatchingObligations#WordMatching0_Oblig        options use_support_list
 p3D =  prove word_matches_aux?_Obligation_termination  in MatchingObligations#WordMatching0_Oblig      % options "(run-time-limit 20)" % fails
 p3E =  prove word_matches_aux?_Obligation_exhaustive   in MatchingObligations#WordMatching0_Oblig     

 p4A =  prove word_matches_at?_def                      in MatchingObligations#WordMatching_Ref0_Oblig  % options "(run-time-limit 20)" % fails

 p5A =  prove find_matches_Obligation_exhaustive        in MatchingObligations#FindMatches0_Oblig
 p5B =  prove find_matches_aux_Obligation_subsort       in MatchingObligations#FindMatches0_Oblig
 p5C =  prove find_matches_aux_Obligation_termination   in MatchingObligations#FindMatches0_Oblig       % options "(run-time-limit 20)" % fails

 p6A =  prove match_finding_lr1                         in MatchingObligations#FindMatches_Ref0_Oblig   % options "(run-time-limit 20)" % fails
 p6B =  prove match_finding_lr2                         in MatchingObligations#FindMatches_Ref0_Oblig   % options "(run-time-limit 20)" % fails
 p6C =  prove match_finding_lr3                         in MatchingObligations#FindMatches_Ref0_Oblig   % options "(run-time-limit 20)" % fails
 p6D =  prove match_finding_rl                          in MatchingObligations#FindMatches_Ref0_Oblig   % options "(run-time-limit 20)" % fails

