%%  MatchingProofs.sw
%do not use prover base;
%call 
%  prwb nil 
%in specware shell

 p1  = prove symb_matches?_Obligation_exhaustive      
in MatchingObligations#SymbolMatching_Oblig     

%% One of the word_matches_at?_Obligation is no longer generated because it is trivially true
p2 = prove word_matches_at?_Obligation_subsort  
in MatchingObligations#WordMatching_Oblig

p3 = prove word_matches_at?_Obligation_subsort0 
in MatchingObligations#WordMatching_Oblig

p5  = prove word_matches_at?_Obligation_subsort   
in MatchingObligations#WordMatching0_Oblig
options use_support

p6  = prove word_matches_at?_Obligation_subsort0  
in MatchingObligations#WordMatching0_Oblig
options use_support_list
 
%p7  = prove word_matches_at?_Obligation_subsort1  in MatchingObligations#WordMatching0_Oblig

p8  = prove word_matches_aux?_Obligation_subsort  
in MatchingObligations#WordMatching0_Oblig
options use_support_list

(*  %% termination proof---not attempted
p9  = prove word_matches_aux?_Obligation_termination 
in MatchingObligations#WordMatching0_Oblig
*)

p10 = prove word_matches_aux?_Obligation_exhaustive 
in MatchingObligations#WordMatching0_Oblig

 %% One of the word_matches_at?_Obligation is no longer generated because it is trivially true

% currently missing from generated obligations:
%p11 = prove ...                                      in MatchingObligations#WordMatching_Ref0_Oblig  % options "(run-time-limit 30)"

p12 = prove find_matches_Obligation_exhaustive   
in MatchingObligations#FindMatches0_Oblig

p13 = prove find_matches_aux_Obligation_subsort  
in MatchingObligations#FindMatches0_Oblig

(* %% termination proof---not attempted
p14 = prove find_matches_aux_Obligation_termination in MatchingObligations#FindMatches0_Oblig
*)

(* %% translation to snark introduces undefined function symbol.

p15 = prove match_finding in MatchingObligations#FindMatches_Ref0_Oblig
*)
