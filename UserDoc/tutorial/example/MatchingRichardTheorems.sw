
%% execute 
%%%   prwb nil   
%%% do not use ProverBase


MatchingRichardSpec = spec


import MatchingObligations#WordMatching0_Oblig




%  def use_support_list = 
%    "(use-resolution t)
%    (use-paramodulation t)
%    (use-hyperresolution nil)
%    (use-negative-hyperresolution nil)
%    (run-time-limit 20)
%    (assert-supported nil)
%    (use-term-ordering :rpo)
%    (use-default-ordering nil)
%    (use-literal-ordering-with-resolution 'literal-ordering-a)
%    (use-literal-ordering-with-paramodulation 'literal-ordering-a)
%    (use-literal-ordering-with-hyperresolution 'literal-ordering-p)
%    (use-literal-ordering-with-negative-hyperresolution 'literal-ordering-n)
%    (declare-predicate-symbol '>= 2 :sort '(boolean number number)
%    :alias 'gte)
%    (declare-function '+ :any 
%     :commutative t :associative t)
%    (declare-function '- 2 :alias 'minusBinary)
%    (declare-ordering-greaterp 'minusBinary '+ '|Nat.one| '1 '|Nat.zero| '0)   ;;  
%    (declare-ordering-greaterp 'snark::< 'snark::=<)
%    (declare-ordering-greaterp 'snark::> 'snark::=<)
%    (declare-ordering-greaterp 'snark::gte  'snark::=<)
%    (declare-ordering-greaterp 'snark::|List.length_Symbol| '+)
%    (declare-ordering-greaterp 'snark::|List.length_Symbol| '1)
%    (declare-ordering-greaterp 'snark::|List.length_Option_Symbol| '+)
%    (declare-ordering-greaterp 'snark::|List.length_Option_Symbol| '1)
%    (declare-ordering-greaterp 'snark::|embed_Cons| 'snark::|List.length|)
%    (declare-ordering-greaterp 'snark::|embed_Cons| '+)
%    (declare-ordering-greaterp 'snark::|embed_Cons| '1)
%    (declare-ordering-greaterp 'snark::|List.cons| 'snark::|embed_Cons|)"




endspec





p1 = prove symb_matches?_Obligation_exhaustive in MatchingObligations#SymbolMatching_Oblig


%% One of the word_matches_at?_Obligation is no longer generated because it is trivially true
p2 = prove word_matches_at?_Obligation_subsort  in MatchingObligations#WordMatching_Oblig
p3 = prove word_matches_at?_Obligation_subsort0 in MatchingObligations#WordMatching_Oblig

p5  = prove word_matches_at?_Obligation_subsort   in 
MatchingObligations#WordMatching_Oblig %%MatchingRichardSpec
%%options use_support




p6  = prove word_matches_at?_Obligation_subsort0  in 
MatchingObligations#WordMatching0_Oblig %MatchingRichardSpec
options use_support_list

% name not in spec
%p7  = prove word_matches_at?_Obligation_subsort1  
%in MatchingObligations#WordMatching0_Oblig
%options use_support_list

p8  = prove word_matches_aux?_Obligation_subsort  in 
MatchingObligations#WordMatching0_Oblig
options use_support_list
(*  %% termination proof
p9  = prove word_matches_aux?_Obligation_termination in MatchingRichardSpec
options use_support_list
*)


p10 = prove word_matches_aux?_Obligation_exhaustive 
in MatchingObligations#WordMatching0_Oblig
options use_support_list

% currently missing from generated obligations:
% p11 = prove ... in MatchingObligations#WordMatching_Ref0_Oblig

p12 = prove find_matches_Obligation_exhaustive    %% 
in MatchingObligations#FindMatches0_Oblig 
options use_support_list

p13 = prove find_matches_aux_Obligation_subsort  %% 
in MatchingObligations#FindMatches0_Oblig
options use_support_list
(*  %% termination proof
p14 = prove find_matches_aux_Obligation_termination %% 
in MatchingObligations#FindMatches0_Oblig
options use_support_list
*)

%% remaining are not proved---contain symbols with no axioms.
p15 = prove match_finding_lr1
in MatchingObligations#FindMatches_Ref0_Oblig
options use_support_list

p16 = prove match_finding_lr2 %% 
in MatchingObligations#FindMatches_Ref0_Oblig
options use_support_list

p17 = prove match_finding_lr3 %% 
in MatchingObligations#FindMatches_Ref0_Oblig
options use_support_list

p18 = prove match_finding_rl %% 
in MatchingObligations#FindMatches_Ref0_Oblig
options use_support_list

%% uncomment for consistency check
 

%contradictory =
%prove contradictory in contradictorySpec
%options 
%"(use-resolution t)
%    (use-paramodulation t)
%    (use-factoring)
%    (use-literal-ordering-with-resolution nil)
%    (use-literal-ordering-with-paramodulation nil)
%    (use-term-ordering nil)
%    (use-default-ordering nil)
%    (assert-supported t)
%    (run-time-limit 600)
%    (use-ac-connectives)
%    (use-code-for-numbers nil)
%    (use-term-ordering :rpo)
%    (use-default-ordering nil)
%    (use-literal-ordering-with-resolution 'literal-ordering-a)
%    (use-literal-ordering-with-paramodulation 'literal-ordering-a)
%    (use-literal-ordering-with-hyperresolution 'literal-ordering-p)
%    (use-literal-ordering-with-negative-hyperresolution 'literal-ordering-n)
%    (declare-predicate-symbol '>= 2 :sort '(boolean number number)
%    :alias 'gte)
%    (declare-function '+ :any 
%     :commutative t :associative t)
%    (declare-ordering-greaterp '+ '0)
%    (declare-ordering-greaterp 'snark::< 'snark::=<)
%    (declare-ordering-greaterp 'snark::> 'snark::=<)
%    (declare-ordering-greaterp 'snark::gte  'snark::=<)
%    (declare-ordering-greaterp 'snark::|List.length_Symbol| '+)
%    (declare-ordering-greaterp 'snark::|List.length_Symbol| '1)
%    (declare-ordering-greaterp 'snark::|List.length_Option_Symbol| '+)
%    (declare-ordering-greaterp 'snark::|List.length_Option_Symbol| '1)
%    (declare-ordering-greaterp 'snark::|embed_Cons| 'snark::|List.length|)
%    (declare-ordering-greaterp 'snark::|embed_Cons| '+)
%    (declare-ordering-greaterp 'snark::|embed_Cons| '1)
%    (declare-ordering-greaterp 'snark::|List.cons| 'snark::|embed_Cons|)"

