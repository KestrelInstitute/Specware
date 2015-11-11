%%% Should directly go to sets as characteristic Maps, i.e. Set a = Map(a, Bool)

%% FIXME: Figure out the story with the proof obligations of this.
%% FIXME: The obligations have the same names as the obligations in SetsAsBags, for which we already have proofs that Specware tries to use but that won't work in this context!
%% add JIRA issue
SetsAsBagMaps = SetsAsBags[BagsAsMaps#M]

%% NOTE: These pragmas overwrite the pragmas with the same names in SetsAsBags:

%% Translated version of the proof in SetsAsBags.sw:
proof Isa set_insert_Obligation_subtype
   apply(simp add: SetsAsBags__no_rep_p_def BagsAsMaps__bag_fold2 BagsAsMaps__bag_insertion)
   apply(auto simp add: SetsAsBags__in_p_def BagsAsMaps__bagin_p_def)
   apply(rule BagsAsMaps__bag_fold_true)
   apply(auto)
   apply(cut_tac f=" (\<lambda>(no_rep_found, x). if \<not> no_rep_found then False else BagsAsMaps__occs (x, s) = 1)" in  BagsAsMaps__bag_fold_true_back)
   apply(auto)
end-proof

%% Translated version of the proof in SetsAsBags.sw:
proof Isa SetsAsBags__empty_set_Obligation_subtype
  apply(simp add: SetsAsBags__no_rep_p_def BagsAsMaps__bag_fold1)
end-proof

%% Translated version of the proof in SetsAsBags.sw (slightly fixed up, since there are more assumptions to discharge):
proof Isa set_insert_new_Obligation_subtype
  apply(rule SetsAsBags__set_insert_Obligation_subtype, assumption+)
end-proof

%% Translated version of the proof in SetsAsBags.sw:
proof Isa e_bsl_fsl_Obligation_subtype
  apply(rule BagsAsMaps__occurrences)
  apply(simp add: SetsAsBags__set_insert_def BagsAsMaps__bag_insertion)
  apply(auto simp add: BagsAsMaps__bagin_of_insert SetsAsBags__in_p_def)
end-proof

%% Translated version of the proof in SetsAsBags.sw (now somewhat changed):
proof Isa e_fsl_bsl_Obligation_subtype
  apply(rule BagsAsMaps__occurrences, auto simp add: SetsAsBags__set_insert_def BagsAsMaps__bag_insertion SetsAsBags__in_p_def BagsAsMaps__bagin_of_insert)
  apply(cases "z=y", auto)
  apply(auto simp add:  BagsAsMaps__Map_P_of_insert)
  apply(cases "z=y", auto simp add: BagsAsMaps__Map_P_of_insert)
  apply(cases "z=y", auto simp add: BagsAsMaps__Map_P_of_insert)
  apply(cases "z=y", auto simp add: BagsAsMaps__Map_P_of_insert BagsAsMaps__bag_insertion_commutativity)
end-proof

proof Isa SetsAsBags__e_bsl_fsl_Obligation_subtype
  apply(rule BagsAsMaps__occurrences)
  apply(simp add: SetsAsBags__set_insert_def BagsAsMaps__bag_insertion)
  apply(auto simp add: BagsAsMaps__bagin_of_insert SetsAsBags__in_p_def BagsAsMaps__Map_P_of_insert SetsAsBags__set_insert_def BagsAsMaps__bag_insertion)
end-proof

proof Isa Bag__in_bag_union
  apply(metis Bag__occs_bag_union BagsAsMaps__bagin_p_def add_is_0)
end-proof

proof Isa Bag__commutativity_of_bag_union
  apply(rule BagsAsMaps__occurrences)
  sorry
end-proof

proof Isa Bag__associative_bag_join
  sorry
end-proof

proof Isa Bag__bagin_p_of_bag_intersection
  sorry
end-proof

proof Isa Bag__bag_intersection_right_zero
  sorry
end-proof

proof Isa Bag__bag_intersection_left_zero
  sorry
end-proof

proof Isa Bag__bag_sum_empty
  sorry
end-proof

proof Isa Bag__bag_sum_insert
  sorry
end-proof

proof Isa Bag__delete_of_empty
  sorry
end-proof

proof Isa Bag__distribute_bagunion_over_right_insert
  sorry
end-proof

proof Isa Bag__distribute_bagunion_over_left_insert
  sorry
end-proof

proof Isa Bag__distribute_bag_diff_over_left_insert
  sorry
end-proof

proof Isa Bag__distribute_bagunion_over_right_delete
  sorry
end-proof

proof Isa Bag__distribute_bag_diff_over_left_delete
  sorry
end-proof

proof Isa Bag__distribute_bag_diff_over_right_insert
  sorry
end-proof

proof Isa Bag__bag_union_right_unit
  sorry
end-proof

proof Isa Bag__bag_union_left_unit
  sorry
end-proof

proof Isa Bag__bag_diff_left_zero
  sorry
end-proof



M = morphism Sets -> SetsAsBagMaps {Set._ +-> SetsAsBags._}

proof Isa Set__membership
  sorry
end-proof

proof Isa Set__subset_def
  sorry
end-proof

proof Isa Set__empty_set
  sorry
end-proof

proof Isa Set__set_insertion
  sorry
end-proof

proof Isa Set__set_union
  sorry
end-proof

proof Isa Set__set_intersection
  sorry
end-proof

proof Isa Set__induction
  sorry
end-proof

proof Isa Set__set_fold1
  sorry
end-proof

proof Isa Set__set_fold2
  sorry
end-proof

proof Isa Set__set_deletion
  sorry
end-proof

proof Isa Set__set_difference
  sorry
end-proof

proof Isa Set__filter_def
  sorry
end-proof

proof Isa Set__map_def
  sorry
end-proof

proof Isa nt_subset_def
  sorry
end-proof

proof Isa e_bsl_bsl_fsl_fsl_def_Obligation_subtype
  sorry
end-proof

proof Isa e_bsl_bsl_fsl_fsl_def
  sorry
end-proof

proof Isa e_fsl_fsl_bsl_bsl_def_Obligation_subtype
  sorry
end-proof

proof Isa e_fsl_fsl_bsl_bsl_def
  sorry
end-proof

proof Isa set_insert_new_def
  sorry
end-proof

proof Isa Set__set_delete_new_def
  sorry
end-proof

proof Isa Set__size_def
  sorry
end-proof

proof Isa size_def_Obligation_subtype
  sorry
end-proof
