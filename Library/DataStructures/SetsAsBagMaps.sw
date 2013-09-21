%%% Should directly go to sets as characteristic Maps, i.e. Set a = Map(a, Bool)

%% FIXME: Figure out the story with the proof obligations of this.
%% FIXME: The obligations have the same names as the obligations in SetsAsBags, for which we already have proofs that Specware tries to use but that won't work in this context!
%% FIXME: I'd like to put the proofs for this just below this next line:
SetsAsBagMaps = SetsAsBags[BagsAsMaps#M]

%% Translated version of the proof in SetsAsBags.sw:
proof Isa set_insert_Obligation_subtype
   apply(simp add: SetsAsBags__no_rep_p_def BagsAsMaps__bag_fold2 BagsAsMaps__bag_insertion)
   apply(auto simp add: SetsAsBags__in_p_def BagsAsMaps__bagin_p_def)
   apply(rule BagsAsMaps__bag_fold_true)
   apply(auto)
   apply(smt BagsAsMaps__bag_fold_true_back Pair_inject prod_caseE)
end-proof

%% Translated version of the proof in SetsAsBags.sw:
proof Isa SetsAsBags__empty_set_Obligation_subtype
  apply(simp add: SetsAsBags__no_rep_p_def BagsAsMaps__bag_fold1)
end-proof

%% Translated version of the proof in SetsAsBags.sw:
proof Isa set_insert_new_Obligation_subtype
  apply(rule SetsAsBags__set_insert_Obligation_subtype, assumption, assumption)
end-proof

%% Translated version of the proof in SetsAsBags.sw:
proof Isa e_bsl_fsl_Obligation_subtype
  apply(rule BagsAsMaps__occurrences)
  apply(simp add: SetsAsBags__set_insert_def BagsAsMaps__bag_insertion)
  apply(auto simp add: BagsAsMaps__bagin_of_insert SetsAsBags__in_p_def)
end-proof

%% Translated version of the proof in SetsAsBags.sw:
proof Isa e_fsl_bsl_Obligation_subtype
  apply(rule BagsAsMaps__occurrences, auto simp add: SetsAsBags__set_insert_def BagsAsMaps__bag_insertion SetsAsBags__in_p_def BagsAsMaps__bagin_of_insert)
  apply(cases "z=y", auto)
  apply(simp add: BagsAsMaps__bag_insertion_commutativity)
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
