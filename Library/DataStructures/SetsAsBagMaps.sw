%%% Should directly go to sets as characteristic Maps, i.e. Set a = Map(a, Bool)

%% TODO: Add a SetsAsBagMaps qualifier?  Otherwise, the names conflict with SetsAsBags
SetsAsBagMaps = SetsAsBags[BagsAsMaps#M]

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

