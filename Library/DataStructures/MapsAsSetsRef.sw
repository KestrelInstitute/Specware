% the following morphism witnesses (once its proof obligations are
% discharged) that MapsAsSets is indeed a refinement of Maps

morphism Maps -> MapsAsSets {}    % {Map.map_apply +-> apply}

% proof obligations:
% the axioms characterizing the operations in Maps are satisfied
% by the definitions of those operations in MapsAsSets


proof Isa Map__total_p_def
  apply(auto simp add: Map__total_p_def mem_def Set__subset)
  apply(cut_tac Map__map_domain, auto)
  apply(cut_tac Map__map_domain, auto)
end-proof

proof Isa Map__map_equality
  sorry
end-proof

proof Isa Map__empty_map
  sorry
end-proof

proof Isa Map__update
  sorry
end-proof

proof Isa Map__def_of_singletonMap
  sorry
end-proof

proof Isa Map__map_induction
  sorry
end-proof

proof Isa Map__map_domain
  sorry
end-proof

proof Isa Map__map_range
  sorry
end-proof

proof Isa Map__map_domainToList
  sorry
end-proof

proof Isa Map__map_rangeToList
  sorry
end-proof

proof Isa Map__totalmap_equality_Obligation_subtype
  sorry
end-proof

proof Isa Map__totalmap_equality_Obligation_subtype0
  sorry
end-proof

proof Isa Map__totalmap_equality
  sorry
end-proof

proof Isa Map__TMApply_def_Obligation_the
  sorry
end-proof

proof Isa Map__TMApply_def
  sorry
end-proof

proof Isa Map__map_apply_def
  sorry
end-proof

proof Isa Map__size_def
  sorry
end-proof

