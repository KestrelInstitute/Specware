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
