(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% we compose this refinement of maps as sets with the refinement of
% sets as lists, thus obtaining a refinement of maps as lists: a map
% is represented by an equivalence class of repetition-free lists of pairs
% satisfying the "functional requirement"

% the refinements are composed by substituting Sets with SetsAsLists
% in MapsAsSets

MapsAsLists = MapsAsSets[SetsAsLists#M]

M = morphism Maps -> MapsAsLists {}