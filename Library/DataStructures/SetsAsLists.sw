(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% we compose the refinement of sets as bags with the refinement of
% bags as lists, thus obtaining a refinement of sets as lists: a set
% is represented by an equivalence class of repetition-free lists

% the refinements are composed by substituting Bags with BagsAsLists
% in SetsAsBags

SetsAsLists = SetsAsBags[BagsAsLists#M] 

% the validity of this morphism follows by compositionality from the
% validity of SetsAsBagsRef and BagsAsLists#M

% The same as SetsAsListsRef (now removed).
M = morphism Sets -> SetsAsLists {}
