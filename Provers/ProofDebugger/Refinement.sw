(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

morphism Spec -> Implementation  
  %% use same mappings as in /Library/General/FiniteSequencesAsListsMorphism
  {FSeq.++      +-> List.++,
   FSeq.length  +-> List.length,
   FSeq.foldr   +-> List.foldr,
   FSeq.map     +-> List.map,
   FSeq.filter  +-> List.filter,
   FSeq.flatten +-> List.flatten}
