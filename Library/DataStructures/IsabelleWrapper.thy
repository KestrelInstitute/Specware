theory IsabelleWrapper

(* This is a hand-written Isabelle wrapper used for testing.  It is faster to process this Isabelle theory than the separate theories below separately (because common things like the Base libraries are processed only once).  This file was not put in Isa/ because often that directory is cleared out and we want to keep this hand-written file. *)

imports "Isa/MapsAsSets_M" "Isa/SetsAsMaps_M" "Isa/SetsAsBagMaps_M" "Isa/StacksAsCoproducts_M" "Isa/StacksAsLists_M" "Isa/SetsAsBags_M" "Isa/BagsAsMaps_M" "Isa/MapsAsSTHTables_M" "Isa/MapsAsVectors_M" "Isa/AllIsa"

begin
end