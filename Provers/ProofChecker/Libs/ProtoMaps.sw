spec

  (* A map can be viewed as a partial function. We specify the type `Map' of
  all maps (finite and infinite) and the type `FMap' of finite maps
  analogously to `Set' and `FSet': see the explanations in spec
  `ProtoSets'. *)

  import ProtoMapsParameter

  (* Since certain operations on maps involve sets (e.g. return the domain of
  a map), we use proto-sets in this spec. Proto-sets are instantiated to
  finite sets or all sets at the same time when proto-maps are instantiated to
  finite maps or all maps. *)

  import ProtoSets

endspec
