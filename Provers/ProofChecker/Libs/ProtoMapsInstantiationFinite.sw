spec

  (* See spec `ProtoMaps' for an explanation. This spec instantiates
  protoMapFunction? to contain exactly all finite functions and accordingly
  instantiates proto-sets to finite sets. *)

  import PartialFunctions

  op protoMapFunction? : [a,b] PFunction(a,b) -> Boolean
  def protoMapFunction? = finite?

  import FiniteSets

endspec
