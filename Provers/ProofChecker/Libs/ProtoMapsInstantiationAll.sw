spec

  (* See spec `ProtoMaps' for an explanation. This spec instantiates
  protoMapFunction? to contain all partial functions and accordingly
  instantiates proto-sets to sets. *)

  import PartialFunctions

  op protoMapFunction? : [a,b] PFunction(a,b) -> Boolean
  def protoMapFunction? = fn f -> true

  import Sets

endspec
