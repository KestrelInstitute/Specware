PMap qualifying spec

  (* See the explanation in spec `ProtoMaps'. *)

  import PartialFunctions

  op protoMapFunction? : [a,b] PFunction(a,b) -> Boolean

  axiom finiteOrAllFunctions is [a,b]
    protoMapFunction? = finite? ||
    protoMapFunction? = (fn f -> true)

  import ProtoSets

endspec
