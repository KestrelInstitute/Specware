spec

  (* See the explanation in spec `ProtoMaps'. *)

  import PartialFunctions

  op protoMapFunction? : [a,b] PFunction(a,b) -> Boolean

  axiom atLeastAllFiniteFunctions is [a,b]
    fa (f : PFunction(a,b)) finite? f => protoMapFunction? f

endspec
