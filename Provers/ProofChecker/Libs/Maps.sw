Map qualifying spec

  (* Here we refine proto-maps to be all maps and we add a few ops that are
  specific to all maps and do not apply to finite maps.

  The spec imported by the following `import' is constructed from spec
  `ProtoMaps' as follows: (1) rename type `PMap' to `Map'; (2) substitute spec
  `ProtoMapsParameter' with spec `ProtoMapsInstantiationAll' (which includes
  substituting spec `ProtoSets' with spec `Sets'); and (3) rename qualifier
  `PMap' to `Map'. *)

  import translate (translate ProtoMaps by {PMap +-> Map})
                   [morphism ProtoMapsParameter ->
                             ProtoMapsInstantiationAll
                             {protoMapFunction?       +-> protoMapFunction?,
                              PSet.protoSetPredicate? +-> Set.protoSetPredicate?,
                              PSet.PSetPredicate      +-> Set.PSetPredicate,
                              PSet.PSet               +-> Set.Set,
                              PSet.setPredicate       +-> Set.setPredicate,
                              PSet.setSuchThat        +-> Set.setSuchThat,
                              PSet.in?                +-> Set.in?,
                              PSet.<=                 +-> Set.<=,
                              PSet.>=                 +-> Set.>=,
                              PSet.forall?            +-> Set.forall?,
                              PSet.exists?            +-> Set.exists?,
                              PSet.\/                 +-> Set.\/,
                              PSet./\                 +-> Set./\,
                              PSet.unionAll           +-> Set.unionAll,
                              PSet.intersectAll       +-> Set.intersectAll,
                              PSet.--                 +-> Set.--,
                              PSet.empty              +-> Set.empty,
                              PSet.empty?             +-> Set.empty?,
                              PSet.singleton          +-> Set.singleton,
                              PSet.singleton?         +-> Set.singleton?,
                              PSet.uniqueElement      +-> Set.uniqueElement,
                              PSet.with               +-> Set.with,
                              PSet.wout               +-> Set.wout,
                              PSet.map                +-> Set.map,
                              PSet.filter             +-> Set.filter}]
                   by {PMap._ +-> Map._}

  op finite? : [a,b] Map(a,b) -> Boolean
  def finite? m = finite? (domain m)

endspec
