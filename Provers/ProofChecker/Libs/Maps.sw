Map qualifying spec

  (* Here we refine proto-maps to be all maps and we add a few ops that are
  specific to all maps and do not apply to finite maps. *)

  import translate ProtoMaps
                   [morphism ProtoMapsParameter ->
                             ProtoMapsInstantiationAll
                             {PSet.protoSetPredicate? +-> Set.protoSetPredicate?,
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
                   by {PMap       +-> Map.Map,
                       <<=        +-> Map.<=,
                       >>=        +-> Map.>=,
                       mempty     +-> Map.empty,
                       msingleton +-> Map.singleton,
                       \\/        +-> Map.\/,
                       //\        +-> Map./\,
                       mmap       +-> Map.map,
                       mfilter    +-> Map.filter}

  op finite? : [a,b] Map(a,b) -> Boolean
  def finite? m = finite? (domain m)

endspec
