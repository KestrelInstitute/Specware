FMap qualifying spec

  (* Here we refine proto-maps to be finite maps and we add a few ops that are
  specific to finite maps and do not apply to infinite maps. *)

  import translate ProtoMaps
                   [morphism ProtoMapsParameter ->
                             ProtoMapsInstantiationFinite
                             {PSet.protoSetPredicate? +-> FSet.protoSetPredicate?,
                              PSet.PSetPredicate      +-> FSet.PSetPredicate,
                              PSet.PSet               +-> FSet.FSet,
                              PSet.setPredicate       +-> FSet.setPredicate,
                              PSet.setSuchThat        +-> FSet.setSuchThat,
                              PSet.in?                +-> FSet.in?,
                              PSet.<=                 +-> FSet.<=,
                              PSet.>=                 +-> FSet.>=,
                              PSet.forall?            +-> FSet.forall?,
                              PSet.exists?            +-> FSet.exists?,
                              PSet.\/                 +-> FSet.\/,
                              PSet./\                 +-> FSet./\,
                              PSet.unionAll           +-> FSet.unionAll,
                              PSet.intersectAll       +-> FSet.intersectAll,
                              PSet.--                 +-> FSet.--,
                              PSet.empty              +-> FSet.empty,
                              PSet.empty?             +-> FSet.empty?,
                              PSet.singleton          +-> FSet.singleton,
                              PSet.singleton?         +-> FSet.singleton?,
                              PSet.uniqueElement      +-> FSet.uniqueElement,
                              PSet.with               +-> FSet.with,
                              PSet.wout               +-> FSet.wout,
                              PSet.map                +-> FSet.map,
                              PSet.filter             +-> FSet.filter}]
                   by {PMap       +-> FMap.FMap,
                       <<=        +-> FMap.<=,
                       >>=        +-> FMap.>=,
                       mempty     +-> FMap.empty,
                       msingleton +-> FMap.singleton,
                       \\/        +-> FMap.\/,
                       //\        +-> FMap./\,
                       mmap       +-> FMap.map,
                       mfilter    +-> FMap.filter}

  op size : [a,b] FMap(a,b) -> Nat
  def size m = size (domain m)

  (* The requirements to fold over a map are similar to those to fold over a
  set; see spec `FiniteSets'. *)

  op foldable? : [a,b,c] FMap(a,b) * c * (c * b -> c) -> Boolean
  def [a,b,c] foldable?(m,c,f) =
    (fa (x:a, y:a, z:c) x in? domain m && y in? domain m =>
                        f(f(z,apply(m,x)),apply(m,y)) =
                        f(f(z,apply(m,y)),apply(m,x)))

  op fold : [a,b,c] FMap(a,b) * c * (c * b -> c) -> c
  def [a,b,c] fold =
    the (fn (fold : FMap(a,b) * c * (c * b -> c) -> c) ->
      (fa(c,f) foldable? (empty, c, f) => fold (empty, c, f) = c) &&
      (fa(m,x,y,c,f) foldable? (define(m,x,y), c, f) =>
                     fold (define(m,x,y), c, f) =
                     f (fold (undefine(m,x), c, f), y)))

  (* With a map, we can also fold including domain values in the function. *)

  op foldableDom? : [a,b,c] FMap(a,b) * c * (c * a * b -> c) -> Boolean
  def [a,b,c] foldableDom?(m,c,f) =
    (fa (x:a, y:a, z:c) x in? domain m && y in? domain m =>
                        f(f(z,x,apply(m,x)),y,apply(m,y)) =
                        f(f(z,y,apply(m,y)),x,apply(m,x)))

  op foldDom : [a,b,c] FMap(a,b) * c * (c * a * b -> c) -> c
  def [a,b,c] foldDom =
    the (fn (foldDom : FMap(a,b) * c * (c * a * b -> c) -> c) ->
      (fa(c,f) foldableDom? (empty, c, f) => foldDom (empty, c, f) = c) &&
      (fa(m,x,y,c,f) foldableDom? (define(m,x,y), c, f) =>
                     foldDom (define(m,x,y), c, f) =
                     f (foldDom (undefine(m,x), c, f), x, y)))

endspec
