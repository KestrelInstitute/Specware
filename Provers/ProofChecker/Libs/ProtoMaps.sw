PMap qualifying spec

  (* A map can be viewed as a partial function. We specify the type `Map' of
  all maps (finite and infinite) and the type `FMap' of finite maps
  analogously to the types `Set' and `FSet': see the explanation in spec
  `ProtoSets'.

  Since certain operations on maps involve sets (e.g. return the domain of
  a map), we use proto-sets in this spec. Proto-sets are instantiated to
  finite sets or all sets at the same time when proto-maps are instantiated to
  finite maps or all maps. So, proto-sets are imported in spec
  `ProtoMapsParameter', which constitutes the parameter of this spec. *)

  import ProtoMapsParameter

  type PMapFunction(a,b) = (PFunction(a,b) | protoMapFunction?)

  type PMap(a,b)

  op mapFunction : [a,b] Bijection (PMap(a,b), PMapFunction(a,b))

  % construct map from function:
  op mapSuchThat : [a,b] Bijection (PMapFunction(a,b), PMap(a,b))
  def mapSuchThat = inverse mapFunction

  op apply : [a,b] {(m,x) : PMap(a,b) * a | definedAt? (mapFunction m, x)} -> b
  def apply(m,x) =
    the (fn y -> mapFunction m x = Some y)

  op domain : [a,b] PMap(a,b) -> PSet a
  def domain m =
    setSuchThat (fn x -> definedAt? (mapFunction m, x))

  op range : [a,b] PMap(a,b) -> PSet b
  def range m =
    setSuchThat (fn y -> (ex(x) mapFunction m x = Some y))

  op <= infixl 20 : [a,b] PMap(a,b) * PMap(a,b) -> Boolean
  def <= (m1,m2) =
    domain m1 <= domain m2 &&
    (fa(x) x in? domain m1 => apply(m1,x) = apply(m2,x))

  op >= infixl 20 : [a,b] PMap(a,b) * PMap(a,b) -> Boolean
  def >= (m1,m2) = (m2 <= m1)

  op empty : [a,b] PMap(a,b)
  def empty =
    mapSuchThat (fn x -> None)

  % extend or overwrite map at point:
  op define : [a,b] PMap(a,b) * a * b -> PMap(a,b)
  def define(m,x,y) =
    mapSuchThat (fn z -> if z = x then Some y else mapFunction m z)

  % extend or overwrite map at multiple points:
  op defineMulti : [a,b] PMap(a,b) * PMap(a,b) -> PMap(a,b)
  def defineMulti(m,update) =
    mapSuchThat (fn z -> if z in? domain update
                         then mapFunction update z
                         else mapFunction m z)

  % make map undefined at point:
  op undefine : [a,b] PMap(a,b) * a -> PMap(a,b)
  def undefine(m,x) =
    mapSuchThat (fn z -> if z = x then None else mapFunction m z)

  % map map defined at one point:
  op singleton : [a,b] a * b -> PMap(a,b)
  def singleton(x,y) = define (empty, x, y)

  % make map undefined at multiple points:
  op undefineMulti : [a,b] PMap(a,b) * PSet a -> PMap(a,b)
  def undefineMulti(m,dom) =
    mapSuchThat (fn z -> if z in? dom
                         then None
                         else mapFunction m z)

  op definedAt? : [a,b] PMap(a,b) * a -> Boolean
  def definedAt?(m,x) = (x in? domain m)

  op undefinedAt? : [a,b] PMap(a,b) * a -> Boolean
  def undefinedAt?(m,x) = ~(x in? domain m)

  % identity map with given domain:
  op id : [a] PSet a -> PMap(a,a)
  def id dom = mapSuchThat (fn x -> if x in? dom then Some x else None)

  op o infixl 24 : [a,b,c] PMap(b,c) * PMap(a,b) -> PMap(a,c)
  def o (m2, m1) =
    mapSuchThat (fn x -> case mapFunction m1 x of
                            | Some y -> mapFunction m2 y
                            | None   -> None)

  % maps agree on intersection of domains:
  op agree? : [a,b] PMap(a,b) * PMap(a,b) -> Boolean
  def agree?(m1,m2) =
    (fa(x) x in? (domain m1 /\ domain m2) => apply(m1,x) = apply(m2,x))

  op \/ infixl 25 : [a,b] ((PMap(a,b) * PMap(a,b)) | agree?) -> PMap(a,b)
  def \/ (m1, m2) =
    mapSuchThat (fn x -> if x in? domain m1 then mapFunction m1 x
                    else if x in? domain m2 then mapFunction m2 x
                    else None)

  op /\ infixl 25 : [a,b] ((PMap(a,b) * PMap(a,b)) | agree?) -> PMap(a,b)
  def /\ (m1, m2) =
    mapSuchThat (fn x -> if x in? (domain m1 /\ domain m2)
                         then mapFunction m1 x % = mapFunction m2 x
                         else none)

  % map[verb] function over range values of map[noun]:
  op map : [a,b,c] (b -> c) * PMap(a,b) -> PMap(a,c)
  def map(f,m) =
    mapSuchThat (fn x -> case mapFunction m x of
                            | Some y -> Some (f y)
                            | None   -> None)

  % like (m)map but include domain value as argument to function:
  op mapDom : [a,b,c] (a * b -> c) * PMap(a,b) -> PMap(a,c)
  def mapDom(f,m) =
    mapSuchThat (fn x -> case mapFunction m x of
                            | Some y -> Some (f(x,y))
                            | None   -> None)

  op filterDom : [a,b] PMap(a,b) * Predicate a -> PMap(a,b)
  def filterDom(m,p) =
    mapSuchThat (fn x -> if p x then mapFunction m x else None)

  op filterRange : [a,b] PMap(a,b) * Predicate b -> PMap(a,b)
  def filterRange(m,p) =
    mapSuchThat (fn x -> case mapFunction m x of
                            | Some y -> (if p y then Some y else None)
                            | None   -> None)

  op filter : [a,b] PMap(a,b) * Predicate(a*b) -> PMap(a,b)
  def filter(m,p) =
    mapSuchThat (fn x -> case mapFunction m x of
                            | Some y -> (if p(x,y) then Some y else None)
                            | None   -> None)

endspec
