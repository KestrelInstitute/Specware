FMap qualifying spec

  (* The motivation for this spec is analogous to the one for spec
  `FiniteSets'; see comments in that spec.

  Some of the operations on maps in spec `Maps' involve sets. In this spec, we
  use the (refinable) finite sets specified in spec `FiniteSets', otherwise we
  would be unable to refine this spec for finite maps. *)

  import Maps, EndoRelations, FiniteSets

  type FMap(a,b)

  % isomorphisms:

  op toFMap : [a,b] Bijection (FiniteMap(a,b), FMap(a,b))

  op fromFMap : [a,b] FMap(a,b) -> FiniteMap(a,b)
  def fromFMap = inverse toFMap

  (* Since `FiniteMap' is a subtype of `Map' which is a subtype of `Relation'
  which is a subtype of `Set', it "inherits" ops for maps, (endo)relations,
  and sets. Since `FMap(a,b)' is only isomorphic to `FiniteSet(a*b)' (as
  opposed to being a subtype), the relevant inherited ops (those that make
  sense for finite maps and that can be refined to actual implementations) are
  introduced here for type `FMap', and defined using the isomorphism. Some of
  the inherited ops for `Relation' and `Set' are renamed here to use names
  that are more appropriate to maps vs. relations and sets. *)

  % operations and subtypes:

  op maps? : [a,b] FMap(a,b) -> a -> b -> Boolean
  def maps? m x y = (x,y) in? fromFMap m

  op domain : [a,b] FMap(a,b) -> FSet a
  def domain m = toFSet (domain (fromFMap m))

  op range : [a,b] FMap(a,b) -> FSet b
  def range m = toFSet (range (fromFMap m))

  op definedAt infixl 20 : [a,b] FMap(a,b) * a -> Boolean
  def definedAt (m,x) = (fromFMap m) definedAt x

  op undefinedAt infixl 20 : [a,b] FMap(a,b) * a -> Boolean
  def undefinedAt (m,x) = (fromFMap m) undefinedAt x

  op @ infixl 30 : [a,b] ((FMap(a,b) * a) | definedAt) -> b
  def @ (m,x) = (fromFMap m) @ x

  op @@ infixl 30 : [a,b] FMap(a,b) * a -> Option b
  def @@ (m,x) = (fromFMap m) @@ x

  op applyi : [a,b] FMap(a,b) -> b -> FSet a
  def applyi m y = toFSet (applyi (fromFMap m) y)

  op applys : [a,b] FMap(a,b) -> FSet a -> FSet b
  def applys m xS = toFSet (applys (fromFMap m) (fromFSet xS))

  op applyis : [a,b] FMap(a,b) -> FSet b -> FSet a
  def applyis m yS = toFSet (applyis (fromFMap m) (fromFSet yS))

  op id : [a] FSet a -> FMap(a,a)
  def id dom = toFMap (idOver (fromFSet dom))

  op :> infixl 24 : [a,b,c] FMap(a,b) * FMap(b,c) -> FMap(a,c)
  def :> (m1,m2) = toFMap (fromFMap m1 :> fromFMap m2)

  op o infixl 24 : [a,b,c] FMap(b,c) * FMap(a,b) -> FMap(a,c)
  def o (m1,m2) = toFMap (fromFMap m1 o fromFMap m2)

  op <= infixl 20 : [a,b] FMap(a,b) * FMap(a,b) -> Boolean
  def <= (m1,m2) = fromFMap m1 <= fromFMap m2

  op < infixl 20 : [a,b] FMap(a,b) * FMap(a,b) -> Boolean
  def < (m1,m2) = fromFMap m1 < fromFMap m2

  op >= infixl 20 : [a,b] FMap(a,b) * FMap(a,b) -> Boolean
  def >= (m1,m2) = fromFMap m1 >= fromFMap m2

  op > infixl 20 : [a,b] FMap(a,b) * FMap(a,b) -> Boolean
  def > (m1,m2) = fromFMap m1 > fromFMap m2

  op empty : [a,b] FMap(a,b)
  def empty = toFMap empty

  op empty? : [a,b] FMap(a,b) -> Boolean
  def empty? m = empty? (fromFMap m)

  op nonEmpty? : [a,b] FMap(a,b) -> Boolean
  def nonEmpty? m = nonEmpty? (fromFMap m)

  type NonEmptyFMap(a,b) = (FMap(a,b) | nonEmpty?)

  op <<< infixl 25 : [a,b] FMap(a,b) * FMap(a,b) -> FMap(a,b)
  def <<< (m1,m2) = toFMap (fromFMap m1 <<< fromFMap m2)

  op update : [a,b] FMap(a,b) -> a -> b -> FMap(a,b)
  def update m x y = toFMap (update (fromFMap m) x y)

  op -- infixl 25 : [a,b] FMap(a,b) * FSet a -> FMap(a,b)
  def -- (m,xS) = toFMap (fromFMap m -- fromFSet xS)

  op - infixl 25 : [a,b] FMap(a,b) * a -> FMap(a,b)
  def - (m,x) = toFMap (fromFMap m - x)

  op agree? : [a,b] FMap(a,b) * FMap(a,b) -> Boolean
  def agree?(m1,m2) = agree? (fromFMap m1, fromFMap m2)

  op /\ infixr 25 : [a,b] ((FMap(a,b) * FMap(a,b)) | agree?) -> FMap(a,b)
  def /\ (m1,m2) = toFMap (fromFMap m1 /\ fromFMap m2)

  op \/ infixr 24 : [a,b] ((FMap(a,b) * FMap(a,b)) | agree?) -> FMap(a,b)
  def \/ (m1,m2) = toFMap (fromFMap m1 \/ fromFMap m2)

  op forall? : [a,b] (a * b -> Boolean) -> FMap(a,b) -> Boolean
  def forall? p m = fromFMap m <= p

  op exists? : [a,b] (a * b -> Boolean) -> FMap(a,b) -> Boolean
  def exists? p m = nonEmpty? (fromFMap m /\ p)

  op exists1? : [a,b] (a * b -> Boolean) -> FMap(a,b) -> Boolean
  def exists1? p m = single? (fromFMap m /\ p)

  op filter : [a,b] (a * b -> Boolean) -> FMap(a,b) -> FMap(a,b)
  def filter p m = toFMap (fromFMap m /\ p)

  op restrictDomain infixl 25 : [a,b] FMap(a,b) * (a -> Boolean) -> FMap(a,b)
  def restrictDomain (m,p) = toFMap (fromFMap m restrictDomain p)

  op restrictRange infixl 25 : [a,b] FMap(a,b) * (b -> Boolean) -> FMap(a,b)
  def restrictRange (m,p) = toFMap (fromFMap m restrictRange p)

  op single : [a,b] a -> b -> FMap(a,b)
  def single x y = toFMap (single (x,y))

  op single? : [a,b] FMap(a,b) -> Boolean
  def single? m = single? (fromFMap m)

  type SingletonFMap(a,b) = (FMap(a,b) | single?)

  op thePair : [a,b] SingletonFMap(a,b) -> a * b
  def thePair m = theMember (fromFMap m)

  op size : [a,b] FMap(a,b) -> Nat
  def size m = size (fromFMap m)

  op foldable? : [a,b,c] c * (c * (a*b) -> c) * FMap(a,b) -> Boolean
  def foldable?(c,f,m) = foldable? (c, f, fromFMap m)

  op fold : [a,b,c] ((c * (c * (a*b) -> c) * FMap(a,b)) | foldable?) -> c
  def fold(c,f,m) = fold (c, f, fromFMap m)

  op injective? : [a,b] FMap(a,b) -> Boolean
  def injective? m = Relation.injective? (fromFMap m)

  type InjectiveFMap(a,b) = (FMap(a,b) | injective?)

  op inverse : [a,b] InjectiveFMap(a,b) -> InjectiveFMap(b,a)
  def inverse m = toFMap (inverse (fromFMap m))

  % apply function to all range values:
  op map : [a,b,c] (b -> c) -> FMap(a,b) -> FMap(a,c)
  def [a,b,c] map f m =
    let fLiftedToPairs: a * b -> a * c = (fn (x,y) -> (x, f y)) in
    toFMap (map fLiftedToPairs (fromFMap m))

  % like previous op but also include domain value:
  op mapWithDomain : [a,b,c] (a * b -> c) -> FMap(a,b) -> FMap(a,c)
  def [a,b,c] mapWithDomain f m =
    let fLiftedToPairs: a * b -> a * c = (fn (x,y) -> (x, f(x,y))) in
    toFMap (map fLiftedToPairs (fromFMap m))

  (* While `FiniteMap(a,b)' is a subtype of `FiniteSet(a*b)', the types
  `FMap(a,b)' and `FSet(a*b)' are just isomorphic. So, we provide explicit
  conversions here. *)

  op toFSet : [a,b] FMap(a,b) -> FSet(a*b)
  def toFSet m = toFSet (fromFMap m)

  op fromFSet : [a,b] {s : FSet(a*b) | functional? (fromFSet s)} -> FMap(a,b)
  def fromFSet s = toFMap (fromFSet s)

endspec
