FMap qualifying spec

  import /Library/General/Maps,
         /Library/General/EndoRelations,
         /Library/General/FiniteSets

  % maps as (functional) sets of pairs:
  type FMap(a,b) = (FSet (a * b) | (functional? o fromFSet))

  op toFMap : [a,b] Bijection (FiniteMap(a,b), FMap(a,b))
  def toFMap finiteMap =  % not executable
    toFSet finiteMap

  op fromFMap : [a,b] FMap(a,b) -> FiniteMap(a,b)
  def fromFMap m = fromFSet m

  op maps? : [a,b] FMap(a,b) -> a -> b -> Boolean
  def maps? m x y = (x,y) in? m

  op domain : [a,b] FMap(a,b) -> FSet a
  def domain m = map (project 1) m

  op range : [a,b] FMap(a,b) -> FSet b
  def range m = map (project 2) m

  op definedAt infixl 20 : [a,b] FMap(a,b) * a -> Boolean
  def definedAt (m,x) = x in? domain m

  op undefinedAt infixl 20 : [a,b] FMap(a,b) * a -> Boolean
  def undefinedAt (m,x) = x nin? domain m

  op @ infixl 30 : [a,b] ((FMap(a,b) * a) | definedAt) -> b
  def @ (m,x) = let xy = FSet.theMember (filter (fn(x1,_) -> x1 = x) m) in xy.2

  op @@ infixl 30 : [a,b] FMap(a,b) * a -> Option b
  def @@ (m,x) = if m definedAt x then Some (m @ x) else None

  op applyi : [a,b] FMap(a,b) -> b -> FSet a
  def applyi m y = map (project 1) (filter (fn(_,y1) -> y1 = y) m)

  op applys : [a,b] FMap(a,b) -> FSet a -> FSet b
  def applys m xS = map (project 2) (filter (fn(x,_) -> x in? xS) m)

  op applyis : [a,b] FMap(a,b) -> FSet b -> FSet a
  def applyis m yS = map (project 1) (filter (fn(_,y) -> y in? yS) m)

  op id : [a] FSet a -> FMap(a,a)
  def id dom = map (fn x -> (x,x)) dom

  op :> infixl 24 : [a,b,c] FMap(a,b) * FMap(b,c) -> FMap(a,c)
  def [a,b,c] :> (m1,m2) =
    let def foldingFunction (m : FMap(a,c), (x,y) : a*b) : FMap(a,c) =
          case m2 @@ y of
            | Some z -> m <| (x,z)
            | None -> m
    in
    fold (empty, foldingFunction, m1)

  op o infixl 24 : [a,b,c] FMap(b,c) * FMap(a,b) -> FMap(a,c)
  def o (m1,m2) = m2 :> m1

  op <= infixl 20 : [a,b] FMap(a,b) * FMap(a,b) -> Boolean
  def <= (m1,m2) = m1 FSet.<= m2

  op < infixl 20 : [a,b] FMap(a,b) * FMap(a,b) -> Boolean
  def < (m1,m2) = m1 FSet.< m2

  op >= infixl 20 : [a,b] FMap(a,b) * FMap(a,b) -> Boolean
  def >= (m1,m2) = m1 FSet.>= m2

  op > infixl 20 : [a,b] FMap(a,b) * FMap(a,b) -> Boolean
  def > (m1,m2) = m1 FSet.> m2

  op empty : [a,b] FMap(a,b)
  def empty = FSet.empty

  op empty? : [a,b] FMap(a,b) -> Boolean
  def empty? m = FSet.empty? m

  op nonEmpty? : [a,b] FMap(a,b) -> Boolean
  def nonEmpty? m = FSet.nonEmpty? m

  type NonEmptyFMap(a,b) = (FMap(a,b) | nonEmpty?)

  op forall? : [a,b] (a * b -> Boolean) -> FMap(a,b) -> Boolean
  def forall? p m = FSet.forall? p m

  op exists? : [a,b] (a * b -> Boolean) -> FMap(a,b) -> Boolean
  def exists? p m = FSet.exists? p m

  op exists1? : [a,b] (a * b -> Boolean) -> FMap(a,b) -> Boolean
  def exists1? p m = FSet.exists1? p m

  op agree? : [a,b] FMap(a,b) * FMap(a,b) -> Boolean
  def agree?(m1,m2) =
    forall? (fn(x,y) -> case m2 @@ x of Some y1 -> y1 = y | None -> true) m1

  op /\ infixr 25 : [a,b] ((FMap(a,b) * FMap(a,b)) | agree?) -> FMap(a,b)
  def /\ (m1,m2) = m1 FSet./\ m2

  op \/ infixr 24 : [a,b] ((FMap(a,b) * FMap(a,b)) | agree?) -> FMap(a,b)
  def \/ (m1,m2) = m1 FSet.\/ m2

  op filter : [a,b] (a * b -> Boolean) -> FMap(a,b) -> FMap(a,b)
  def filter p m = FSet.filter p m

  op restrictDomain infixl 25 : [a,b] FMap(a,b) * (a -> Boolean) -> FMap(a,b)
  def restrictDomain (m,p) = filter (fn(x,_) -> p x) m

  op restrictRange infixl 25 : [a,b] FMap(a,b) * (b -> Boolean) -> FMap(a,b)
  def restrictRange (m,p) = filter (fn(_,y) -> p y) m

  op <<< infixl 25 : [a,b] FMap(a,b) * FMap(a,b) -> FMap(a,b)
  def [a,b] <<< (m1,m2) =
    (m1 restrictDomain (fn x -> x nin? domain m2)) \/ m2

  op update : [a,b] FMap(a,b) -> a -> b -> FMap(a,b)
  def update m x y = m <<< single (x,y)

  op -- infixl 25 : [a,b] FMap(a,b) * FSet a -> FMap(a,b)
  def -- (m,xS) = m restrictDomain (fn x -> x nin? xS)

  op - infixl 25 : [a,b] FMap(a,b) * a -> FMap(a,b)
  def - (m,x) = m -- single x

  op single : [a,b] a -> b -> FMap(a,b)
  def single x y = single (x,y)

  op single? : [a,b] FMap(a,b) -> Boolean
  def single? m = FSet.single? m

  type SingletonFMap(a,b) = (FMap(a,b) | single?)

  op thePair : [a,b] SingletonFMap(a,b) -> a * b
  def thePair m = theMember m

  op size : [a,b] FMap(a,b) -> Nat
  def size m = FSet.size m

  op foldable? : [a,b,c] c * (c * (a*b) -> c) * FMap(a,b) -> Boolean
  def foldable?(c,f,m) = % not executable
    FSet.foldable? (c, f, m)

  op fold : [a,b,c] ((c * (c * (a*b) -> c) * FMap(a,b)) | foldable?) -> c
  def fold(c,f,m) = FSet.fold (c, f, m)

  op injective? : [a,b] FMap(a,b) -> Boolean
  def injective? m =
    size (domain m) = size (range m)

  type InjectiveFMap(a,b) = (FMap(a,b) | injective?)

  op inverse : [a,b] InjectiveFMap(a,b) -> InjectiveFMap(b,a)
  def inverse m = map (fn(x,y) -> (y,x)) m

  op map : [a,b,c] (b -> c) -> FMap(a,b) -> FMap(a,c)
  def map f m = map (fn(x,y) -> (x, f y)) m

  op mapWithDomain : [a,b,c] (a * b -> c) -> FMap(a,b) -> FMap(a,c)
  def mapWithDomain f m = map (fn(x,y) -> (x, f(x,y))) m

  op toFSet : [a,b] FMap(a,b) -> FSet(a*b)
  def toFSet m = m

  op fromFSet : [a,b] {s : FSet (a*b) | functional? (fromFSet s)} -> FMap(a,b)
  def fromFSet = id

endspec
