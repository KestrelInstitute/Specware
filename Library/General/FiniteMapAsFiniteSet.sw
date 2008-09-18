FMap qualifying spec

  import Map, EndoRelation, FiniteSet

  % maps as (functional) sets of pairs:
  type FMap(a,b) = (FSet (a * b) | (functional? o fromFSet))

  op toFMap : [a,b] Bijection (FiniteMap(a,b), FMap(a,b)) =
    fn finiteMap: FiniteMap(a,b) -> toFSet finiteMap  % not executable

  op [a,b] fromFMap (m: FMap(a,b)) : FiniteMap(a,b) = fromFSet m

  op [a,b] maps? (m: FMap(a,b)) (x:a) (y:b) : Boolean = (x,y) in? m

  op [a,b] domain (m: FMap(a,b)) : FSet a = map (project 1) m

  op [a,b] range (m: FMap(a,b)) : FSet b = map (project 2) m

  op [a,b] definedAt (m: FMap(a,b), x:a) infixl 20 : Boolean = x in? domain m

  op [a,b] undefinedAt (m: FMap(a,b), x:a) infixl 20 : Boolean =
    x nin? domain m

  op [a,b] @ (m: FMap(a,b), x:a | m definedAt x) infixl 30 : b =
    let xy = FSet.theMember (filter (fn(x1,_) -> x1 = x) m) in xy.2

  op [a,b] @@ (m: FMap(a,b), x:a) infixl 30 : Option b =
    if m definedAt x then Some (m @ x) else None

  op [a,b] applyi (m: FMap(a,b)) (y:b) : FSet a =
    map (project 1) (filter (fn(_,y1) -> y1 = y) m)

  op [a,b] applys (m: FMap(a,b)) (xS: FSet a) : FSet b =
    map (project 2) (filter (fn(x,_) -> x in? xS) m)

  op [a,b] applyis (m: FMap(a,b)) (yS: FSet b) : FSet a =
    map (project 1) (filter (fn(_,y) -> y in? yS) m)

  op [a] id (dom: FSet a) : FMap(a,a) = map (fn x -> (x,x)) dom

  op [a,b,c] :> (m1: FMap(a,b), m2: FMap(b,c)) infixl 24 : FMap(a,c) =
    let def foldingFunction (m : FMap(a,c), (x,y) : a*b) : FMap(a,c) =
          case m2 @@ y of
            | Some z -> m <| (x,z)
            | None -> m
    in
    fold (empty, foldingFunction, m1)

  op [a,b,c] o (m1: FMap(b,c), m2: FMap(a,b)) infixl 24 : FMap(a,c) = m2 :> m1

  op [a,b] <= (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Boolean = m1 FSet.<= m2

  op [a,b] < (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Boolean = m1 FSet.< m2

  op [a,b] >= (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Boolean = m1 FSet.>= m2

  op [a,b] > (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Boolean = m1 FSet.> m2

  op empty : [a,b] FMap(a,b) = FSet.empty

  op [a,b] empty? (m: FMap(a,b)) : Boolean = FSet.empty? m

  op [a,b] nonEmpty? (m: FMap(a,b)) : Boolean = FSet.nonEmpty? m

  type NonEmptyFMap(a,b) = (FMap(a,b) | nonEmpty?)

  op [a,b] forall? (p: a * b -> Boolean) (m: FMap(a,b)) : Boolean =
    FSet.forall? p m

  op [a,b] exists? (p: a * b -> Boolean) (m: FMap(a,b)) : Boolean =
    FSet.exists? p m

  op [a,b] exists1? (p: a * b -> Boolean) (m: FMap(a,b)) : Boolean =
    FSet.exists1? p m

  op [a,b] agree? (m1: FMap(a,b), m2: FMap(a,b)) : Boolean =
    forall? (fn(x,y) -> case m2 @@ x of Some y1 -> y1 = y | None -> true) m1

  op [a,b] /\ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 25
              : FMap(a,b) = m1 FSet./\ m2

  op [a,b] \/ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 24
              : FMap(a,b) = m1 FSet.\/ m2

  op [a,b] filter (p: a * b -> Boolean) (m: FMap(a,b)) : FMap(a,b) =
    FSet.filter p m

  op [a,b] restrictDomain (m: FMap(a,b), p: a -> Boolean) infixl 25
                          : FMap(a,b) = filter (fn(x,_) -> p x) m

  op [a,b] restrictRange (m: FMap(a,b), p: b -> Boolean) infixl 25
                         : FMap(a,b) = filter (fn(_,y) -> p y) m

  op [a,b] <<< (m1: FMap(a,b), m2: FMap(a,b)) infixl 25 : FMap(a,b) =
    (m1 restrictDomain (fn x -> x nin? domain m2)) \/ m2

  op [a,b] update (m: FMap(a,b)) (x:a) (y:b) : FMap(a,b) = m <<< single (x,y)

  op [a,b] -- (m: FMap(a,b), xS: FSet a) infixl 25 : FMap(a,b) =
    m restrictDomain (fn x -> x nin? xS)

  op [a,b] - (m: FMap(a,b), x:a) infixl 25 : FMap(a,b) = m -- single x

  op [a,b] single (x:a) (y:b) : FMap(a,b) = single (x,y)

  op [a,b] single? (m: FMap(a,b)) : Boolean = FSet.single? m

  type SingletonFMap(a,b) = (FMap(a,b) | single?)

  op [a,b] thePair (m: SingletonFMap(a,b)) : a * b = theMember m

  op [a,b] size (m: FMap(a,b)) : Nat = FSet.size m

  op [a,b,c] foldable? (c:c, f: c * (a*b) -> c, m: FMap(a,b)) : Boolean =
    FSet.foldable? (c, f, m)  % not executable

  op [a,b,c] fold(c: c, f: c * (a*b) -> c, m: FMap(a,b) | foldable?(c,f,m)): c =
    FSet.fold (c, f, m)

  op [a,b] injective? (m: FMap(a,b)) : Boolean =
    size (domain m) = size (range m)

  type InjectiveFMap(a,b) = (FMap(a,b) | injective?)

  op [a,b] inverse (m: InjectiveFMap(a,b)) : InjectiveFMap(b,a) =
    map (fn(x,y) -> (y,x)) m

  op [a,b,c] map (f: b -> c) (m: FMap(a,b)) : FMap(a,c) =
    map (fn(x,y) -> (x, f y)) m

  op [a,b,c] mapWithDomain (f: a * b -> c) (m: FMap(a,b)) : FMap(a,c) =
    map (fn(x,y) -> (x, f(x,y))) m

  op [a,b] toFSet (m: FMap(a,b)) : FSet(a*b) = m

  op fromFSet : [a,b] {s: FSet (a*b) |
                       functional? (fromFSet s)} -> FMap(a,b) = id

  op [a,b] FMap.//\\ (setValuedMap: NonEmptyFMap (a, FSet b)) : FSet b =
    FSet.//\\ (range setValuedMap)

  op [a,b] FMap.\\// (setValuedMap: FMap (a, FSet b)) : FSet b =
    FSet.\\// (range setValuedMap)

  op [a,b] FMap.fromLists
           (domList: InjList a, rngList: List b | domList equiLong rngList)
           : FMap(a,b) = toSet (zip (domList, rngList))

endspec
