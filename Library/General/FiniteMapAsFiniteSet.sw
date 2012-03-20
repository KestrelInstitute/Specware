refine FiniteMap by {

  % maps as (functional) sets of pairs:
  type FMap.FMap(a,b) = (FSet (a * b) | (functional? o fromFSet))

  op FMap.toFMap : [a,b] Bijection (FiniteMap(a,b), FMap(a,b)) =
    fn finiteMap: FiniteMap(a,b) -> toFMap finiteMap  % not executable

  op [a,b] FMap.fromFMap (m: FMap(a,b)) : FiniteMap(a,b) = fromFMap m

  op [a,b] FMap.maps? (m: FMap(a,b)) (x:a) (y:b) : Bool = (x,y) in? m

  op [a,b] FMap.domain (m: FMap(a,b)) : FSet a = map (project 1) m

  op [a,b] FMap.range (m: FMap(a,b)) : FSet b = map (project 2) m

  op [a,b] FMap.definedAt (m: FMap(a,b), x:a) infixl 20 : Bool = x in? domain m

  op [a,b] FMap.undefinedAt (m: FMap(a,b), x:a) infixl 20 : Bool =
    x nin? domain m

  op [a,b] FMap.@ (m: FMap(a,b), x:a | m definedAt x) infixl 30 : b =
    let xy = FSet.theMember (FSet.filter (fn(x1,_) -> x1 = x) m) in xy.2

  op [a,b] FMap.@@ (m: FMap(a,b), x:a) infixl 30 : Option b =
    if m definedAt x then Some (m @ x) else None

  op [a,b] FMap.applyi (m: FMap(a,b)) (y:b) : FSet a =
    map (project 1) (FSet.filter (fn(_,y1) -> y1 = y) m)

  op [a,b] FMap.applys (m: FMap(a,b)) (xS: FSet a) : FSet b =
    map (project 2) (FSet.filter (fn(x,_) -> x in? xS) m)

  op [a,b] FMap.applyis (m: FMap(a,b)) (yS: FSet b) : FSet a =
    map (project 1) (FSet.filter (fn(_,y) -> y in? yS) m)

  op [a] FMap.id (dom: FSet a) : FMap(a,a) = map (fn x -> (x,x)) dom

  op [a,b,c] FMap.:> (m1: FMap(a,b), m2: FMap(b,c)) infixl 24 : FMap(a,c) =
    let def foldingFunction (m : FMap(a,c), (x,y) : a*b) : FMap(a,c) =
          case m2 @@ y of
            | Some z -> m <| (x,z)
            | None -> m
    in
    FSet.fold (FSet.empty, foldingFunction, m1)

  op [a,b,c] FMap.o (m1: FMap(b,c), m2: FMap(a,b)) infixl 24 : FMap(a,c) =
    m2 :> m1

  op [a,b] FMap.<= (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
    m1 FSet.<= m2

  op [a,b] FMap.< (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
    m1 FSet.< m2

  op [a,b] FMap.>= (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
    m1 FSet.>= m2

  op [a,b] FMap.> (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
    m1 FSet.> m2

  op FMap.empty : [a,b] FMap(a,b) = FSet.empty

  op [a,b] FMap.empty? (m: FMap(a,b)) : Bool = FSet.empty? m

  op [a,b] FMap.nonEmpty? (m: FMap(a,b)) : Bool = FSet.nonEmpty? m


  op [a,b] FMap.forall? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
    FSet.forall? p m

  op [a,b] FMap.exists? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
    FSet.exists? p m

  op [a,b] FMap.exists1? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
    FSet.exists1? p m

  op [a,b] FMap.agree? (m1: FMap(a,b), m2: FMap(a,b)) : Bool =
    forall? (fn(x,y) -> case m2 @@ x of Some y1 -> y1 = y | None -> true) m1

  op [a,b] FMap./\ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 25
              : FMap(a,b) = m1 FSet./\ m2

  op [a,b] FMap.\/ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 24
              : FMap(a,b) = m1 FSet.\/ m2

  op [a,b] FMap.filter (p: a * b -> Bool) (m: FMap(a,b)) : FMap(a,b) =
    FSet.filter p m

  op [a,b] FMap.restrictDomain (m: FMap(a,b), p: a -> Bool) infixl 25
                          : FMap(a,b) = filter (fn(x,_) -> p x) m

  op [a,b] FMap.restrictRange (m: FMap(a,b), p: b -> Bool) infixl 25
                         : FMap(a,b) = filter (fn(_,y) -> p y) m

  op [a,b] FMap.<<< (m1: FMap(a,b), m2: FMap(a,b)) infixl 25 : FMap(a,b) =
    (m1 restrictDomain (fn x -> x nin? domain m2)) FSet.\/ m2

  op [a,b] FMap.update (m: FMap(a,b)) (x:a) (y:b) : FMap(a,b) =
    single (x,y) FSet.\/ (m restrictDomain (fn z -> z ~= x))

  op [a,b] FMap.-- (m: FMap(a,b), xS: FSet a) infixl 25 : FMap(a,b) =
    m restrictDomain (fn x -> x nin? xS)

  op [a,b] FMap.- (m: FMap(a,b), x:a) infixl 25 : FMap(a,b) = m -- single x

  op [a,b] FMap.single (x:a) (y:b) : FMap(a,b) = single (x,y)

  op [a,b] FMap.single? (m: FMap(a,b)) : Bool = FSet.single? m


  op [a,b] FMap.thePair (m: SingletonFMap(a,b)) : a * b = theMember m

  op [a,b] FMap.size (m: FMap(a,b)) : Nat = FSet.size m

  op [a,b,c] FMap.foldable? (c:c, f: c * (a*b) -> c, m: FMap(a,b)) : Bool =
    FSet.foldable? (c, f, m)  % not executable

  op [a,b,c] FMap.fold(c: c, f: c * (a*b) -> c, m: FMap(a,b) | foldable?(c,f,m)): c =
    FSet.fold (c, f, m)

  op [a,b] FMap.injective? (m: FMap(a,b)) : Bool =
    size (domain m) = size (range m)

  op [a,b] FMap.inverse (m: InjectiveFMap(a,b)) : InjectiveFMap(b,a) =
    map (fn(x,y) -> (y,x)) m

  op [a,b,c] FMap.map (f: b -> c) (m: FMap(a,b)) : FMap(a,c) =
    map (fn(x,y) -> (x, f y)) m

  op [a,b,c] FMap.mapWithDomain (f: a * b -> c) (m: FMap(a,b)) : FMap(a,c) =
    map (fn(x,y) -> (x, f(x,y))) m

  op [a,b] FMap.toFSet (m: FMap(a,b)) : FSet(a*b) = m

  op FMap.fromFSet : [a,b] {s: FSet (a*b) |
                            functional? (fromFSet s)} -> FMap(a,b) = id

  op [a,b] FMap.//\\ (setValuedMap: NonEmptyFMap (a, FSet b)) : FSet b =
    FSet.//\\ (range setValuedMap)

  op [a,b] FMap.\\// (setValuedMap: FMap (a, FSet b)) : FSet b =
    FSet.\\// (range setValuedMap)

  op [a,b] FMap.fromLists
           (domList: InjList a, rngList: List b | domList equiLong rngList)
           : FMap(a,b) = toSet (zip (domList, rngList))

}
