(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

FMap qualifying
spec 

import Map, Relation, FiniteSet

  % maps as (functional) sets of pairs:
  type FMap(a,b) = (FSet (a * b) | (functional? o fromFSet))

  %% These three are copied from FiniteMap.sw. TODO These cause a
  %% problem with the Isabelle obligations for the morphism (why?).
  %% Maybe these should have the FMap qualifier (??), but the Isabelle
  %% obligations should not cause Isabelle errors in any case.  Is the morphism even valid?
  type SingletonFMap(a,b) = (FMap(a,b) | single?)
  type NonEmptyFMap(a,b) = (FMap(a,b) | nonEmpty?)
  type InjectiveFMap(a,b) = (FMap(a,b) | injective?)


  op toFMap : [a,b] Bijection (FiniteMap(a,b), FMap(a,b)) =
    fn finiteMap: FiniteMap(a,b) -> toFMap finiteMap  % not executable

  op [a,b] fromFMap (m: FMap(a,b)) : FiniteMap(a,b) = fromFMap m

  op [a,b] maps? (m: FMap(a,b)) (x:a) (y:b) : Bool = (x,y) in? m

  op [a,b] domain (m: FMap(a,b)) : FSet a = map (project 1) m

  op [a,b] range (m: FMap(a,b)) : FSet b = map (project 2) m

  op [a,b] definedAt (m: FMap(a,b), x:a) infixl 20 : Bool = x in? domain m

  op [a,b] undefinedAt (m: FMap(a,b), x:a) infixl 20 : Bool =
    x nin? domain m

  op [a,b] @ (m: FMap(a,b), x:a | m definedAt x) infixl 30 : b =
    let xy = FSet.theMember (FSet.filter (fn(x1,_) -> x1 = x) m) in xy.2

  op [a,b] @@ (m: FMap(a,b), x:a) infixl 30 : Option b =
    if m definedAt x then Some (m @ x) else None

  op [a,b] applyi (m: FMap(a,b)) (y:b) : FSet a =
    map (project 1) (FSet.filter (fn(_,y1) -> y1 = y) m)

  op [a,b] applys (m: FMap(a,b)) (xS: FSet a) : FSet b =
    map (project 2) (FSet.filter (fn(x,_) -> x in? xS) m)

  op [a,b] applyis (m: FMap(a,b)) (yS: FSet b) : FSet a =
    map (project 1) (FSet.filter (fn(_,y) -> y in? yS) m)

  op [a] id (dom: FSet a) : FMap(a,a) = map (fn x -> (x,x)) dom

  op [a,b,c] :> (m1: FMap(a,b), m2: FMap(b,c)) infixl 24 : FMap(a,c) =
    let def foldingFunction (m : FMap(a,c), (x,y) : a*b) : FMap(a,c) =
          case m2 @@ y of
            | Some z -> m <| (x,z)
            | None -> m
    in
    FSet.fold (FSet.empty, foldingFunction, m1)

  op [a,b,c] o (m1: FMap(b,c), m2: FMap(a,b)) infixl 24 : FMap(a,c) =
    m2 :> m1

  op [a,b] <= (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
    m1 FSet.<= m2

  op [a,b] < (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
    m1 FSet.< m2

  op [a,b] >= (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
    m1 FSet.>= m2

  op [a,b] > (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
    m1 FSet.> m2

  op empty : [a,b] FMap(a,b) = FSet.empty

  op [a,b] empty? (m: FMap(a,b)) : Bool = FSet.empty? m

  op [a,b] nonEmpty? (m: FMap(a,b)) : Bool = FSet.nonEmpty? m




  op [a,b] forall? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
    FSet.forall? p m

  op [a,b] exists? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
    FSet.exists? p m

  op [a,b] exists1? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
    FSet.exists1? p m

  op [a,b] agree? (m1: FMap(a,b), m2: FMap(a,b)) : Bool =
    forall? (fn(x,y) -> case m2 @@ x of Some y1 -> y1 = y | None -> true) m1

  op [a,b] /\ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 25
              : FMap(a,b) = m1 FSet./\ m2
  %% TODO Try to remove this "proof Isa" line (and similar things
  %% elsewhere).  This is a workaround for an Isabelle translation
  %% issue. (We have two infix operators called /\, one in FiniteSet.sw and
  %% one in this file, and Isabelle can't tell which one we mean when
  %% we call one of them.):
  proof Isa -> FMap_intersection end-proof

  op [a,b] \/ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 24
              : FMap(a,b) = m1 FSet.\/ m2
  %% TODO Remove this eventually. See comment above.
  proof Isa -> FMap_union end-proof

  op [a,b] filter (p: a * b -> Bool) (m: FMap(a,b)) : FMap(a,b) =
    FSet.filter p m

  op [a,b] restrictDomain (m: FMap(a,b), p: a -> Bool) infixl 25
                          : FMap(a,b) = filter (fn(x,_) -> p x) m

  op [a,b] restrictRange (m: FMap(a,b), p: b -> Bool) infixl 25
                         : FMap(a,b) = filter (fn(_,y) -> p y) m

  op [a,b] <<< (m1: FMap(a,b), m2: FMap(a,b)) infixl 25 : FMap(a,b) =
    (m1 restrictDomain (fn x -> x nin? domain m2)) FSet.\/ m2

  op [a,b] update (m: FMap(a,b)) (x:a) (y:b) : FMap(a,b) =
    single (x,y) FSet.\/ (m restrictDomain (fn z -> z ~= x))

% remove domain value(s) from map:
  op [a,b] -- (m: FMap(a,b), xS: FSet a) infixl 25 : FMap(a,b) =
    m restrictDomain (fn x -> x nin? xS)
  %% TODO Remove this eventually. See comment above.
  proof Isa -> FMap_remove_set end-proof

  op [a,b] - (m: FMap(a,b), x:a) infixl 25 : FMap(a,b) = m -- single x

  op [a,b] single (x:a) (y:b) : FMap(a,b) = single (x,y)

  op [a,b] single? (m: FMap(a,b)) : Bool = FSet.single? m

  op [a,b] thePair (m: SingletonFMap(a,b)) : a * b = theMember m

  op [a,b] size (m: FMap(a,b)) : Nat = FSet.size m

  op [a,b,c] foldable? (c:c, f: c * (a*b) -> c, m: FMap(a,b)) : Bool =
    FSet.foldable? (c, f, m)  % not executable

  op [a,b,c] fold(c: c, f: c * (a*b) -> c, m: FMap(a,b) | foldable?(c,f,m)): c =
    FSet.fold (c, f, m)

  op [a,b] injective? (m: FMap(a,b)) : Bool =
    size (domain m) = size (range m)

  op [a,b] inverse (m: InjectiveFMap(a,b)) : InjectiveFMap(b,a) =
    map (fn(x,y) -> (y,x)) m

  op [a,b,c] map (f: b -> c) (m: FMap(a,b)) : FMap(a,c) =
    map (fn(x,y) -> (x, f y)) m

  op [a,b,c] mapWithDomain (f: a * b -> c) (m: FMap(a,b)) : FMap(a,c) =
    map (fn(x,y) -> (x, f(x,y))) m

  op [a,b] toFSet (m: FMap(a,b)) : FSet(a*b) = m

  op fromFSet : [a,b] {s: FSet (a*b) |
                            functional? (fromFSet s)} -> FMap(a,b) = id

  op [a,b] //\\ (setValuedMap: NonEmptyFMap (a, FSet b)) : FSet b =
    FSet.//\\ (range setValuedMap)

  op [a,b] \\// (setValuedMap: FMap (a, FSet b)) : FSet b =
    FSet.\\// (range setValuedMap)

  op [a,b] fromLists
           (domList: InjList a, rngList: List b | domList equiLong rngList)
           : FMap(a,b) = toSet (zip (domList, rngList))

proof isa FMap__toFMap ()
  by (pat_completeness, auto)
  termination
  sorry
end-proof

proof isa FMap__fromFMap ()
  by (pat_completeness, auto)
  termination
  sorry
end-proof

proof Isa FMap__toFMap_Obligation_subtype
  sorry
end-proof

proof Isa FMap__e_at_Obligation_subtype
  sorry
end-proof

proof Isa FMap__id_Obligation_subtype
  sorry
end-proof

proof Isa FMap__e_cl_gt__foldingFunction_Obligation_subtype
  sorry
end-proof

proof Isa FMap__e_cl_gt_Obligation_subtype
  sorry
end-proof

proof Isa FMap__e_cl_gt_Obligation_subtype0
  sorry
end-proof

proof Isa FMap__empty_Obligation_subtype
  sorry
end-proof

proof Isa FMap__e_fsl_bsl_Obligation_subtype
  sorry
end-proof

proof Isa FMap__e_bsl_fsl_Obligation_subtype
  sorry
end-proof

proof Isa FMap__filter_Obligation_subtype
  sorry
end-proof

proof Isa FMap__e_lt_lt_lt_Obligation_subtype
  sorry
end-proof

proof Isa FMap__update_Obligation_subtype
  sorry
end-proof

proof Isa FMap__single_Obligation_subtype
  sorry
end-proof

proof Isa FMap__thePair_Obligation_subtype
  sorry
end-proof

proof Isa FMap__fold_Obligation_subtype
  sorry
end-proof

proof Isa FMap__inverse_Obligation_subtype
  sorry
end-proof

proof Isa FMap__inverse_Obligation_subtype0
  sorry
end-proof

proof Isa FMap__map_Obligation_subtype
  sorry
end-proof

proof Isa FMap__mapWithDomain_Obligation_subtype
  sorry
end-proof

proof Isa FMap__e_fsl_fsl_bsl_bsl_Obligation_subtype
  sorry
end-proof

proof Isa FMap__fromLists_Obligation_subtype
  sorry
end-proof




end-spec
