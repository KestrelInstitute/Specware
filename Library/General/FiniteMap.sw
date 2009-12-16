FMap qualifying spec

(* The motivation for this spec is analogous to the one for spec `FiniteSet';
see comments in that spec.

Some of the operations on maps in spec `Map' involve sets. In this spec, we use
the (refinable) finite sets specified in spec `FiniteSet', otherwise we would be
unable to refine this spec for finite maps. *)

import Map, EndoRelation, FiniteSet

type FMap(a,b)

% isomorphisms:

op toFMap : [a,b] Bijection (FiniteMap(a,b), FMap(a,b))

op fromFMap : [a,b] FMap(a,b) -> FiniteMap(a,b) = inverse toFMap

proof Isa fromFMap_subtype_constr
 sorry
end-proof

proof Isa fromFMap_subtype_constr1
 sorry
end-proof

(* Since `FiniteMap' is a subtype of `Map' which is a subtype of `Relation'
which is a subtype of `Set', it "inherits" ops for maps, (endo)relations, and
sets. Since `FMap(a,b)' is only isomorphic to `FiniteSet(a*b)' (as opposed to
being a subtype), the relevant inherited ops (those that make sense for finite
maps and that can be refined to actual implementations) are introduced here for
type `FMap', and defined using the isomorphism. Some of the inherited ops for
`Relation' and `Set' are renamed here to use names that are more appropriate to
maps vs. relations and sets. *)

% operations and subtypes:

op [a,b] maps? (m: FMap(a,b)) (x:a) (y:b) : Bool = (x,y) in? fromFMap m

op [a,b] domain (m: FMap(a,b)) : FSet a = toFSet (domain (fromFMap m))

proof Isa domain_Obligation_subtype
 sorry
end-proof

op [a,b] range (m: FMap(a,b)) : FSet b = toFSet (range (fromFMap m))

proof Isa range_Obligation_subtype
 sorry
end-proof

op [a,b] definedAt (m: FMap(a,b), x:a) infixl 20 : Bool =
  (fromFMap m) definedAt x
proof Isa -> definedAt_fm end-proof

op [a,b] undefinedAt (m: FMap(a,b), x:a) infixl 20 : Bool =
  (fromFMap m) undefinedAt x
proof Isa -> undefinedAt_fm end-proof

op [a,b] @ (m: FMap(a,b), x:a | m definedAt x) infixl 30 : b =
  (fromFMap m) @ x
proof Isa -> @_fm end-proof

proof Isa e_at_Obligation_subtype
 sorry
end-proof

op [a,b] @@ (m: FMap(a,b), x:a) infixl 30 : Option b = (fromFMap m) @@ x
proof Isa -> @@_fm end-proof

op [a,b] applyi (m: FMap(a,b)) (y:b) : FSet a =
  toFSet (applyi (fromFMap m) y)

proof Isa applyi_Obligation_subtype
 sorry
end-proof

op [a,b] applys (m: FMap(a,b)) (xS: FSet a) : FSet b =
  toFSet (applys (fromFMap m) (fromFSet xS))

proof Isa applys_Obligation_subtype
 sorry
end-proof

op [a,b] applyis (m: FMap(a,b)) (yS: FSet b) : FSet a =
  toFSet (applyis (fromFMap m) (fromFSet yS))

proof Isa applyis_Obligation_subtype
 sorry
end-proof

op [a] id (dom: FSet a) : FMap(a,a) = toFMap (idOver (fromFSet dom))

proof Isa id_Obligation_subtype
 sorry
end-proof

proof Isa id_Obligation_subtype0
 sorry
end-proof

op [a,b,c] :> (m1: FMap(a,b), m2: FMap(b,c)) infixl 24 : FMap(a,c) =
  toFMap (fromFMap m1 :> fromFMap m2)
proof Isa -> :>_fm end-proof

proof Isa e_cl_gt_Obligation_subtype
 sorry
end-proof

proof Isa e_cl_gt_Obligation_subtype0
 sorry
end-proof

op [a,b,c] o (m1: FMap(b,c), m2: FMap(a,b)) infixl 24 : FMap(a,c) =
  toFMap (fromFMap m1 o fromFMap m2)
proof Isa -> o_fm end-proof

proof Isa o_Obligation_subtype
 sorry
end-proof

proof Isa o_Obligation_subtype0
 sorry
end-proof

op [a,b] <= (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
  fromFMap m1 <= fromFMap m2
proof Isa -> <=_fm end-proof

op [a,b] < (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
  fromFMap m1 < fromFMap m2
proof Isa -> <_fm end-proof

op [a,b] >= (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
  fromFMap m1 >= fromFMap m2
proof Isa -> >=_fm end-proof

op [a,b] > (m1: FMap(a,b), m2: FMap(a,b)) infixl 20 : Bool =
  fromFMap m1 > fromFMap m2
proof Isa -> >_fm end-proof

op empty : [a,b] FMap(a,b) = toFMap empty
proof Isa -> empty_fm end-proof

proof Isa empty_Obligation_subtype
 sorry
end-proof

proof Isa empty_Obligation_subtype0
 sorry
end-proof

proof Isa empty_subtype_constr
 sorry
end-proof

op [a,b] empty? (m: FMap(a,b)) : Bool = empty? (fromFMap m)

op [a,b] nonEmpty? (m: FMap(a,b)) : Bool = nonEmpty? (fromFMap m)

type NonEmptyFMap(a,b) = (FMap(a,b) | nonEmpty?)

op [a,b] <<< (m1: FMap(a,b), m2: FMap(a,b)) infixl 25 : FMap(a,b) =
  toFMap (fromFMap m1 <<< fromFMap m2)
proof Isa -> <<<_fm end-proof

proof Isa e_lt_lt_lt_Obligation_subtype
 sorry
end-proof

op [a,b] update (m: FMap(a,b)) (x:a) (y:b) : FMap(a,b) =
  toFMap (update (fromFMap m) x y)

proof Isa update_Obligation_subtype
 sorry
end-proof

op [a,b] -- (m: FMap(a,b), xS: FSet a) infixl 25 : FMap(a,b) =
  toFMap (fromFMap m -- fromFSet xS)
proof Isa -> --_fm end-proof

proof Isa e_dsh_dsh_Obligation_subtype
 sorry
end-proof

op [a,b] - (m: FMap(a,b), x:a) infixl 25 : FMap(a,b) =
  toFMap (fromFMap m - x)
proof Isa -> less_fm end-proof

proof Isa e_dsh_Obligation_subtype
 sorry
end-proof

op [a,b] agree? (m1: FMap(a,b), m2: FMap(a,b)) : Bool =
  agree? (fromFMap m1, fromFMap m2)

op [a,b] /\ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 25
            : FMap(a,b) = toFMap (fromFMap m1 /\ fromFMap m2)
proof Isa -> /\_fm end-proof

proof Isa e_fsl_bsl_Obligation_subtype
 sorry
end-proof

proof Isa e_fsl_bsl_Obligation_subtype0
 sorry
end-proof

op [a,b] \/ (m1: FMap(a,b), m2: FMap(a,b) | agree?(m1,m2)) infixr 24
            : FMap(a,b) = toFMap (fromFMap m1 \/ fromFMap m2)
proof Isa -> \/_fm end-proof

proof Isa e_bsl_fsl_Obligation_subtype
 sorry
end-proof

proof Isa e_bsl_fsl_Obligation_subtype0
 sorry
end-proof

op [a,b] forall? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
  fromFMap m <= p

op [a,b] exists? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
  nonEmpty? (fromFMap m /\ p)

op [a,b] exists1? (p: a * b -> Bool) (m: FMap(a,b)) : Bool =
  single? (fromFMap m /\ p)

op [a,b] filter (p: a * b -> Bool) (m: FMap(a,b)) : FMap(a,b) =
  toFMap (fromFMap m /\ p)

proof Isa filter_Obligation_subtype
 sorry
end-proof

proof Isa filter_Obligation_subtype0
 sorry
end-proof

op [a,b] restrictDomain (m: FMap(a,b), p: a -> Bool) infixl 25
                        : FMap(a,b) = toFMap (fromFMap m restrictDomain p)
proof Isa -> restrictDomain_fm end-proof

proof Isa restrictDomain_Obligation_subtype
 sorry
end-proof

proof Isa restrictDomain_Obligation_subtype0
 sorry
end-proof

op [a,b] restrictRange (m: FMap(a,b), p: b -> Bool) infixl 25
                       : FMap(a,b) = toFMap (fromFMap m restrictRange p)
proof Isa -> restrictRange_fm end-proof

proof Isa restrictRange_Obligation_subtype
 sorry
end-proof

proof Isa restrictRange_Obligation_subtype0
 sorry
end-proof

op [a,b] single (x:a) (y:b) : FMap(a,b) = toFMap (single (x,y))

proof Isa single_Obligation_subtype
 sorry
end-proof

proof Isa single_Obligation_subtype0
 sorry
end-proof

proof Isa single_subtype_constr
 sorry
end-proof

op [a,b] single? (m: FMap(a,b)) : Bool = single? (fromFMap m)

type SingletonFMap(a,b) = (FMap(a,b) | single?)

op [a,b] thePair (m: SingletonFMap(a,b)) : a * b = theMember (fromFMap m)

op [a,b] size (m: FMap(a,b)) : Nat = size (fromFMap m)

op [a,b,c] foldable? (c:c, f: c * (a*b) -> c, m: FMap(a,b)) : Bool =
  foldable? (c, f, fromFMap m)

op [a,b,c] fold(c: c, f: c * (a*b) -> c, m: FMap(a,b) | foldable?(c,f,m)): c =
  fold (c, f, fromFMap m)

proof Isa fold_Obligation_subtype
 sorry
end-proof

op [a,b] injective? (m: FMap(a,b)) : Bool =
  Relation.injective? (fromFMap m)

type InjectiveFMap(a,b) = (FMap(a,b) | injective?)

op [a,b] inverse (m: InjectiveFMap(a,b)) : InjectiveFMap(b,a) =
  toFMap (inverse (fromFMap m))

proof Isa inverse__stp_subtype_constr
 sorry
end-proof

proof Isa inverse_Obligation_subtype
 sorry
end-proof

proof Isa inverse_Obligation_subtype0
 sorry
end-proof

proof Isa inverse_Obligation_subtype1
 sorry
end-proof

proof Isa inverse_subtype_constr
 sorry
end-proof

% apply function to all range values:
op [a,b,c] map (f: b -> c) (m: FMap(a,b)) : FMap(a,c) =
  let fLiftedToPairs: a * b -> a * c = (fn (x,y) -> (x, f y)) in
  toFMap (map fLiftedToPairs (fromFMap m))

proof Isa map_Obligation_subtype
 sorry
end-proof

proof Isa map_Obligation_subtype0
 sorry
end-proof

% like previous op but also include domain value:
op [a,b,c] mapWithDomain (f: a * b -> c) (m: FMap(a,b)) : FMap(a,c) =
  let fLiftedToPairs: a * b -> a * c = (fn (x,y) -> (x, f(x,y))) in
  toFMap (map fLiftedToPairs (fromFMap m))

proof Isa mapWithDomain_Obligation_subtype
 sorry
end-proof

proof Isa mapWithDomain_Obligation_subtype0
 sorry
end-proof

(* While `FiniteMap(a,b)' is a subtype of `FiniteSet(a*b)', the types
`FMap(a,b)' and `FSet(a*b)' are just isomorphic. So, we provide explicit
conversions here. *)

op [a,b] toFSet (m: FMap(a,b)) : FSet(a*b) = toFSet (fromFMap m)

op [a,b] fromFSet (s : FSet(a*b) | functional? (fromFSet s)) : FMap(a,b) =
  toFMap (fromFSet s)

% intersection of all sets in a map's range:

op [a,b] //\\ (setValuedMap: NonEmptyFMap (a, FSet b)) : FSet b =
  FSet.//\\ (range setValuedMap)

proof Isa e_fsl_fsl_bsl_bsl_Obligation_subtype
 sorry
end-proof

% union of all sets in a map's range:

op [a,b] \\// (setValuedMap: FMap (a, FSet b)) : FSet b =
  FSet.\\// (range setValuedMap)

% construct map x1->y1,...,xn->yn from lists x1,...,xn and y1,...,yn:

op [a,b] fromLists
         (domList: InjList a, rngList: List b | domList equiLong rngList)
         : FMap(a,b) =
  toFMap (fn (x,y) ->
    (ex(i:Nat) i < length domList && domList @ i = x && y = rngList @ i))

proof Isa fromLists_Obligation_subtype
 sorry
end-proof

proof Isa fromLists_Obligation_subtype0
 sorry
end-proof

proof Isa fromLists_Obligation_subtype1
 sorry
end-proof

proof Isa fromLists_subtype_constr
 sorry
end-proof

endspec
