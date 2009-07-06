FSet qualifying spec

(* The spec `Set' defines a subtype `FiniteSet' for finite sets. In principle,
that subtype could be used in specs and then refined, e.g. in terms of lists, to
obtain an executable implementation. In practice, currently Specware requires
morphisms, which are used to express refinement, to map subtypes to subtypes.

For this reason, we introduce here an "alternative" type for finite sets, called
`FSet', and constrain it to be isomorphic to type `FiniteSet'.  Operations on
`FSet' are defined in terms of the isomorphism and of operations in spec `Set'.

By not equating type `FSet' to any other type (we only constrain it to be
isomorphic to type `FiniteSet'), we leave the possibility open to refine it,
e.g. in terms of lists, using current Specware morphisms. All operations
introduced here can be refined, except the isomorphisms. Users of this spec
should not use the isomorphisms, which are only used here internally to
constrain type `FSet'. *)

import Set

type FSet a

% isomorphisms:

op toFSet : [a] Bijection (FiniteSet a, FSet a)

op fromFSet : [a] FSet a -> FiniteSet a = inverse toFSet

proof Isa fromFSet_subtype_constr
 sorry
end-proof

% operations and subtypes (see spec `Set'):

op [a] in? (x:a, s: FSet a) infixl 20 : Bool = x in? fromFSet s
proof Isa -> in_fset? end-proof

op [a] nin? (x:a, s: FSet a) infixl 20 : Bool = x nin? fromFSet s
proof Isa -> nin_fset? end-proof

op [a] <= (s1: FSet a, s2: FSet a) infixl 20 : Bool =
  fromFSet s1 <= fromFSet s2
proof Isa -> <=_fset? end-proof

op [a] < (s1: FSet a, s2: FSet a) infixl 20 : Bool =
  fromFSet s1 < fromFSet s2
proof Isa -> <_fset? end-proof

op [a] >= (s1: FSet a, s2: FSet a) infixl 20 : Bool =
  fromFSet s1 >= fromFSet s2
proof Isa -> >=_fset? end-proof

op [a] > (s1: FSet a, s2: FSet a) infixl 20 : Bool =
  fromFSet s1 > fromFSet s2
proof Isa -> >_fset? end-proof

op [a] /\ (s1: FSet a, s2: FSet a) infixr 25 : FSet a =
  toFSet (fromFSet s1 /\ fromFSet s2)

proof Isa e_fsl_bsl__stp_Obligation_subtype
 sorry
end-proof

proof Isa e_fsl_bsl_Obligation_subtype
 sorry
end-proof

op [a] \/ (s1: FSet a, s2: FSet a) infixr 24 : FSet a =
  toFSet (fromFSet s1 \/ fromFSet s2)

proof Isa e_bsl_fsl__stp_Obligation_subtype
 sorry
end-proof

proof Isa e_bsl_fsl_Obligation_subtype
 sorry
end-proof

op [a] -- (s1: FSet a, s2: FSet a) infixl 25 : FSet a =
  toFSet (fromFSet s1 -- fromFSet s2)
proof Isa -> --_fs end-proof

proof Isa e_dsh_dsh__stp_Obligation_subtype
 sorry
end-proof

proof Isa e_dsh_dsh_Obligation_subtype
 sorry
end-proof

op [a,b] * (s1: FSet a, s2: FSet b) infixl 27 : FSet (a * b) =
  toFSet (fromFSet s1 * fromFSet s2)
proof Isa -> *_fset? end-proof

proof Isa e_ast__stp_Obligation_subtype
 sorry
end-proof

proof Isa e_ast_Obligation_subtype
 sorry
end-proof

op [a] power (s: FSet a) : FSet (FSet a) =
  toFSet (map toFSet (power (fromFSet s)))

proof Isa power__stp_Obligation_subtype
 sorry
end-proof

proof Isa power_Obligation_subtype
 sorry
end-proof

op empty : [a] FSet a = toFSet empty
proof Isa -> empty_fset_p end-proof

proof Isa empty_subtype_constr
 sorry
end-proof

op [a] empty? (s: FSet a) : Bool = empty? (fromFSet s)

op [a] nonEmpty? (s: FSet a) : Bool = nonEmpty? (fromFSet s)

type NonEmptyFSet a = (FSet a | nonEmpty?)

op [a] single (x:a) : FSet a = toFSet (single x)

proof Isa single_subtype_constr
 sorry
end-proof

op [a] single? (s: FSet a) : Bool = single? (fromFSet s)

op [a] onlyMemberOf (x:a, s: FSet a) infixl 20 : Bool =
  x onlyMemberOf (fromFSet s)
proof Isa -> onlyMemberOf_fs end-proof

type SingletonFSet a = (FSet a | single?)

op [a] theMember (s: SingletonFSet a) : a = theMember (fromFSet s)

op [a] <| (s: FSet a, x:a) infixl 25 : FSet a = toFSet (fromFSet s <| x)
proof Isa -> with_fs [simp] end-proof

proof Isa theMember__stp_Obligation_subtype
 sorry
end-proof

proof Isa e_lt_bar__stp_Obligation_subtype
 sorry
end-proof

proof Isa e_lt_bar_Obligation_subtype
 sorry
end-proof

op [a] - (s: FSet a, x:a) infixl 25 : FSet a = toFSet (fromFSet s - x)
proof Isa -> -_fset? end-proof

proof Isa e_dsh__stp_Obligation_subtype
 sorry
end-proof

proof Isa e_dsh_Obligation_subtype
 sorry
end-proof

op [a,b] map (f: a -> b) (s: FSet a) : FSet b = toFSet (map f (fromFSet s))

proof Isa map__stp_Obligation_subtype
 sorry
end-proof

proof Isa map_Obligation_subtype
 sorry
end-proof

op [a,b] FSet.mapPartial (f: a -> Option b) (s: FSet a) : FSet b =
  toFSet (Set.mapPartial f (fromFSet s):FiniteSet(b))

proof Isa mapPartial__stp_Obligation_subtype
 sorry
end-proof

proof Isa mapPartial_Obligation_subtype
 sorry
end-proof

op [a] size (s: FSet a) : Nat = size (fromFSet s)

op [a,b] foldable? (c: b, f: b * a -> b, s: FSet a) : Bool =
  foldable? (c, f, fromFSet s)

op [a,b] fold (c: b, f: b * a -> b, s: FSet a | foldable?(c,f,s)) : b =
  fold (c, f, fromFSet s)

proof Isa fold__stp_Obligation_subtype
 sorry
end-proof

proof Isa fold_Obligation_subtype
 sorry
end-proof

op powerf : [a] FSet a -> FSet (FSet a) = power

% we must strengthen the domain to non-empty sets of sets,
% because in spec `Set' we have `//\\ empty = full':
op [a] //\\ (ss: NonEmptyFSet (FSet a)) : FSet a =
  toFSet (//\\ (map fromFSet (fromFSet ss)))

proof Isa e_fsl_fsl_bsl_bsl__stp_Obligation_subtype0
 sorry
end-proof

proof Isa e_fsl_fsl_bsl_bsl_Obligation_subtype0
 sorry
end-proof

op [a] \\// (ss: FSet (FSet a)) : FSet a =
  toFSet (\\// (map fromFSet (fromFSet ss)))

proof Isa e_bsl_bsl_fsl_fsl__stp_Obligation_subtype
 sorry
end-proof

proof Isa e_bsl_bsl_fsl_fsl_Obligation_subtype
 sorry
end-proof

op [a] forall? (p: a -> Bool) (s: FSet a) : Bool = fromFSet s <= p

op [a] exists? (p: a -> Bool) (s: FSet a) : Bool =
  nonEmpty? (fromFSet s /\ p)

op [a] exists1? (p: a -> Bool) (s: FSet a) : Bool =
  single? (fromFSet s /\ p)

op [a] filter (p: a -> Bool) (s: FSet a) : FSet a =
  toFSet (fromFSet s /\ p)

proof Isa filter__stp_Obligation_subtype
 sorry
end-proof

proof Isa filter_Obligation_subtype
 sorry
end-proof

% convert list to set:

op [a] List.toSet (l: List a) : FSet a = toFSet (fn x -> x in? l)

proof Isa List__toSet__stp_Obligation_subtype
 sorry
end-proof

proof Isa List__toSet__stp_Obligation_subtype0
 sorry
end-proof

proof Isa List__toSet_Obligation_subtype
 sorry
end-proof

% intersection of all sets contained in a list:

op [a] List.//\\ (ls: List1 (FSet a)) : FSet a = //\\ (toSet ls)

proof Isa e_fsl_fsl_bsl_bsl__stp_Obligation_subtype
 sorry
end-proof

proof Isa e_fsl_fsl_bsl_bsl_Obligation_subtype
 sorry
end-proof


% union of all sets contained in a list:

op [a] List.\\// (ls: List (FSet a)) : FSet a = \\// (toSet ls)

endspec
