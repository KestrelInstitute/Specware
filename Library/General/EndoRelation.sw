EndoRelation qualifying spec

import Relation

type EndoRelation a = Relation(a,a)

% identity:

op id : [a] EndoRelation a = (=)

% identity over given domain:

op [a] idOver (s: Set a) : EndoRelation a = s * s

% various properties of endorelations:

op [a] reflexive? (r: EndoRelation a) : Bool = (fa(x) r(x,x))

type ReflexiveRelation a = (EndoRelation a | reflexive?)

op [a] irreflexive? (r: EndoRelation a) : Bool = (fa(x) ~~r(x,x))

type IrreflexiveRelation a = (EndoRelation a | irreflexive?)

op [a] symmetric? (r: EndoRelation a) : Bool = (fa(x,y) r(x,y) => r(y,x))

type SymmetricRelation a = (EndoRelation a | symmetric?)

op [a] antisymmetric? (r: EndoRelation a) : Bool =
  fa(x,y) r(x,y) && r(y,x) => x = y

type AntisymmetricRelation a = (EndoRelation a | antisymmetric?)

op [a] asymmetric? (r: EndoRelation a) : Bool =
  fa(x,y) ~ (r(x,y) && r(y,x))

type AsymmetricRelation a = (EndoRelation a | asymmetric?)

op [a] transitive? (r: EndoRelation a) : Bool =
  fa(x,y,z) r(x,y) && r(y,z) => r(x,z)

type TransitiveRelation a = (EndoRelation a | transitive?)

op [a] negativeTransitive? (r: EndoRelation a) : Bool =
  fa(x,y,z) ~~r(x,y) && ~~r(y,z) => ~~r(x,z)

type NegativeTransitiveRelation a = (EndoRelation a | negativeTransitive?)

op [a] trichotomous? (r: EndoRelation a) : Bool =
  % exactly one of `r(x,y)', `r(y,x)', and `x = y' holds:
  fa(x,y) r(x,y) && ~~r(y,x) && x ~= y
     || ~~r(x,y) &&   r(y,x) && x ~= y
     || ~~r(x,y) && ~~r(y,x) && x  = y

type TrichotomousRelation a = (EndoRelation a | trichotomous?)

op equivalence? : [a] EndoRelation a -> Bool =
  reflexive? /\ symmetric? /\ transitive?

type Equivalence a = (EndoRelation a | equivalence?)

op partialEquivalence? : [a] EndoRelation a -> Bool =
  symmetric? /\ transitive?

type PartialEquivalence a = (EndoRelation a | partialEquivalence?)

op [a] wellFounded? (r: EndoRelation a) : Bool =
  % each non-empty predicate:
  fa (p: a -> Bool) (ex(y:a) p y) =>
  % has a minimal element w.r.t. the relation:
    (ex(y:a) p y && (fa(x:a) p x => ~ (r(x,y))))

type WellFoundedRelation a = (EndoRelation a | wellFounded?)

% closure operators:

op [a] reflexiveClosure (r: EndoRelation a) : ReflexiveRelation a =
  min (fn rc -> r <= rc && reflexive? rc)

op [a] symmetricClosure (r: EndoRelation a) : SymmetricRelation a =
  min (fn rc -> r <= rc && symmetric? rc)

op [a] transitiveClosure (r: EndoRelation a) : TransitiveRelation a =
  min (fn rc -> r <= rc && transitive? rc)

op [a] equivalenceClosure (r: EndoRelation a) : Equivalence a =
  min (fn rc -> r <= rc && equivalence? rc)

proof Isa reflexiveClosure_Obligation_subtype
 sorry
end-proof

proof Isa reflexiveClosure_Obligation_subtype0
 sorry
end-proof

proof Isa reflexiveClosure_subtype_constr
 sorry
end-proof

proof Isa symmetricClosure_Obligation_subtype
 sorry
end-proof

proof Isa symmetricClosure_Obligation_subtype0
 sorry
end-proof

proof Isa symmetricClosure_subtype_constr
 sorry
end-proof

proof Isa transitiveClosure_Obligation_subtype
 sorry
end-proof

proof Isa transitiveClosure_Obligation_subtype0
 sorry
end-proof

proof Isa transitiveClosure_subtype_constr
 sorry
end-proof

proof Isa equivalenceClosure_Obligation_subtype
 sorry
end-proof

proof Isa equivalenceClosure_Obligation_subtype0
 sorry
end-proof

proof Isa equivalenceClosure_subtype_constr
 sorry
end-proof

endspec
