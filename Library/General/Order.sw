Order qualifying spec

import EndoRelation

%%% Generate stp version of orderSubsumption in case it is useful later
proof Isa -stp-theorems end-proof

% various kinds of orders:

op preOrder? : [a] EndoRelation a -> Bool = reflexive? /\ transitive?

type PreOrder a = (EndoRelation a | preOrder?)

op partialOrder? : [a] EndoRelation a -> Bool = preOrder? /\ antisymmetric?

type PartialOrder a = (EndoRelation a | partialOrder?)

op weakOrder? : [a] EndoRelation a -> Bool =
  reflexive? /\ antisymmetric? /\ negativeTransitive?

type WeakOrder a = (EndoRelation a | weakOrder?)

op [a] linearOrder? (r: EndoRelation a) : Bool =
  partialOrder? r &&
  % the following is sometimes called "totality" in the
  % context of orders, but `total?' is already defined in
  % spec `Relation' with a different meaning
  (fa(x,y) r(x,y) || r(y,x))

type LinearOrder a = (EndoRelation a | linearOrder?)

theorem orderSubsumption is [a]
  linearOrder?  <= (weakOrder?    : EndoRelation a -> Bool) &&
  weakOrder?    <= (partialOrder? : EndoRelation a -> Bool) &&
  partialOrder? <= (preOrder?     : EndoRelation a -> Bool)

proof Isa orderSubsumption__stp
 sorry
end-proof

proof Isa orderSubsumption
 sorry
end-proof

% make strict version of predicate over endorelations:

op [a] strict (p: EndoRelation a -> Bool) (r: EndoRelation a) : Bool =
  % `r' satisfies strict version of `p' iff:
  irreflexive? r &&       % `r' is irreflexive and
  p (reflexiveClosure r)  % making `r' reflexive satisfies `p'

op strictPreOrder? : [a] EndoRelation a -> Bool = strict preOrder?

type StrictPreOrder a = (EndoRelation a | strictPreOrder?)

op strictPartialOrder? : [a] EndoRelation a -> Bool = strict partialOrder?

type StrictPartialOrder a = (EndoRelation a | strictPartialOrder?)

op strictWeakOrder? : [a] EndoRelation a -> Bool = strict weakOrder?

type StrictWeakOrder a = (EndoRelation a | strictWeakOrder?)

op strictLinearOrder? : [a] EndoRelation a -> Bool = strict linearOrder?

type StrictLinearOrder a = (EndoRelation a | strictLinearOrder?)

% make reflexive/irreflexive relation irreflexive/reflexive:

op [a] strictify (r: ReflexiveRelation a) : IrreflexiveRelation a = r -- id

proof Isa strictify_Obligation_subtype
 sorry
end-proof

proof Isa strictify_subtype_constr
 sorry
end-proof

proof Isa strictify_subtype_constr1
 sorry
end-proof

proof Isa strictify_subtype_constr2
 sorry
end-proof

op unstrictify : [a] IrreflexiveRelation a -> ReflexiveRelation a =
  inverse strictify

proof Isa unstrictify_Obligation_subtype
 sorry
end-proof

proof Isa unstrictify_subtype_constr
 sorry
end-proof

endspec
