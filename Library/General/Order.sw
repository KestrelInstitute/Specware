Order qualifying spec

  import EndoRelation

  % various kinds of orders:

  op preOrder? : [a] EndoRelation a -> Boolean = reflexive? /\ transitive?

  type PreOrder a = (EndoRelation a | preOrder?)

  op partialOrder? : [a] EndoRelation a -> Boolean = preOrder? /\ antisymmetric?

  type PartialOrder a = (EndoRelation a | partialOrder?)

  op weakOrder? : [a] EndoRelation a -> Boolean =
    reflexive? /\ antisymmetric? /\ negativeTransitive?

  type WeakOrder a = (EndoRelation a | weakOrder?)

  op [a] linearOrder? (r: EndoRelation a) : Boolean =
    partialOrder? r &&
    % the following is sometimes called "totality" in the
    % context of orders, but `total?' is already defined in
    % spec `Relation' with a different meaning
    (fa(x,y) r(x,y) || r(y,x))

  type LinearOrder a = (EndoRelation a | linearOrder?)

  theorem orderSubsumption is [a]
    linearOrder?  <= (weakOrder?    : EndoRelation a -> Boolean) &&
    weakOrder?    <= (partialOrder? : EndoRelation a -> Boolean) &&
    partialOrder? <= (preOrder?     : EndoRelation a -> Boolean)

  % make strict version of predicate over endorelations:

  op [a] strict (p: EndoRelation a -> Boolean) (r: EndoRelation a) : Boolean =
    % `r' satisfies strict version of `p' iff:
    irreflexive? r &&       % `r' is irreflexive and
    p (reflexiveClosure r)  % making `r' reflexive satisfies `p'

  op strictPreOrder? : [a] EndoRelation a -> Boolean = strict preOrder?

  type StrictPreOrder a = (EndoRelation a | strictPreOrder?)

  op strictPartialOrder? : [a] EndoRelation a -> Boolean = strict partialOrder?

  type StrictPartialOrder a = (EndoRelation a | strictPartialOrder?)

  op strictWeakOrder? : [a] EndoRelation a -> Boolean = strict weakOrder?

  type StrictWeakOrder a = (EndoRelation a | strictWeakOrder?)

  op strictLinearOrder? : [a] EndoRelation a -> Boolean = strict linearOrder?

  type StrictLinearOrder a = (EndoRelation a | strictLinearOrder?)

  % make reflexive/irreflexive relation irreflexive/reflexive:

  op [a] strictify (r: ReflexiveRelation a) : IrreflexiveRelation a = r -- id

  op unstrictify : [a] IrreflexiveRelation a -> ReflexiveRelation a =
    inverse strictify

endspec
