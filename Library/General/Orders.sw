Order qualifying spec

  import EndoRelations

  op preOrder? : [a] EndoRelation a -> Boolean
  def preOrder? = reflexive? /\ transitive?

  type PreOrder a = (EndoRelation a | preOrder?)

  op partialOrder? : [a] EndoRelation a -> Boolean
  def partialOrder? = preOrder? /\ antisymmetric?

  type PartialOrder a = (EndoRelation a | partialOrder?)

  op weakOrder? : [a] EndoRelation a -> Boolean
  def weakOrder? = reflexive? /\ antisymmetric? /\ negativeTransitive?

  type WeakOrder a = (EndoRelation a | weakOrder?)

  op linearOrder? : [a] EndoRelation a -> Boolean
  def linearOrder? r = partialOrder? r &&
                       % the following is sometimes called "totality" in the
                       % context of orders, but `total?' is already defined in
                       % spec `Relations' with a different meaning
                       (fa(x,y) r(x,y) || r(y,x))

  type LinearOrder a = (EndoRelation a | linearOrder?)

  conjecture orderSubsumption is
    linearOrder?  <= weakOrder?  &&
    weakOrder?    <= partialOrder? &&
    partialOrder? <= preOrder?

  % make strict version of predicate over endorelations:
  op strict : [a] (EndoRelation a -> Boolean) -> EndoRelation a -> Boolean
  def strict p r =          % `r' satisfies strict version of `p' iff:
    irreflexive? r &&       % `r' is irreflexive and
    p (reflexiveClosure r)  % making `r' reflexive satisfies `p'

  op strictPreOrder? : [a] EndoRelation a -> Boolean
  def strictPreOrder? = strict preOrder?

  type StrictPreOrder a = (EndoRelation a | strictPreOrder?)

  op strictPartialOrder? : [a] EndoRelation a -> Boolean
  def strictPartialOrder? = strict partialOrder?

  type StrictPartialOrder a = (EndoRelation a | strictPartialOrder?)

  op strictWeakOrder? : [a] EndoRelation a -> Boolean
  def strictWeakOrder? = strict weakOrder?

  type StrictWeakOrder a = (EndoRelation a | strictWeakOrder?)

  op strictLinearOrder? : [a] EndoRelation a -> Boolean
  def strictLinearOrder? = strict linearOrder?

  type StrictLinearOrder a = (EndoRelation a | strictLinearOrder?)

  % make reflexive relation irreflexive:
  op strictify : [a] ReflexiveRelation a -> IrreflexiveRelation a
  def strictify r = r -- id

  % make irreflexive relation reflexive:
  op unstrictify : [a] IrreflexiveRelation a -> ReflexiveRelation a
  def unstrictify = inverse strictify

endspec
