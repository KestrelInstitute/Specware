EndoRelation qualifying spec

  import Relations

  type EndoRelation a = Relation(a,a)

  % identity:
  op id : [a] EndoRelation a
  def id = (=)

  % identity over given domain:
  op idOver : [a] Set a -> EndoRelation a
  def idOver s = s * s

  op reflexive? : [a] EndoRelation a -> Boolean
  def reflexive? r = (fa(x) r(x,x))

  type ReflexiveRelation a = (EndoRelation a | reflexive?)

  op irreflexive? : [a] EndoRelation a -> Boolean
  def irreflexive? r = (fa(x) ~~r(x,x))

  type IrreflexiveRelation a = (EndoRelation a | irreflexive?)

  op symmetric? : [a] EndoRelation a -> Boolean
  def symmetric? r = (fa(x,y) r(x,y) => r(y,x))

  type SymmetricRelation a = (EndoRelation a | symmetric?)

  op antisymmetric? : [a] EndoRelation a -> Boolean
  def antisymmetric? r = (fa(x,y) r(x,y) && r(y,x) => x = y)

  type AntisymmetricRelation a = (EndoRelation a | antisymmetric?)

  op asymmetric? : [a] EndoRelation a -> Boolean
  def asymmetric? r = (fa(x,y) ~ (r(x,y) && r(y,x)))

  type AsymmetricRelation a = (EndoRelation a | asymmetric?)

  op transitive? : [a] EndoRelation a -> Boolean
  def transitive? r = (fa(x,y,z) r(x,y) && r(y,z) => r(x,z))

  type TransitiveRelation a = (EndoRelation a | transitive?)

  op negativeTransitive? : [a] EndoRelation a -> Boolean
  def negativeTransitive? r = (fa(x,y,z) ~~r(x,y) && ~~r(y,z) => ~~r(x,z))

  type NegativeTransitiveRelation a = (EndoRelation a | negativeTransitive?)

  op trichotomous? : [a] EndoRelation a -> Boolean
  def trichotomous? r =
    % exactly one of `r(x,y)', `r(y,x)', and `x = y' holds:
    (fa(x,y) r(x,y) && ~~r(y,x) && x ~= y
        || ~~r(x,y) &&   r(y,x) && x ~= y
        || ~~r(x,y) && ~~r(y,x) && x  = y)

  type TrichotomousRelation a = (EndoRelation a | trichotomous?)

  op equivalence? : [a] EndoRelation a -> Boolean
  def equivalence? = reflexive? /\ symmetric? /\ transitive?

  type Equivalence a = (EndoRelation a | equivalence?)

  op reflexiveClosure : [a] EndoRelation a -> ReflexiveRelation a
  def reflexiveClosure r = min (fn rc -> r <= rc && reflexive? rc)

  op symmetricClosure : [a] EndoRelation a -> SymmetricRelation a
  def symmetricClosure r = min (fn rc -> r <= rc && symmetric? rc)

  op transitiveClosure : [a] EndoRelation a -> TransitiveRelation a
  def transitiveClosure r = min (fn rc -> r <= rc && transitive? rc)

  op equivalenceClosure : [a] EndoRelation a -> Equivalence a
  def equivalenceClosure r = min (fn rc -> r <= rc && equivalence? rc)

endspec
