EndoRelation qualifying spec

  import Relations

  type EndoRelation a = Relation(a,a)

  % identity:

  op id : [a] EndoRelation a = (=)

  % identity over given domain:

  op [a] idOver (s: Set a) : EndoRelation a = s * s

  % various properties of endorelations:

  op [a] reflexive? (r: EndoRelation a) : Boolean = (fa(x) r(x,x))

  type ReflexiveRelation a = (EndoRelation a | reflexive?)

  op [a] irreflexive? (r: EndoRelation a) : Boolean = (fa(x) ~~r(x,x))

  type IrreflexiveRelation a = (EndoRelation a | irreflexive?)

  op [a] symmetric? (r: EndoRelation a) : Boolean = (fa(x,y) r(x,y) => r(y,x))

  type SymmetricRelation a = (EndoRelation a | symmetric?)

  op [a] antisymmetric? (r: EndoRelation a) : Boolean =
    fa(x,y) r(x,y) && r(y,x) => x = y

  type AntisymmetricRelation a = (EndoRelation a | antisymmetric?)

  op [a] asymmetric? (r: EndoRelation a) : Boolean =
    fa(x,y) ~ (r(x,y) && r(y,x))

  type AsymmetricRelation a = (EndoRelation a | asymmetric?)

  op [a] transitive? (r: EndoRelation a) : Boolean =
    fa(x,y,z) r(x,y) && r(y,z) => r(x,z)

  type TransitiveRelation a = (EndoRelation a | transitive?)

  op [a] negativeTransitive? (r: EndoRelation a) : Boolean =
    fa(x,y,z) ~~r(x,y) && ~~r(y,z) => ~~r(x,z)

  type NegativeTransitiveRelation a = (EndoRelation a | negativeTransitive?)

  op [a] trichotomous? (r: EndoRelation a) : Boolean =
    % exactly one of `r(x,y)', `r(y,x)', and `x = y' holds:
    fa(x,y) r(x,y) && ~~r(y,x) && x ~= y
       || ~~r(x,y) &&   r(y,x) && x ~= y
       || ~~r(x,y) && ~~r(y,x) && x  = y

  type TrichotomousRelation a = (EndoRelation a | trichotomous?)

  op equivalence? : [a] EndoRelation a -> Boolean =
    reflexive? /\ symmetric? /\ transitive?

  type Equivalence a = (EndoRelation a | equivalence?)

  % closure operators:

  op [a] reflexiveClosure (r: EndoRelation a) : ReflexiveRelation a =
    min (fn rc -> r <= rc && reflexive? rc)

  op [a] symmetricClosure (r: EndoRelation a) : SymmetricRelation a =
    min (fn rc -> r <= rc && symmetric? rc)

  op [a] transitiveClosure (r: EndoRelation a) : TransitiveRelation a =
    min (fn rc -> r <= rc && transitive? rc)

  op [a] equivalenceClosure (r: EndoRelation a) : Equivalence a =
    min (fn rc -> r <= rc && equivalence? rc)

endspec
