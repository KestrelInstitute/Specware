Relation qualifying spec

  import Sets

  % a relation is a set of (i.e. predicate over) pairs:
  type Relation(a,b) = Set (a * b)  % = Predicate (a * b)

  op domain : [a,b] Relation(a,b) -> Set a
  def domain r = (fn x -> (ex(y) r(x,y)))

  op range : [a,b] Relation(a,b) -> Set b
  def range r = (fn y -> (ex(x) r(x,y)))

  % range values related to domain value:
  op apply : [a,b] Relation(a,b) -> a -> Set b
  def apply r x = (fn y -> r(x,y))

  % inverse of `apply' (we use `_' because `-' is disallowed):
  op apply_1 : [a,b] Relation(a,b) -> b -> Set a
  def apply_1 r y = (fn x -> r(x,y))

  % lifting of `apply' to sets:
  op applys : [a,b] Relation(a,b) -> Set a -> Set b
  def applys r xS = (fn y -> (ex(x) x in? xS && r(x,y)))

  % inverse of `applys':
  op applys_1 : [a,b] Relation(a,b) -> Set b -> Set a
  def applys_1 r yS = (fn x -> (ex(y) y in? yS && r(x,y)))

  % composition:
  op o infixl 24 : [a,b,c] Relation(b,c) * Relation(a,b) -> Relation(a,c)
  def o (r1,r2) = (fn (x,z) -> (ex(y) r2(x,y) && r1(y,z)))

  op inverse : [a,b] Relation(a,b) -> Relation(b,a)
  def inverse r = (fn (y,x) -> r(x,y))

  op filterDomain : [a,b] Predicate a -> Relation(a,b) -> Relation(a,b)
  def filterDomain p r = (fn (x,y) -> r(x,y) && p x)

  op filterRange : [a,b] Predicate b -> Relation(a,b) -> Relation(a,b)
  def filterRange p r = (fn (x,y) -> r(x,y) && p y)

  % some range value for every domain value:
  op total? : [a,b] Relation(a,b) -> Boolean
  def total? r = (domain r = full)

  type TotalRelation(a,b) = (Relation(a,b) | total?)

  % some domain value for every range value:
  op surjective? : [a,b] Relation(a,b) -> Boolean
  def surjective? r = (range r = full)

  type SurjectiveRelation(a,b) = (Relation(a,b) | surjective?)

  % at most one range value for every domain value:
  op functional? : [a,b] Relation(a,b) -> Boolean
  def functional? r = (fa(x) (single? OR empty?) (apply r x))

  type FunctionalRelation(a,b) = (Relation(a,b) | functional?)

  % at most one domain value for every range value:
  op injective? : [a,b] Relation(a,b) -> Boolean
  def injective? r = (fa(y) (single? OR empty?) (apply_1 r y))

  type InjectiveRelation(a,b) = (Relation(a,b) | injective?)

  op bijective? : [a,b] Relation(a,b) -> Boolean
  def bijective? = injective? AND surjective?

  type BijectiveRelation(a,b) = (Relation(a,b) | bijective?)

  type FiniteRelation(a,b) = (Relation(a,b) | finite?)

  type InfiniteRelation(a,b) = (Relation(a,b) | infinite?)

  type CountableRelation(a,b) = (Relation(a,b) | countable?)

  type UncountableRelation(a,b) = (Relation(a,b) | uncountable?)

endspec
