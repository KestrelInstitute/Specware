Relation qualifying spec

  import Sets

  % relations as sets of pairs:
  type Relation(a,b) = Set (a * b)

  op domain : [a,b] Relation(a,b) -> Set a
  def domain r = fn x -> (ex(y) r(x,y))

  op range : [a,b] Relation(a,b) -> Set b
  def range r = fn y -> (ex(x) r(x,y))

  % range values related to domain value:
  op apply : [a,b] Relation(a,b) -> a -> Set b
  def apply r x = fn y -> r(x,y)

  % domain values related to range value (apply inverse):
  op applyi : [a,b] Relation(a,b) -> b -> Set a
  def applyi r y = fn x -> r(x,y)

  % lifting of `apply' to sets:
  op applys : [a,b] Relation(a,b) -> Set a -> Set b
  def applys r xS = fn y -> (ex(x) x in? xS && r(x,y))

  % lifting of `applyi' to sets:
  op applyis : [a,b] Relation(a,b) -> Set b -> Set a
  def applyis r yS = fn x -> (ex(y) y in? yS && r(x,y))

  % forward composition:
  op :> infixl 24 : [a,b,c] Relation(a,b) * Relation(b,c) -> Relation(a,c)
  def :> (r1,r2) = fn (x,z) -> (ex(y) r1(x,y) && r2(y,z))

  % backward composition:
  op o infixl 24 : [a,b,c] Relation(b,c) * Relation(a,b) -> Relation(a,c)
  def o (r1,r2) = r2 :> r1

  op inverse : [a,b] Relation(a,b) -> Relation(b,a)
  def inverse r = fn (y,x) -> r(x,y)

  % remove pairs whose domain value is not in argument set:
  op restrictDomain infixl 25 : [a,b] Relation(a,b) * Set a -> Relation(a,b)
  def restrictDomain (r,xS) = fn (x,y) -> r(x,y) && x in? xS

  % remove pairs whose range value is not in argument set:
  op restrictRange infixl 25 : [a,b] Relation(a,b) * Set b -> Relation(a,b)
  def restrictRange (r,yS) = fn (x,y) -> r(x,y) && y in? yS

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
  def functional? r = (fa(x) (single? \/ empty?) (apply r x))

  type Map(a,b) = (Relation(a,b) | functional?)

  % at most one domain value for every range value:
  op injective? : [a,b] Relation(a,b) -> Boolean
  def injective? r = (fa(y) (single? \/ empty?) (applyi r y))

  type InjectiveRelation(a,b) = (Relation(a,b) | injective?)

  % cardinalities:
  type FiniteRelation(a,b) = (Relation(a,b) | finite?)
  type InfiniteRelation(a,b) = (Relation(a,b) | infinite?)
  type CountableRelation(a,b) = (Relation(a,b) | countable?)
  type UncountableRelation(a,b) = (Relation(a,b) | uncountable?)

endspec
