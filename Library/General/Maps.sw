Map qualifying spec

  import Relations

  type Map(a,b) = FunctionalRelation(a,b)

  op definedAt infixl 20 : [a,b] Map(a,b) * a -> Boolean
  def definedAt (m,x) = x in? domain m

  op undefinedAt infixl 20 : [a,b] Map(a,b) * a -> Boolean
  def undefinedAt (m,x) = ~(x in? domain m)

  % value of map at (`@') point, i.e. map application:
  op @ infixl 23 : [a,b] ((Map(a,b) * a) | definedAt) -> b
  def @ (m,x) = the (fn y -> m(x,y))

  % "totalization" of `@' using `Option':
  op @@ infixl 23 : [a,b] Map(a,b) * a -> Option b
  def @@ (m,x) = if m definedAt x then Some (m @ x) else None

  % update map (analogous to record update):
  op <<< infixl 25 : [a,b] Map(a,b) * Map(a,b) -> Map(a,b)
  def <<< (m1,m2) = the (fn m ->
    domain m = domain m1 \/ domain m2 &&
    (fa(x) x in? domain m =>
           m @ x = (if m2 definedAt x then m2 @ x else m1 @ x)))

  % update map at one point:
  op update : [a,b] Map(a,b) -> a -> b -> Map(a,b)
  def update m x y = m <<< single (x, y)

  % remove domain values from map:
  op -- infixl 25 : [a,b] Map(a,b) * Set a -> Map(a,b)
  def -- (m,xS) = filterDomain (\ xS) m

  % remove domain value from map:
  op - infixl 25 : [a,b] Map(a,b) * a -> Map(a,b)
  def - (m,x) = m -- single x

  type TotalMap(a,b) = (Map(a,b) | total?)

  % convert function to (total) map:
  op fromFunction : [a,b] (a -> b) -> TotalMap(a,b)
  def fromFunction f = (fn (x,y) -> y = f x)

  % convert total map to function:
  op toFunction : [a,b] TotalMap(a,b) -> (a -> b)
  def toFunction = inverse fromFunction

  % maps agree on intersection of domains:
  op agree? : [a,b] Map(a,b) * Map(a,b) -> Boolean
  def agree?(m1,m2) = functional? (m1 \/ m2)

  type SurjectiveMap(a,b) = (Map(a,b) | Relation.surjective?)

  type InjectiveMap(a,b) = (Map(a,b) | Relation.injective?)

  type BijectiveMap(a,b) = (Map(a,b) | Relation.bijective?)

  type FiniteMap(a,b) = (Map(a,b) | finite?)

  type InfiniteMap(a,b) = (Map(a,b) | infinite?)

  type CountableMap(a,b) = (Map(a,b) | countable?)

  type UncountableMap(a,b) = (Map(a,b) | uncountable?)

endspec
