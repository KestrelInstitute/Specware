spec
  import ../Finite
  import FinitePolySet qualifying Polymorphic/AsLists

  sort Set = FinitePolySet.Set Elem

  def empty = FinitePolySet.empty
  def empty? = FinitePolySet.empty?

  def insert = FinitePolySet.insert
  def member? = FinitePolySet.member?
  def size = FinitePolySet.size
  def singleton = FinitePolySet.singleton
  def theSingleton = FinitePolySet.theSingleton
  def difference = FinitePolySet.difference
  def union = FinitePolySet.union

  (*
   * The next function is dubious. The point is that, while it make sense
   * to define a function for enumerating the elements of a finite map,
   * that function must not be sensitive to the way the map is constructed.
   * Hence,
   *   takeOne (update (update (m,x,y),u,v))
   * must be the same as:
   *   takeOne (update (update (m,u,v),x,y)) 
   * If we represent maps by association lists and ignore the ordering, this
   * will not be the case. For this reason, the next function should disappear.
   *)
  def takeOne set =
    case set of
      | [] -> None
      | x::rest -> One (x,rest)

  def fold = foldl

  (*
   * These can migrate to the more abstract specification.
   *)
  def foldl (f,unit,map) =
    case takeOne map of
      | None -> unit
      | One (p,rest) -> foldl (f, f (unit,p), rest)

  def foldr (f,unit,map) =
    case takeOne map of
      | None -> unit
      | One (p,rest) -> f (foldr (f,unit,rest), p)
endspec
