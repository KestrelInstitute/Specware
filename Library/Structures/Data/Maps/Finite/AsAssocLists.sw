spec
  import translate Polymorphic/AsAssocList by {Map._ +-> FinitePolyMap._}

  import ../Finite

  sort Map = FinitePolyMap.Map (Dom,Cod)
  def empty = FinitePolyMap.empty
  def evalPartial = FinitePolyMap.evalPartial
  def eval = FinitePolyMap.eval
  def update = FinitePolyMap.update

  (*
   * The next function is dubious. The point is that, while it make sense
   * to define a function for enumerating the elements of a finite map,
   * that function must not be sensitive to the way the map is constructed.
   * Hence,
   *   takeOne (update (update (m,x,y),u,v))
   * must be the same as:
   *   takeOne (update (update (m,u,v),x,y)) 
   * If we represent maps by association lists and ignore the ordering, this
   * will not be the case. For this reason, the next function
   * may disappear.
   *)
  def takeOne map =
    case map of
      | [] -> None
      | (x,y)::rest -> One ((x,y),rest)

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
