spec
  import /Library/Structures/Data/Sets/Finite
  
  op Elem.eq? : Elem * Elem -> Boolean

  sort Set = List Elem

  def empty? s = ([] = s)

  def empty = []

  def difference (s1,s2) = foldl (fn (x,s) -> delete (s,x)) s1 s2
  def union (s1,s2) = foldl (fn (x,s) -> insert (s,x)) s1 s2
  def intersect (s1,s2) = foldl (fn (x,s) ->
    if member? (s1,x) then cons (x,s) else s) [] s2
   
  def member? (l,x) =
    case l of
      | [] -> false
      | h::t -> (Elem.eq? (h,x)) or (member? (t,x))

  def delete (l,x) =
    case l of
      | [] -> []
      | h::t -> 
          if (Elem.eq? (h,x)) then
            t
          else
            Cons (h, delete (t,x))

  def insert (l,a) =
    if (member? (l,a)) then
      l
    else
      Cons (a,l)

  def singleton x = [x]

  def theSingleton x =
    case x of
      | [] -> fail "theSingleton: applied to empty list"
      | [x] -> x
      | _::_ -> fail "theSingleton: applied to non-singleton list"

  def size x =
    case x of
      | [] -> 0
      | x::l -> 1 + (size l)
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
