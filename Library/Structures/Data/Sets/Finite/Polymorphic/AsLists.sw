spec
  import ../Polymorphic

  sort Set a = List a

  def empty? s = ([] = s)

  def empty = []

  def difference (s1,s2) = foldl (fn (x,s) -> delete (s,x)) s1 s2
  def union (s1,s2) = foldl (fn (x,s) -> insert (s,x)) s1 s2
  def intersect (s1,s2) = foldl (fn (x,s) ->
    if member? (s1,x) then cons (x,s) else s) [] s2
   
  def member? (l,x) =
    case l of
      | [] -> false
      | h::t -> (h = x) or (member? (t,x))

  def delete (l,x) =
    case l of
      | [] -> []
      | h::t -> 
          if (h = x) then
            t
          else
            Cons (h, delete (t,x))

  def insert (l,a) =
    if (member? (l,a)) then
      l
    else
      Cons (a,l)

  % op union : fa(a) Set a -> Set a -> Set a
  % op intersection : fa(a) Set a -> Set a -> Set a
  % op difference : fa(a) Set a -> Set a -> Set a

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
endspec
