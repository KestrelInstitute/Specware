This is a hopelessly naive implementation of Sets as Lists.

Note that the value of this file is not a spec, but function that returns
a spec. The argument to the function is a string used to suffix the sorts
and operators in the spec. 

This inconsistency where some files evaluate to a spec and other evaluate
to a function needs to be addessed. It may be enough to choose a name for
this file to reflect that it is a function that suffixes the spec.

\begin{spec}
let SetsAsLists = spec
  import USI(/PrettyPrinter)
  import USI(Sets)

  sort Set a = List a

  def empty? s = (Nil = s)

  def member? l x =
    case l of
        Nil -> false
      | h::t -> (h = x) or (member? t x)

  def empty = Nil

  def delete l x =
    case l of
        Nil -> Nil
      | h::t -> 
          if (h = x) then
            t
          else
            Cons (h, delete t x)

  def insert l a =
    if (member? l a) then
      l
    else
      Cons (a,l)

  def fold f e l =
    case l of
        Nil -> e
      | h::t -> fold f (f e h) t  % this looks to be the wrong way around

  def map f s =
    case s of
        Nil -> Nil
      | h::t -> Cons(f h, map f t)

  def find pred s =
    case s of
	    Nil -> None
	  | h::t -> if pred(h) then Some h else find pred t
    
  def singleton x = Cons(x,Nil)

  def union s1 s2 = fold insert s1 s2

  def take s =
    case s of
	    Nil -> None
	  | h::t -> Some (h,t)

  def takeTwo s =
    case s of
	    Nil -> Zero
	  | h::[] -> One h
	  | x1::x2::l -> Two (x1,x2,l)

  def ppSet ppElem l =
     ppConcat [
       ppString "{",
       ppSep (ppString ",") (map ppElem l),
       ppString "}"
     ]

  def toList l = l
   
end in
  fn suffix : String -> translateSpec SetsAsLists [
    "Set" |-> "Set" ^ suffix,
    "MaybeTwo" |-> "MaybeTwo" ^ suffix,
    "empty" |-> "empty" ^ suffix,
    "empty?" |-> "empty?" ^ suffix,
    "union" |-> "union" ^ suffix,
    "intersection" |-> "intersection" ^ suffix,
    "difference" |->"difference"  ^ suffix,
    "member?" |-> "member?" ^ suffix,
    "delete" |-> "delete" ^ suffix,
    "insert" |-> "insert" ^ suffix,
    "singleton" |-> "singleton" ^ suffix,
    "fold" |-> "fold" ^ suffix,
    "find" |-> "find" ^ suffix,
    "map" |-> "map" ^ suffix,
    "take" |-> "take" ^ suffix,
    "takeTwo" |-> "takeTwo" ^ suffix,
    "ppSet" |-> "ppSet" ^ suffix,
    "toList" |-> "toList" ^ suffix
]
\end{spec}
