\section{Sets as Lists}
This is a hopelessly naive implementation of Sets as Lists.

Note that the value of this file is not a spec, but function that returns
a spec. The argument to the function is a string used to suffix the sorts
and operators in the spec. 

This inconsistency where some files evaluate to a spec and other evaluate
to a function needs to be addessed. It may be enough to choose a name for
this file to reflect that it is a function that suffixes the spec.

\begin{spec}
spec {
  import /Library/PrettyPrinter/WadlerLindig
  import Sets

  sort Set a = List a

  def empty? s = ([] = s)

  def member? l x =
    case l of
      | [] -> false
      | h::t -> (h = x) or (member? t x)

  def empty = []

  def delete l x =
    case l of
      | [] -> []
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
      | [] -> e
      | h::t -> fold f (f e h) t  % this looks to be the wrong way around

  def map f s =
    case s of
      | [] -> []
      | h::t -> Cons(f h, map f t)

  def find pred s =
    case s of
	  | [] -> None
	  | h::t -> if pred(h) then Some h else find pred t
    
  def singleton x = Cons(x,[])

  def union s1 s2 = fold insert s1 s2

  def take s =
    case s of
	  | [] -> None
	  | h::t -> Some (h,t)

  def ppSet ppElem l =
     ppConcat [
       ppString "{",
       ppSep (ppString ",") (map ppElem l),
       ppString "}"
     ]

  def toList l = l
}
