(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Sets as Lists}
This is a hopelessly naive implementation of Sets as Lists.

\begin{spec}
spec
  import ../Polymorphic
  import /Library/PrettyPrinter/WadlerLindig

  type Set a = List a

  def empty? s = ([] = s)

  def member? l x =
    case l of
      | [] -> false
      | h::t -> (h = x) || (member? t x)

  def subset? s1 s2 =
    forall? (fn e1 -> member? s2 e1) s1

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

  def fold fl e l =
    case l of
      | [] -> e
      | h::t -> fold fl (fl e h) t  % this looks to be the wrong way around

  def map f s =
    case s of
      | [] -> []
      | h::t -> Cons(f h, map f t)

  def find pred s =
    case s of
	  | [] -> None
	  | h::t -> if (pred h) then Some h else find pred t
    
  def singleton x = Cons(x,[])

  def union s1 s2 = fold insert s1 s2

%   def takeOne s =
%     case s of
% 	  | [] -> None
% 	  | h::t -> Some (h,t)

  def ppSet ppElem l =
     ppConcat [
       ppString "{",
       ppSep (ppString ",") (map ppElem l),
       ppString "}"
     ]

  def toList l = l
  def fromList l = l
endspec
