\section{List}

\begin{spec}
List qualifying spec
  import Lift
  import PrimitiveSorts
  import Nat
  import Compare

  sort List.List a = | Nil | Cons  a * List a

  op nil              : fa(a)   List a
  op app              : fa(a)   (a -> ()) -> List a -> ()
  op map              : fa(a,b) (a -> b) -> List a -> List b
  op exists           : fa(a)   (a -> Boolean) -> List a -> Boolean
  op foldr            : fa(a,b) (a*b -> b) ->  b -> List a -> b
  op foldl            : fa(a,b) (a*b -> b) ->  b -> List a -> b
  op insert           : fa(a)   a * List a -> List a
  op concat           : fa(a)   List a * List a -> List a
  op diff             : fa(a)   List a * List a -> List a
  op member           : fa(a)   a * List a -> Boolean
  op length           : fa(a)   List a -> Nat
  op ++     infixl 11 : fa(a)   List a * List a -> List a
  op @      infixl 11 : fa(a)   List a * List a -> List a
  op nth              : fa(a)   List a * Nat -> a
  op nthTail          : fa(a)   List a * Nat -> List a
  op rev              : fa(a)   List a -> List a
  op all              : fa(a)   (a -> Boolean) -> List a -> Boolean
  op null             : fa(a)   List a -> Boolean
  op flatten          : fa(a)   List(List a) -> List a
  op mapPartial       : fa(a,b) (a -> Option b) -> List a -> List b
  op filter           : fa(a)   (a -> Boolean) -> List a -> List a
  op find             : fa(a)   (a -> Boolean) -> List a -> Option(a)
  op hd               : fa(a)   List a -> a
  op tl               : fa(a)   List a -> List a  
  op cons             : fa(a)   a * List a -> List a
  op tabulate         : fa(a)   Nat * (Nat -> a) -> List a
  op compare          : fa(a)   (a * a -> Comparison) -> List a * List a -> Comparison

  def nil       = Nil
  def cons(a,l) = Cons(a,l)

  def null l = case l of Nil -> true | _ -> false 
  def hd l   = case l of Cons(h,_) -> h 
  def tl l   = case l of Cons(_,t) -> t

  def app f s = 
    case s of
      | [] -> ()
      | hd::tl -> (f hd; app f tl)

  def map f s = 
    case s of
      | [] -> [] 
      | hd::tl -> Cons (f hd,map f tl)

  op rev2 : fa(a) List a * List a -> List a
  def rev2 (l,r) = 
    case l of
      | [] -> r
      | a::l -> rev2(l,Cons(a,r))

  def rev (s) = rev2(s,[])

  def foldr f base s = 
    case s of
      | [] -> base
      | hd::tl -> f(hd,foldr f base tl)

  def foldl f base s = 
    case s of
      | [] -> base
      | hd::tl -> foldl f (f (hd,base)) tl

  def exists p s = 
    case s of
      | [] -> false
      | hd::tl -> if p(hd) then true else (exists p tl)

  def all p s = 
    case s of
      | [] -> true
      | hd::tl -> if p(hd) then all p tl else false

  def insert(hd,tl) = Cons (hd,tl)

  def concat(s1,s2) = 
    case s1 of
      | [] -> s2
      | hd::tl -> Cons (hd,concat (tl,s2))

  def ++(s1,s2) = concat (s1,s2)
  def @ (s1,s2) = concat (s1,s2)

  def member (a,l) = 
    case l of
      | [] -> false
      | hd::tl -> if a = hd then true else (member (a,tl))

  def length s =
    case s of
      | [] -> 0
      | _::l -> 1 Nat.+ (length l)

  def diff (s1,s2) = 
    case s1 of
      | [] -> []
      | hd::tl -> 
          if member (hd,s2) then
            diff (tl,s2) 
          else
            Cons(hd, diff (tl,s2))

  def nth(ls,i) = 
    case ls of
      hd::tl -> if (i = 0) then hd else nth (tl,i Nat.- 1)

  def nthTail(ls,i) = 
    case ls of
      | [] -> []
      | hd::tl -> if i = 0 then tl else nthTail(tl,i Nat.- 1)

  (* May result in non-exhaustive match *)  

  def flatten l = 
    case l of
      | [] -> []
      | l::ls -> concat(l,flatten ls)

  def mapPartial f l = 
    case l of
      | [] -> []
      | l::ls -> 
          (case f l of
             | Some x -> Cons(x,mapPartial f ls)
             | None   -> mapPartial f ls)

  def filter f l = 
    case l of
      | [] -> []
      | l::ls -> if f l then Cons(l,filter f ls) else (filter f ls)

   def find p l = 
     case l of
       | [] -> None
       | l::ls -> if p l then Some l else find p ls

   def tabulate (n,f) = 
     let def tabulateRec(m:Integer,tl) = 
        if m < 0 then
          tl
        else
          tabulateRec (m - 1,cons(f(m),tl))
     in
          tabulateRec (n - 1,[])

   def compare comp (l1,l2) = 
     case (l1,l2) of
       | (t1::t1s, t2::t2s) -> 
           (case comp(t1,t2) of
              | EQUAL  -> compare comp (t1s,t2s)
              | result -> result)
       | ([],   []   ) -> EQUAL
       | ([],   _::_ ) -> LESS
       | (_::_, []   ) -> GREATER
end
\end{spec}

Version of Lists.spec From (mobies) specware4 tree:
Basic operations on Lists.

=begin{spec}
spec
  % import USx(/Library/Base/PrettyPrinter)
=end{spec}

This may be contentious. These are curried versions of list
folds. Arguably these are more standard. Note that the order to the
arguments to foldl have changed with respect to the current Specware.

=begin{spec}
  op foldl : fa (a,b) (b -> a -> b) -> b -> List a -> b
  op foldr : fa (a,b) (a -> b -> b) -> b -> List a -> b

  def foldr f base s = 
    case s of
       Nil -> base
     | Cons (hd,tl) -> f hd (foldr f base tl)

  def foldl f base s = 
    case s of
       Nil -> base
     | Cons (hd,tl) -> foldl f (f base hd) tl
=end{spec}

This pretty prints a list. One must provide the separator (a string) for the
elements of the list.  There are no opening and closing brackets. The
first argument is the method for pretty printing each element of the list.

=begin{spec}
 % op print : fa (a) (a -> Pretty) -> String -> List a -> Pretty
 % def print f sep l = ppBlockLinear (addSeparator (string sep) (List.map f l))
=end{spec}

Same as the above with delimiters.

=begin{spec}
%  op printDelim : fa (a) (a -> Pretty)
%           -> String
%           -> String
%           -> String
%           -> List a
%           -> Pretty
% 
%  def printDelim f left sep right l =
%    ppBlockLinear [
%       (string left),
%       ppBlockNone (addSeparator (string sep) (List.map f l)),
%       (string right)]

end
=end{spec}
