List qualifying spec 
  import Option
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
  op firstUpTo        : fa(a)   (a -> Boolean) -> List a -> Option (a * List a)
  op firstUpToHelper  : fa(a)   ((a -> Boolean) * List a * List a) -> Option(a * List a)

  def nil       = Nil
  def cons(a,l) = Cons(a,l)

  def null l = case l of Nil -> true | _ -> false 
  def hd l   = case l of Cons (h,_) -> h 
  def tl l   = case l of Cons (_,t) -> t

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
      | hd::tl -> if (p hd) then true else (exists p tl)

  def all p s = 
    case s of
      | [] -> true
      | hd::tl -> if (p hd) then all p tl else false

  def insert (hd,tl) = Cons (hd,tl)

  def concat (s1,s2) = 
    case s1 of
      | [] -> s2
      | hd::tl -> Cons (hd,concat (tl,s2))

  def ++ (s1,s2) = concat (s1,s2)
  def @ (s1,s2) = concat (s1,s2)

  def member (a,l) = 
    case l of
      | [] -> false
      | hd::tl -> if a = hd then true else (member (a,tl))

  def length s =
    case s of
      | [] -> 0
      | _::l -> 1 + (length l)

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
      hd::tl ->
        if i = 0 then
          hd
        else
          nth (tl, i - 1)

  def nthTail(ls,i) = 
    case ls of
      | [] -> []
      | hd::tl ->
          if i = 0 then
            tl
          else
            nthTail (tl, i - 1)

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
          tabulateRec (m - 1,cons (f m,tl))
     in
       tabulateRec (n - 1,[])

   def compare comp (l1,l2) = 
     case (l1,l2) of
       | (t1::t1s, t2::t2s) -> 
           (case comp (t1,t2) of
              | Equal  -> compare comp (t1s,t2s)
              | result -> result)
       | ([],   []   ) -> Equal
       | ([],   _::_ ) -> Less
       | (_::_, []   ) -> Greater

   def firstUpTo p l =
     firstUpToHelper(p, l, [])

   def firstUpToHelper(p, l, res) =
     case l of
       | [] -> None
       | hd::tl -> if p hd then Some (hd, res) else firstUpToHelper(p, tl, Cons(hd,res))
endspec
