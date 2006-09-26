List qualifying spec

  import Option, Integer

  % types:

  type List.List a = | Nil | Cons a * List.List a
       % qualifier required for internal parsing reasons

  axiom induction is [a]
    fa (p : List a -> Boolean)
      p Nil &&  % base
      (fa (x:a, l:List a) p l => p(Cons(x,l))) =>  % step
      (fa (l:List a) p l)

  % ops on lists:

  op nil             : [a]   List a
  op cons            : [a]   a * List a -> List a
  op insert          : [a]   a * List a -> List a
  op length          : [a]   List a -> Nat
  op null            : [a]   List a -> Boolean
  op hd              : [a]   {l : List a | ~(null l)} -> a
  op tl              : [a]   {l : List a | ~(null l)} -> List a
  op concat          : [a]   List a * List a -> List a
  op ++ infixl 25    : [a]   List a * List a -> List a
  op nth             : [a]   {(l,i) : List a * Nat | i < length l} -> a
  op nthTail         : [a]   {(l,i) : List a * Nat | i <= length l} ->
                               List a
  op last            : [a]   {l: List a | length(l) > 0} -> a
  op butLast         : [a]   {l: List a | length(l) > 0} -> List a
  op member          : [a]   a * List a -> Boolean
  op sublist         : [a]   {(l,i,j) : List a * Nat * Nat |
                                i <= j && j <= length l} -> List a
  op map             : [a,b] (a -> b) -> List a -> List b
  op mapPartial      : [a,b] (a -> Option b) -> List a -> List b
  op foldl           : [a,b] (a * b -> b) -> b -> List a -> b
  op foldr           : [a,b] (a * b -> b) -> b -> List a -> b
  op exists          : [a]   (a -> Boolean) -> List a -> Boolean
  op all             : [a]   (a -> Boolean) -> List a -> Boolean
  op filter          : [a]   (a -> Boolean) -> List a -> List a
  op diff            : [a]   List a * List a -> List a
  op rev             : [a]   List a -> List a
  op rev2            : [a]   List a * List a -> List a
  op flatten         : [a]   List(List a) -> List a
  op find            : [a]   (a -> Boolean) -> List a -> Option(a)
  op tabulate        : [a]   Nat * (Nat -> a) -> List a
  op firstUpTo       : [a]   (a -> Boolean) -> List a ->
                               Option (a * List a)
  op splitList       : [a]   (a -> Boolean) -> List a ->
                               Option(List a * a * List a)
  op locationOf      : [a]   List a * List a -> Option(Nat * List a)
  op compare         : [a]   (a * a -> Comparison) -> List a * List a ->
                               Comparison
  op app             : [a]   (a -> ()) -> List a -> ()  % deprecated

  def nil = Nil

  def cons(x,l) = Cons(x,l)

  def insert(x,l) = Cons(x,l)

  def length l =
    case l of
       | []    -> 0
       | _::tl -> 1 + (length tl)

  def null l =
    case l of
       | [] -> true
       | _  -> false

  def hd(h::_) = h  % list is non-empty by definition

  def tl(_::t) = t  % list is non-empty by definition

  def concat (l1,l2) = 
    case l1 of
       | []     -> l2
       | hd::tl -> Cons(hd,concat(tl,l2))

  def ++ (s1,s2) = concat(s1,s2)

  def nth(hd::tl,i) =  % list is non-empty because length > i >= 0
    if i = 0 then hd
             else nth(tl,i-1)

  def nthTail(l,i) =
    if i = 0 then l
             else nthTail(tl l,i-1)

  def last(hd::tl) =
    case tl of
      | [] -> hd
      | _ -> last(tl)

  def butLast(hd::tl) =
    case tl of
      | [] -> []
      | _ -> Cons(hd, butLast(tl))

  def member(x,l) =
    case l of
       | []     -> false
       | hd::tl -> if x = hd then true else member(x,tl)

  def sublist(l,i,j) =
    let def removeFirstElems(l,i) =
          if i = 0 then l
          else removeFirstElems(tl l,i-1) in
    let def collectFirstElems(l,i) =
          if i = 0 then Nil
          else Cons (hd l, collectFirstElems(tl l,i-1)) in
    collectFirstElems(removeFirstElems(l,i),j-i)

  def map f l =
    case l of
       | []     -> [] 
       | hd::tl -> Cons(f hd,map f tl)

  def mapPartial f l =
    case l of
       | []     -> []
       | hd::tl -> (case f hd of
                       | Some x -> Cons(x,mapPartial f tl)
                       | None   -> mapPartial f tl)

  def foldl f base l =
    case l of
       | []     -> base
       | hd::tl -> foldl f (f(hd,base)) tl

  def foldr f base l =
    case l of
       | []     -> base
       | hd::tl -> f(hd,foldr f base tl)

  def exists p l =
    case l of
       | []     -> false
       | hd::tl -> if (p hd) then true else (exists p tl)

  def all p l =
    case l of
       | []     -> true
       | hd::tl -> if (p hd) then all p tl else false

  def filter p l =
    case l of
       | []     -> []
       | hd::tl -> if (p hd) then Cons(hd,filter p tl) else (filter p tl)

  def diff (l1,l2) =
    case l1 of
       | []     -> []
       | hd::tl -> if member(hd,l2) then diff(tl,l2) 
                                    else Cons(hd,diff(tl,l2))

  def rev l = rev2(l,[])

  def rev2 (l,r) =
    case l of
       | []     -> r
       | hd::tl -> rev2(tl,Cons(hd,r))

  def flatten l =
    case l of
       | []     -> []
       | hd::tl -> concat(hd,flatten tl)

  def find p l =
    case l of
       | []     -> None
       | hd::tl -> if (p hd) then Some hd else find p tl

  def [a] tabulate(n,f) =
    let def tabulateAux (i : Nat, l : List a) : List a =
            if i = 0 then l
            else tabulateAux(i-1,Cons(f(i-1),l)) in
    tabulateAux(n,[])

  def firstUpTo p l =
    case l of
       | []     -> None
       | hd::tl -> if p hd then Some(hd,Nil)
                   else case firstUpTo p tl of
                           | None       -> None
                           | Some(x,l1) -> Some(x,Cons(hd,l1))

  def splitList p l =
    case l of
       | []     -> None
       | hd::tl -> if (p hd) then Some(Nil,hd,tl)
                   else case splitList p tl of
                           | None -> None
                           | Some(l1,x,l2) -> Some(Cons(hd,l1),x,l2)

  def [a] locationOf(subl,supl) =
    let def checkPrefix (subl : List a, supl : List a) : Option(List a) =
            % checks if subl is prefix of supl and if so
            % returns what remains of supl after subl
            case (subl,supl) of
               | (subhd::subtl, suphd::suptl) -> if subhd = suphd
                                                 then checkPrefix(subtl,suptl)
                                                 else None
               | ([],_)                       -> Some supl
               | _                            -> None in
    let def locationOfNonEmpty (subl : List a, supl : List a, pos : Nat)
            : Option(Nat * List a) =
            % assuming subl is non-empty, searches first position of subl
            % within supl and if found returns what remains of supl after subl
            let subhd::subtl = subl in
            case supl of
               | [] -> None
               | suphd::suptl ->
                 if subhd = suphd
                 then case checkPrefix(subtl,suptl) of  % heads =, check tails
                         | None -> locationOfNonEmpty(subl,suptl,pos+1)
                         | Some suplrest -> Some(pos,suplrest)
                 else locationOfNonEmpty(subl,suptl,pos+1) in
    case subl of
       | [] -> Some(0,supl)
       | _  -> locationOfNonEmpty(subl,supl,0)

  def compare comp (l1,l2) = 
    case (l1,l2) of
       | (hd1::tl1,hd2::tl2) -> (case comp(hd1,hd2) of
                                    | Equal  -> compare comp (tl1,tl2)
                                    | result -> result)
       | ([],      []      ) -> Equal
       | ([],      _::_    ) -> Less
       | (_::_,    []      ) -> Greater

  def app f l =
    case l of
       | []     -> ()
       | hd::tl -> (f hd; app f tl)

endspec
