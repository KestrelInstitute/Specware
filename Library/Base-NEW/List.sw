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

  op nil : [a] List a
  def nil = Nil

  op cons : [a] a * List a -> List a
  def cons(x,l) = Cons(x,l)

  op insert : [a] a * List a -> List a
  def insert(x,l) = Cons(x,l)

  op length : [a] List a -> Nat
  def length l =
    case l of
       | []    -> 0
       | _::tl -> 1 + (length tl)

  op null : [a] List a -> Boolean
  def null l =
    case l of
       | [] -> true
       | _  -> false

  op hd : [a] {l : List a | ~(null l)} -> a
  def hd(h::_) = h  % list is non-empty by definition

  op tl : [a] {l : List a | ~(null l)} -> List a
  def tl(_::t) = t  % list is non-empty by definition

  op concat : [a] List a * List a -> List a
  def concat (l1,l2) = 
    case l1 of
       | []     -> l2
       | hd::tl -> Cons(hd,concat(tl,l2))

  op ++ infixl 25 : [a] List a * List a -> List a
  def ++ (s1,s2) = concat(s1,s2)

  op nth : [a] {(l,i) : List a * Nat | i < length l} -> a
  def nth(hd::tl,i) =  % list is non-empty because length > i >= 0
    if i = 0 then hd
             else nth(tl,i-1)

  op nthTail : [a] {(l,i) : List a * Nat | i < length l} -> List a
  def nthTail(hd::tl,i) =  % list is non-empty because length > i >= 0
    if i = 0 then tl
             else nthTail(tl,i-1)

  op last : [a] {l: List a | length(l) > 0} -> a
  def last(hd::tl) =
    case tl of
      | [] -> hd
      | _ -> last(tl)

  op butLast : [a] {l: List a | length(l) > 0} -> List a
  def butLast(hd::tl) =
    case tl of
      | [] -> []
      | _ -> Cons(hd, butLast(tl))

  op member : [a] a * List a -> Boolean
  def member(x,l) =
    case l of
       | []     -> false
       | hd::tl -> if x = hd then true else member(x,tl)

  op sublist : [a]
     {(l,i,j) : List a * Nat * Nat | i <= j && j <= length l} -> List a
  def sublist(l,i,j) =
    let def removeFirstElems(l,i) =
          if i = 0 then l
          else removeFirstElems(tl l,i-1) in
    let def collectFirstElems(l,i) =
          if i = 0 then Nil
          else Cons (hd l, collectFirstElems(tl l,i-1)) in
    collectFirstElems(removeFirstElems(l,i),j-i)

  op map : [a,b] (a -> b) -> List a -> List b
  def map f l =
    case l of
       | []     -> [] 
       | hd::tl -> Cons(f hd,map f tl)

  op mapPartial : [a,b] (a -> Option b) -> List a -> List b
  def mapPartial f l =
    case l of
       | []     -> []
       | hd::tl -> (case f hd of
                       | Some x -> Cons(x,mapPartial f tl)
                       | None   -> mapPartial f tl)

  op foldl : [a,b] (a * b -> b) -> b -> List a -> b
  def foldl f base l =
    case l of
       | []     -> base
       | hd::tl -> foldl f (f(hd,base)) tl

  op foldr : [a,b] (a * b -> b) -> b -> List a -> b
  def foldr f base l =
    case l of
       | []     -> base
       | hd::tl -> f(hd,foldr f base tl)

  op exists : [a] (a -> Boolean) -> List a -> Boolean
  def exists p l =
    case l of
       | []     -> false
       | hd::tl -> if (p hd) then true else (exists p tl)

  op all : [a] (a -> Boolean) -> List a -> Boolean
  def all p l =
    case l of
       | []     -> true
       | hd::tl -> if (p hd) then all p tl else false

  op filter : [a] (a -> Boolean) -> List a -> List a
  def filter p l =
    case l of
       | []     -> []
       | hd::tl -> if (p hd) then Cons(hd,filter p tl) else (filter p tl)

  op diff : [a] List a * List a -> List a
  def diff (l1,l2) =
    case l1 of
       | []     -> []
       | hd::tl -> if member(hd,l2) then diff(tl,l2) 
                                    else Cons(hd,diff(tl,l2))

  op rev : [a] List a -> List a
  def rev l = rev2(l,[])

  op rev2 : [a] List a * List a -> List a
  def rev2 (l,r) =
    case l of
       | []     -> r
       | hd::tl -> rev2(tl,Cons(hd,r))

  op flatten : [a] List(List a) -> List a
  def flatten l =
    case l of
       | []     -> []
       | hd::tl -> concat(hd,flatten tl)

  op find : [a] (a -> Boolean) -> List a -> Option(a)
  def find p l =
    case l of
       | []     -> None
       | hd::tl -> if (p hd) then Some hd else find p tl

  op tabulate : [a] Nat * (Nat -> a) -> List a
  def [a] tabulate(n,f) =
    let def tabulateAux (i : Nat, l : List a) : List a =
            if i = 0 then l
            else tabulateAux(i-1,Cons(f(i-1),l)) in
    tabulateAux(n,[])

  op firstUpTo : [a] (a -> Boolean) -> List a -> Option (a * List a)
  def firstUpTo p l =
    case l of
       | []     -> None
       | hd::tl -> if p hd then Some(hd,Nil)
                   else case firstUpTo p tl of
                           | None       -> None
                           | Some(x,l1) -> Some(x,Cons(hd,l1))

  op splitList : [a] (a -> Boolean) -> List a -> Option(List a * a * List a)
  def splitList p l =
    case l of
       | []     -> None
       | hd::tl -> if (p hd) then Some(Nil,hd,tl)
                   else case splitList p tl of
                           | None -> None
                           | Some(l1,x,l2) -> Some(Cons(hd,l1),x,l2)

  op locationOf : [a] List a * List a -> Option(Nat * List a)
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

  op compare : [a] (a * a -> Comparison) -> List a * List a -> Comparison
  def compare comp (l1,l2) = 
    case (l1,l2) of
       | (hd1::tl1,hd2::tl2) -> (case comp(hd1,hd2) of
                                    | Equal  -> compare comp (tl1,tl2)
                                    | result -> result)
       | ([],      []      ) -> Equal
       | ([],      _::_    ) -> Less
       | (_::_,    []      ) -> Greater

  op app : [a] (a -> ()) -> List a -> ()  % deprecated
  def app f l =
    case l of
       | []     -> ()
       | hd::tl -> (f hd; app f tl)

endspec
