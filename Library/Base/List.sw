List qualifying spec

  % refinement of base spec List

  import Option
  import Nat

  % sorts:

  % sort List a = | Nil | Cons a * List a

  % ops whose Lisp code is generated:

  op nil             : fa(a)   List a
  op cons            : fa(a)   a * List a -> List a
  op insert          : fa(a)   a * List a -> List a
  op length          : fa(a)   List a -> Nat
  op null            : fa(a)   List a -> Boolean
  op hd              : fa(a)   {l : List a | ~(null l)} -> a
  op tl              : fa(a)   {l : List a | ~(null l)} -> List a
  op concat          : fa(a)   List a * List a -> List a
  op ++ infixl 11    : fa(a)   List a * List a -> List a
  op @  infixl 11    : fa(a)   List a * List a -> List a
  op nth             : fa(a)   {(l,i) : List a * Nat | i < length l} -> a
  op nthTail         : fa(a)   {(l,i) : List a * Nat | i < length l} ->
                               List a
  op member          : fa(a)   a * List a -> Boolean
  op sublist         : fa(a)   {(l,i,j) : List a * Nat * Nat |
                                i < j & j <= length l} -> List a
  op map             : fa(a,b) (a -> b) -> List a -> List b
  op mapPartial      : fa(a,b) (a -> Option b) -> List a -> List b
  op foldl           : fa(a,b) (a * b -> b) -> b -> List a -> b
  op foldr           : fa(a,b) (a * b -> b) -> b -> List a -> b
  op exists          : fa(a)   (a -> Boolean) -> List a -> Boolean
  op all             : fa(a)   (a -> Boolean) -> List a -> Boolean
  op filter          : fa(a)   (a -> Boolean) -> List a -> List a
  op diff            : fa(a)   List a * List a -> List a
  op rev             : fa(a)   List a -> List a
  op rev2            : fa(a)   List a * List a -> List a
  op flatten         : fa(a)   List(List a) -> List a
  op find            : fa(a)   (a -> Boolean) -> List a -> Option(a)
  op tabulate        : fa(a)   Nat * (Nat -> a) -> List a
  op firstUpTo       : fa(a)   (a -> Boolean) -> List a ->
                               Option (a * List a)
  op firstUpToHelper : fa(a)   ((a -> Boolean) * List a * List a) ->
                               Option(a * List a)
  op splitList       : fa(a)  (a -> Boolean) -> List a ->
                              Option(List a * a * List a)
  op splitListHelper : fa(a)  ((a -> Boolean) * List a * List a) ->
                              Option(List a * a * List a)
  op locationOf      : fa(a)  List a * List a -> Option(Nat * List a)
  op compare         : fa(a)  (a * a -> Comparison) -> List a * List a ->
                              Comparison
  op app             : fa(a)  (a -> ()) -> List a -> ()  % deprecated

  % the ops rev2, firstUpToHelper, and splitListHelper are auxiliary ops
  % to define rev, firstUpTo, and splitList; they are not present in the
  % base spec List of which this spec is a refinement

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

  def @ (s1,s2) = concat(s1,s2)

  def nth(hd::tl,i) =  % list is non-empty because length > i >= 0
    if i = 0 then hd
             else nth(tl,i-1)

  def nthTail(hd::tl,i) =  % list is non-empty because length > i >= 0
    if i = 0 then tl
             else nthTail(tl,i-1)

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

  def fa(a) tabulate(n,f) =
    let def tabulateAux (i : Nat, l : List a) : List a =
            if i = 0 then l
            else tabulateAux(i-1,Cons(f(i-1),l)) in
    tabulateAux(n,[])

%  def firstUpTo p l = firstUpToHelper(p,l,[])
  def firstUpTo p l =
    case l of
       | []     -> None
       | hd::tl -> if p hd then Some(hd,Nil)
                   else case firstUpTo p tl of
                           | None       -> None
                           | Some(x,l1) -> Some(x,Cons(hd,l1))

  def firstUpToHelper(p,l,r) =
    case l of
       | []     -> None
       | hd::tl -> if (p hd) then Some(hd,rev r)
                   else firstUpToHelper(p,tl,Cons(hd,r))

%  def splitList p l = splitListHelper(p,l,[])
  def splitList p l =
    case l of
       | []     -> None
       | hd::tl -> if (p hd) then Some(Nil,hd,tl)
                   else case splitList p tl of
                           | None -> None
                           | Some(l1,x,l2) -> Some(Cons(hd,l1),x,l2)

  def splitListHelper(p,l,r) =
    case l of
       | []     -> None
       | hd::tl -> if (p hd) then Some(rev r,hd,tl)
                   else splitListHelper(p,tl,Cons(hd,r))

  def fa(a) locationOf(subl,supl) =
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

  % ops conceptually belonging to this spec but introduced elsewhere:

  % op show : String -> List String -> String

endspec
