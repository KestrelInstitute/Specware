(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

PrList qualifying spec

  import ../Base/List

  % types:

  %type List.List a = | Nil | Cons a * List.List a
       % qualifier required for internal parsing reasons

  axiom induction is [a]
    fa (p : List a -> Bool)
      p Nil &&  % base
      (fa (x:a, l:List a) p l => p(Cons(x,l))) =>  % step
      (fa (l:List a) p l)

  % ops on lists:
(*
  op nil             : [a]   List a
  op cons            : [a]   a * List a -> List a
  op insert          : [a]   a * List a -> List a
  op length          : [a]   List a -> Nat
  op null            : [a]   List a -> Bool
  op hd              : [a]   {l : List a | ~(null l)} -> a
  op tl              : [a]   {l : List a | ~(null l)} -> List a
  op concat          : [a]   List a * List a -> List a
  op ++ infixl 25    : [a]   List a * List a -> List a
%% Deprecated for some time so it should be safe to remove
%  op @  infixl 25    : [a]   List a * List a -> List a
  op nth             : [a]   {(l,i) : List a * Nat | i < length l} -> a
  op nthTail         : [a]   {(l,i) : List a * Nat | i < length l} -> List a
  op last            : [a]   {l: List a | length(l) > 0} -> a
  op butLast         : [a]   {l: List a | length(l) > 0} -> List a
  op member          : [a]   a * List a -> Bool
%  op sublist         : [a]   {(l,i,j) : List a * Nat * Nat | i <= j && j <= length l} -> List a
  op map             : [a,b] (a -> b) -> List a -> List b
  op mapPartial      : [a,b] (a -> Option b) -> List a -> List b
  op foldl           : [a,b] (a * b -> b) -> b -> List a -> b
  op foldr           : [a,b] (a * b -> b) -> b -> List a -> b
  op exists          : [a]   (a -> Bool) -> List a -> Bool
  op all             : [a]   (a -> Bool) -> List a -> Bool
  op filter          : [a]   (a -> Bool) -> List a -> List a
  op diff            : [a]   List a * List a -> List a
  op rev             : [a]   List a -> List a
  op rev2            : [a]   List a * List a -> List a
  op flatten         : [a]   List(List a) -> List a
  op find            : [a]   (a -> Bool) -> List a -> Option(a)
  op tabulate        : [a]   Nat * (Nat -> a) -> List a
  op firstUpTo       : [a]   (a -> Bool) -> List a -> Option (a * List a)
  op splitList       : [a]   (a -> Bool) -> List a -> Option(List a * a * List a)
  op locationOf      : [a]   List a * List a -> Option(Nat * List a)
  op compare         : [a]   (a * a -> Comparison) -> List a * List a -> Comparison
  op app             : [a]   (a -> ()) -> List a -> ()  % deprecated
*)

  axiom nilIsNil is [a] (empty: List a) = Nil

  axiom length_nil is [a] length([]: List a) = 0

  axiom length_cons is [a] fa (x: a, l) length(Cons(x, l)) = 1 + length(l)

  axiom empty?Null is [a] empty?([]: List a)

  axiom empty?Cons is [a] fa (x: a, l) ~(empty?(Cons(x, l)))

  axiom hdCons is [a] fa (x: a, l) head (Cons(x, l)) = x

  axiom tlCons is [a] fa (x: a, l) tail (Cons(x, l)) = l

  axiom concatNull is [a] fa (l: List a) [] ++ l = l

  axiom concatCons is [a] fa (x1: a, l1, l2)
     ++(Cons(x1, l1), l2) = Cons(x1, l1 ++ l2)

%  def @ (s1,s2) = concat(s1,s2)

  axiom nth_def1 is [a] fa(hd: a, tl)
     @(Cons(hd,tl),0) = hd

  axiom @_def2 is [a] fa(hd: a, tl, i) (i > 0) =>
     @(Cons(hd,tl),i) = @(tl, i-1)

  axiom removePrefix_def1 is [a] fa (tl: List a)
     removePrefix(tl,0) = tl

  axiom length_removePrefix_B is [a]		% Really a theorem
    fa(l: List a,i: Nat) i <= length l => length(removePrefix(l,i)) = length l - i

  axiom removePrefix_def2 is [a] fa (hd: a, tl, i) (i > 0) =>
     removePrefix(Cons(hd,tl),i) = removePrefix(tl, i-1)

  axiom last_def1 is [a] fa (hd: a)
    last(Cons(hd, [])) = hd

  axiom last_def2 is [a] fa (hd: a, tl)
    tl ~= [] => last(Cons(hd, tl)) = last(tl)

  axiom butLast_def1 is [a] fa (hd: a)
    butLast(Cons(hd, [])) = []

  axiom butLast_def2 is [a] fa (hd: a, tl)
    tl ~= [] => butLast(Cons(hd, tl)) = Cons(hd, butLast(tl))

  axiom in?_def1 is [a] fa (x: a)
    ~(in?(x, []))

  axiom in?_def1 is [a] fa (hd: a, tl)
     in?(hd, Cons(hd, tl))

  axiom in?_def2 is [a] fa (x: a, hd, tl)
     (x ~= hd => (in?(x, Cons(hd, tl)) <=> in?(x, tl)))

  axiom diff_def1 is [a] fa (l2: List a)
     diff([], l2) = []

  axiom diff_def2 is [a] fa (hd: a, tl, l2)
     in?(hd, l2) => diff (Cons(hd, tl), l2) = diff(tl, l2)

  axiom diff_def3 is [a] fa (hd: a, tl, l2)
     ~(in?(hd, l2)) => diff (Cons(hd, tl), l2) = Cons(hd, diff(tl, l2))

(* TODO
  def rev l = rev2(l,[])

  def rev2 (l,r) =
    case l of
       | []     -> r
       | hd::tl -> rev2(tl,Cons(hd,r))
*)

  axiom flatten_def1 is [a]
    flatten([]) = ([]: List a)

  axiom flatten_def2 is [a] fa (hd: List a, tl)
    flatten(Cons(hd, tl)) = ++(hd, flatten(tl))

(* TODO
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


*)

endspec
