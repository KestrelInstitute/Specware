PrList qualifying spec

  import ../Base/List

  % types:

  %type List.List a = | Nil | Cons a * List.List a
       % qualifier required for internal parsing reasons

  axiom induction is [a]
    fa (p : List a -> Boolean)
      p Nil &&  % base
      (fa (x:a, l:List a) p l => p(Cons(x,l))) =>  % step
      (fa (l:List a) p l)

  % ops on lists:
(*
  op nil             : [a]   List a
  op cons            : [a]   a * List a -> List a
  op insert          : [a]   a * List a -> List a
  op length          : [a]   List a -> Nat
  op null            : [a]   List a -> Boolean
  op hd              : [a]   {l : List a | ~(null l)} -> a
  op tl              : [a]   {l : List a | ~(null l)} -> List a
  op concat          : [a]   List a * List a -> List a
  op ++ infixl 25    : [a]   List a * List a -> List a
%% Deprecated for some time so it should be safe to remove
%  op @  infixl 25    : [a]   List a * List a -> List a
  op nth             : [a]   {(l,i) : List a * Nat | i < length l} -> a
  op nthTail         : [a]   {(l,i) : List a * Nat | i < length l} ->
                               List a
  op last            : [a]   {l: List a | length(l) > 0} -> a
  op butLast         : [a]   {l: List a | length(l) > 0} -> List a
  op member          : [a]   a * List a -> Boolean
%  op sublist         : [a]   {(l,i,j) : List a * Nat * Nat |
%                                i <= j && j <= length l} -> List a
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
*)

  axiom nilIsNil is nil = Nil

  axiom consIsCons is fa (x, l)  cons(x,l) = Cons(x,l)

  axiom insert_def is fa (x, l) insert(x,l) = Cons(x,l)

  axiom length_nil is length([]) = 0

  axiom length_cons is fa (x, l) length(Cons(x, l)) = 1 + length(l)

  axiom nullNull is null([])

  axiom nullCons is fa (x, l) ~(null(Cons(x, l)))

  axiom hdCons is fa (x, l) hd (Cons(x, l)) = x

  axiom tlCons is fa (x, l) tl (Cons(x, l)) = l

  axiom concatNull is fa (l) concat([], l) = l

  axiom concatCons is fa (x1, l1, l2)
     concat(Cons(x1, l1), l2) = Cons(x1, concat(l1, l2))

  axiom concat2_def is fa (s1, s2) ++ (s1,s2) = concat(s1,s2)

%  def @ (s1,s2) = concat(s1,s2)

  axiom nth_def1 is  fa(hd, tl)
     nth(Cons(hd,tl),0) = hd

  axiom nth_def2 is  fa(hd, tl, i) (i > 0) =>
     nth(Cons(hd,tl),i) = nth(tl, i-1)

  axiom nthTail_def1 is fa (hd, tl)
     nthTail(tl,0) = tl

  axiom nthTail_def2 is fa (hd, tl, i) (i > 0) =>
     nthTail(Cons(hd,tl),i) = nthTail(tl, i-1)

  axiom last_def1 is fa (hd)
    last(Cons(hd, [])) = hd

  axiom last_def2 is fa (hd, tl)
    tl ~= [] => last(Cons(hd, tl)) = last(tl)

  axiom butLast_def1 is fa (hd)
    butLast(Cons(hd, [])) = []

  axiom butLast_def2 is fa (hd, tl)
    tl ~= [] => butLast(Cons(hd, tl)) = Cons(hd, butLast(tl))

  axiom member_def1 is fa (x)
    ~(member(x, []))

  axiom member_def1 is fa (hd, tl)
     member(hd, Cons(hd, tl))

  axiom member_def2 is fa (x, hd, tl)
     (x ~= hd => (member(x, Cons(hd, tl)) <=> member(x, tl)))

  axiom diff_def1 is fa (l2)
     diff([], l2) = []

  axiom diff_def2 is fa (hd, tl, l2)
     member(hd, l2) => diff (Cons(hd, tl), l2) = diff(tl, l2)

  axiom diff_def3 is fa (hd, tl, l2)
     ~(member(hd, l2)) => diff (Cons(hd, tl), l2) = Cons(hd, diff(tl, l2))

(* TODO
  def rev l = rev2(l,[])

  def rev2 (l,r) =
    case l of
       | []     -> r
       | hd::tl -> rev2(tl,Cons(hd,r))
*)

  axiom flatten_def1 is fa (l)
    flatten([]) = []

  axiom flatten_def2 is fa (hd, tl)
    flatten(Cons(hd, tl)) = concat(hd, flatten(tl))

(* TODO
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


*)

endspec
