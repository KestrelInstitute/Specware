(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ListUtilities qualifying spec 
  % Ad hoc utility for removing duplicate elements in list

  op removeDuplicates  : [T] List T -> List T
  op insert            : [T] T * List T -> List T
  op listUnion         : [T] List T * List T -> List T
  op delete            : [T] T * List T -> List T
  op enumerate         : Nat * Nat -> List Nat
  op index             : [T] List T * T -> Nat

  op collectDuplicates : [T] List T * (T * T -> Bool) -> List T
  op split             : [T] (T -> Bool) * List T -> (List T * List T)
  op take              : [T] Nat * List T -> List T
  op drop              : [T] Nat * List T -> List T
  op deleteNth         : [a] Nat * List a -> List a
  op replaceNth        : [a] Nat * List a * a -> List a

  op flatMap           : [a,b] (a -> List b) -> List a -> List b

  op findOption        : [a,b] (a -> Option b) -> List a -> Option b
  op findOptionIndex   : [a,b] (a * Nat -> Option b) -> List a -> Option (Nat * b)
  op findIndex         : [a]   (a -> Bool) -> List a -> Option(Nat * a)

  op mapWithIndexRec   : [a,b] (Nat * a -> b) * List a * Nat -> List b
  op mapWithIndex      : [a,b] (Nat * a -> b) -> List a -> List b

  op subset?           : [a] List a * List a -> Bool

  op mapCross          : [a,b,c] (a * b -> c) -> List a * List b -> List c

  op mapi              : [a,b] (Nat * a -> b)  -> List a -> List b
  op appi              : [a]   (Nat * a -> ()) -> List a -> ()

  op tailListList: [a] List a * List a -> Option (List a)

  def insert (e, l) = 
    case l of
      | [] -> [e]
      | e1::l1 ->
          if e = e1 then
            l
          else
            Cons (e1, insert (e, l1))

  def delete(e,l) = 
    case l of
      | [] -> []
      | e1::l1 -> 
          if e = e1 then
            delete(e,l1)
          else
            Cons(e1,delete(e,l1))

  def removeDuplicates(l) = 
    case l of
      | [] -> l 
      | elem::l -> insert (elem,removeDuplicates(l))

  op [a] memberEquiv? (x: a, l: List a, equiv: a * a -> Bool): Bool =
    case l of
      | [] -> false
      | elem::rl ->
        equiv(x, elem) || memberEquiv?(x, rl, equiv)

  op [a] removeDuplicatesEquiv (l: List a, equiv: a * a -> Bool): List a =
    case l of
      | [] -> []
      | elem::rl ->
        let r = removeDuplicatesEquiv(rl, equiv) in
        if memberEquiv?(elem, rl, equiv)
          then r
          else elem :: r

  def listUnion (l1, l2)  = foldl (fn (result,x) -> insert(x,result)) l1 l2

  def enumerate (i, j) = 
    if i > j then
      []
    else
      Cons (i, enumerate (i + 1, j))

  def split(test,l) = 
    let
      def splitAux(l,trues,falses) = 
        case l of
          | [] -> (reverse trues,reverse falses)
          | elem::elems -> 
             if test elem then
               splitAux(elems,Cons(elem,trues),falses)
             else
              splitAux(elems,trues,Cons(elem,falses))
    in
      splitAux(l,[],[])

  def collectDuplicates(l,eqTest) = 
    case l of
      | [] -> []
      | elem::l -> 
          let (elems,rest) = split(fn e -> eqTest(elem,e),l) in
          if empty? elems then
            collectDuplicates(rest,eqTest)
          else
            Cons(elem,collectDuplicates(rest,eqTest))        

  %% Return index of first occurrence of T counting from 1.
  %% return 0 if the element is not found.

  def index(ls,elem) = 
    let
      def indexRec(ls,counter) = 
        case ls of
          | [] -> 0
          | first::rest -> 
              if elem = first then
                counter
              else
                indexRec(rest,counter + 1)
      in
          indexRec(ls,1)

  %% take: first n.
  %% drop: all but first n.
  %% deleteNth : delete the n'th element counting from 0.

  def take (n, es) =
    if n = 0 then
      []
    else
      case es of
        | []  -> []
        | e::es -> Cons (e, take (n -  1, es))

  def drop (n, es) =
    if n = 0 then
      es
    else
      case es of
        | [] -> []
        | e::es -> drop (n - 1, es)

  def deleteNth(n,ls) = 
    if n = 0 then
      tail ls
    else 
      Cons (head ls,
            deleteNth (n - 1, tail ls))

  def replaceNth(n,ls,elem) = 
    if n = 0 then
      Cons(elem,tail ls)
    else 
      Cons (head ls,
            replaceNth (n - 1, tail ls, elem))

  def flatMap f =
    let def loop l =
      case l of
        | [] -> []
        | a::l -> (f a) ++ loop l
    in
      loop

  op  findOptionIndexRec : [a,b] (a * Nat -> Option b) * List a * Nat -> Option (Nat * b)

  def findOptionIndexRec(f,xs,i) = 
    case xs of
      | [] -> None
      | x::xs -> 
          (case f(x,i) of
            | Some y -> Some(i,y)
            | None -> findOptionIndexRec (f,xs,i + 1))

  def findOptionIndex f l = findOptionIndexRec(f,l,0)

  def findOption f l = 
    case l of
      | [] -> None 
      | l::ls -> 
          (case f l of
            | None -> findOption f ls
            | result -> result)

  def findIndex p l =
    let def findIndexRec(l, n) =
            case l of
	      | [] -> None
	      | hd::tl -> if p hd then Some (n, hd) else findIndexRec(tl, n+1) in
      findIndexRec(l, 0)
    

  def mapWithIndexRec(f,ls,i) = 
    case ls of
      | [] -> []
      | x::xs -> Cons(f(i,x),mapWithIndexRec(f,xs,i + 1))

  def mapWithIndex f l = mapWithIndexRec(f,l,0)

  def subset? (l1, l2) = forall? (fn x1 -> x1 in? l2) l1

  def mapCross f (l1, l2) = flatMap (fn a -> List.map (fn b -> f (a, b)) l2) l1

  def mapi f xs =
    let def loop (i, xs) =
      case xs of
        | [] -> []
        | x :: xs -> Cons (f (i, x), loop (i + 1, xs))
    in
      loop (0, xs)

  def appi f xs =
    let def loop (i, xs) =
      case xs of
        | [] -> ()
        | x :: xs ->
           let _ = f (i, x) in
           loop (i + 1, xs)
    in
      loop (0, xs)

  (**
   * When l2 is a prefix of l1 return the tail of l1 after the l2 prefix,
   * otherwise return None.
   * e.g. tailListList([1, 2, 3], [1, 2]) = Some [3]
   *      tailListList([1, 2, 3], [1]) = Some [2, 3]
   *      tailListList([1, 2, 3], [1, 2, 3]) = Some []
   *      tailListList([1, 2, 3], []) = Some [1, 2, 3]
   *      tailListList([1, 2, 3], [2]) = None
   **)
 
  def tailListList(l1, l2) =
    if empty?(l2)
      then Some l1
    else
      let l1Head = subFromTo(l1, 0, length(l2)) in
      if l1Head = l2 
	then Some (removePrefix(l1, length(l2)))
      else None

end-spec