ListUtilities qualifying spec {
  import /Library/Base

  % Ad hoc utility for removing duplicate elements in list

  op removeDuplicates  : fa(T) List T -> List T
  op ListUtilities.insert            : fa(T) T * List T -> List T
  op listUnion         : fa(T) List T * List T -> List T
  op delete            : fa(T) T * List T -> List T
  op enumerate         : Nat * Nat -> List Nat
  op index             : fa(T) List T * T -> Nat

  op collectDuplicates : fa(T) List T * (T * T -> Boolean) -> List T
  op split             : fa(T) (T -> Boolean) * List T -> (List T * List T)
  op take              : fa(T) Nat * List T -> List T
  op drop              : fa(T) Nat * List T -> List T
  op deleteNth         : fa(a) Nat * List a -> List a
  op replaceNth        : fa(a) Nat * List a * a -> List a

  op flatMap           : fa(a,b) (a -> List b) -> List a -> List b

  op findOption        : fa(a,b) (a -> Option b) -> List a -> Option b
  op findOptionIndex   : fa(a,b) (a * Nat -> Option b) -> List a -> Option (Nat * b)

  op mapWithIndex      : fa(a,b) (Nat * a -> b) -> List a -> List b

  op subset?           : fa (a) List a * List a -> Boolean

  op mapCross          : fa (a,b,c) (a * b -> c) -> List a * List b -> List c

  op mapi              : fa (a,b) (Nat * a -> b)  -> List a -> List b
  op appi              : fa (a)   (Nat * a -> ()) -> List a -> ()

  def ListUtilities.insert (e, l) = 
    case l of
      | [] -> [e]
      | e1::l1 ->
          if e = e1 then
            l
          else
            Cons (e1, ListUtilities.insert (e, l1))

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
      | elem::l -> ListUtilities.insert (elem,removeDuplicates(l))

  def listUnion (l1, l2)  = foldr ListUtilities.insert l1 l2

  def enumerate (i, j) = 
    if i > j then
      []
    else
      Cons (i, enumerate (i + 1, j))

  def split(test,l) = 
    let
      def splitAux(l,trues,falses) = 
        case l of
          | [] -> (List.rev trues,List.rev falses)
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
          if List.null elems then
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
      tl ls
    else 
      Cons (hd ls,
            deleteNth (n - 1, tl ls))

  def replaceNth(n,ls,elem) = 
    if n = 0 then
      Cons(elem,tl ls)
    else 
      Cons (hd ls,
            replaceNth (n - 1, tl ls, elem))

  def flatMap f =
    let def loop l =
      case l of
        | [] -> []
        | a::l -> (f a) @ loop l
    in
      loop

  op  findOptionIndexRec : fa(a,b) (a * Nat -> Option b) * List a * Nat -> Option (Nat * b)

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

  def mapWithIndexRec(f,ls,i) = 
    case ls of
      | [] -> []
      | x::xs -> List.cons(f(i,x),mapWithIndexRec(f,xs,i + 1))

  def mapWithIndex f l = mapWithIndexRec(f,l,0)

  def subset? (l1, l2) = List.all (fn x1 -> member (x1, l2)) l1

  def mapCross f (l1, l2) = flatMap (fn a -> List.map (fn b -> f (a, b)) l2) l1

  def mapi f xs =
    let def loop (i, xs) =
      case xs of
        | [] -> []
        | x :: xs -> List.cons (f (i, x), loop (i + 1, xs))
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
}
