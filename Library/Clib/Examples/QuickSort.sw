% QuickSort = 
spec

  op partitionList: fa(a) (a * a -> Boolean) * a * List(a) -> List(a) * List(a)
  def partitionList(cmp,x,l) =
    case l of
      Nil -> (Nil,Nil)
    | hd::tl ->
	let l12 = partitionList(cmp,x,tl) in
	let l1 = l12.1 in
	let l2 = l12.2 in
	if (cmp (hd,x)) then
	  (Cons(hd,l1),l2)
	else
	  (l1,Cons(hd,l2))

  op sortList : fa (a) (a * a -> Boolean) * List a -> List a
  def sortList(cmp,l) =
    case l of
        Nil -> Nil
      | hd::tl ->
          let l12 = partitionList(cmp,hd,tl) in
	  let l1 = l12.1 in
	  let l2 = l12.2 in
	  (sortList(cmp,l1)) ++ List.cons (hd, (sortList(cmp,l2)))

%  op grt: Nat * Nat -> Boolean
%  def grt(a,b) = a>b

  op showList: List Nat -> String
  def showList(l) =
    let
      def showList0(l) : String =
	case l of
	  | [] -> ""
	  | elem::l -> let s1 = Integer.toString(elem) in
	               let s2 = showList0(l) in
		       if s2 = "" then s1
		       else s1 ^ "," ^ s2
    in
    "[" ^ (showList0(l)) ^ "]"


  % testing:
  op arun:() -> ()
  def arun() =
    let l1 = [1,7,4,5,3,2,6] in
    let l2 = [7,1,6,2,3,4,5] in
    let _ = writeLine("l1 = "^showList(l1)) in
    let _ = writeLine("l2 = "^showList(l2)) in
    let _ = writeLine("sorting...") in
    let l1 = sortList(<,l1) in
    let l2 = sortList(<,l2) in
    let _ = writeLine("l1 = "^showList(l1)) in
    let _ = writeLine("l2 = "^showList(l2)) in
    if l1 = l2 then
      writeLine("l1 and l2 are equal.")
    else
      writeLine("l1 and l2 are NOT equal.")


endspec
