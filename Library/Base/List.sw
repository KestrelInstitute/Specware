List qualifying spec

  import Option, Nat

  % inductive definition of lists:

  type List.List a = | Nil | Cons a * List.List a
       % qualifier required for internal parsing reasons

  axiom induction is [a]
    fa (p : List a -> Boolean)
      p Nil &&  % base
      (fa (x:a, l:List a) p l => p(Cons(x,l))) =>  % step
      (fa (l:List a) p l)

  (* Metaslang's list displays [...], list patterns [...], and cons patterns
  ...::..., are simply syntactic shortcuts for expressions and patterns
  involving Nil and Cons. For example, [1,2,3] stands for Cons (1, Cons (2, Cons
  (3, Nil))) and hd::tl stands for Cons(hd,tl). *)

  % ops synonym of embedders:

  op [a] nil : List a = Nil

  op [a] cons   (x:a, l: List a) : List a  = Cons(x,l)

  op [a] insert (x:a, l: List a) : List a  = Cons(x,l)

  % number of elements in list:

  op length : [a] List a -> Nat = fn
    | []    -> 0
    | _::tl -> 1 + (length tl)

  % true iff list is empty:

  op null : [a] List a -> Boolean = fn
    | [] -> true
    | _  -> false

  theorem null_length is [a] fa(l) null l = (length l = 0)
  proof Isa
    apply(case_tac l)
    apply(auto)
  end-proof

  % head and tail of (non-empty) list:

  op [a] hd (l: List a | ~(null l)) : a      = let (h::_) = l in h

  op [a] tl (l: List a | ~(null l)) : List a = let (_::t) = l in t

  % concatenation of two lists:

  op [a] concat (l1: List a, l2: List a) : List a =
    case l1 of
       | []     -> l2
       | hd::tl -> Cons(hd,concat(tl,l2))

  op [a] ++  (l1: List a, l2: List a) infixl 25 : List a =
    case l1 of
       | []     -> l2
       | hd::tl -> Cons(hd,tl ++ l2)

  % n-th element of list (counting from 0, left-to-right):

  op [a] nth ((l,i) : List a * Nat | i < length l) : a =
    let hd::tl = l in  % list is non-empty because length > i >= 0
    if i = 0 then hd
             else nth(tl,i-1)

  % return elements from n-th (inclusive) to last:

  op [a] nthTail ((l,i) : List a * Nat | i <= length l) : List a =
    if i = 0 then l
             else nthTail(tl l,i-1)
  proof Isa "measure (\_lambda(l,i). i)" end-proof
  proof Isa nthTail_Obligation_subsort
  apply (auto simp add: List__null_length)
  end-proof
  proof Isa nthTail_Obligation_subsort1
  apply(auto, arith)
  end-proof

  theorem length_nthTail is
    fa(l,n: Nat) n <= length l => length(nthTail(l,n)) = length l - n
  proof Isa [simp]
    apply(induct_tac l n rule: List__nthTail.induct)
    apply(auto)
  end-proof

  % last (rightmost) element of (non-empty) list:

  op [a] last (l: List a | length(l) > 0) : a =
    let hd::tl = l in  % list is non-empty because length > i >= 0
    case tl of
      | [] -> hd
      | _ -> last(tl)

  % remove last element from list:

  op [a] butLast (l: List a | length(l) > 0) : List a =
    let hd::tl = l in  % list is non-empty because length > i >= 0
    case tl of
      | [] -> []
      | _ -> Cons(hd, butLast(tl))

  % true iff element is in list:

  op [a] member (x:a, l: List a) : Boolean =
    case l of
       | []     -> false
       | hd::tl -> if x = hd then true else member(x,tl)

  % remove first i elements from list:

  op [a] removeFirstElems (l: List a, i:Nat | i <= length l) : List a =
    if i = 0 then l
             else removeFirstElems(tl l,i-1)
  proof Isa "measure (\_lambda(l,i). i)" end-proof
  proof Isa removeFirstElems_Obligation_subsort
    apply(auto simp add: List__null_length)
  end-proof
  proof Isa removeFirstElems_Obligation_subsort1
  apply(auto, arith)
  end-proof

  theorem length_removeFirstElems is
     fa(l,i: Nat) i <= length l => length(removeFirstElems(l,i)) = length l - i
  proof Isa [simp]
    apply(induct_tac l i rule: List__removeFirstElems.induct)
    apply(auto)
  end-proof

  % sublist from the i-th element (inclusive) to the j-th element (exclusive):

  op [a] sublist ((l,i,j) : List a * Nat * Nat |
                  i <= j && j <= length l) : List a =
    let def collectFirstElems (l: List a, i: Nat | i <= length l) =
          if i = 0 then Nil
          else Cons (hd l, collectFirstElems(tl l,i-1)) in
    collectFirstElems(removeFirstElems(l,i),j-i)

  proof Isa sublist__collectFirstElems_Obligation_subsort
    apply(auto simp add: List__null_length)
  end-proof
  proof Isa sublist__collectFirstElems_Obligation_subsort0
    apply(auto simp add: List__null_length)
  end-proof
  proof Isa sublist__collectFirstElems_Obligation_subsort2
  apply(auto, arith)
  end-proof
  proof Isa sublist__collectFirstElems "measure (\_lambda(l,i). i)" end-proof

  theorem sublist_whole is
    [a] fa (l: List a) sublist(l,0,length l) = l
  proof Isa [simp]
    apply(induct_tac l)
    apply(auto)
  end-proof
  proof Isa List__sublist_Obligation_subsort1
  apply(auto, arith)
  end-proof

  % homomorphically apply f to all elements:

  op [a,b] map (f: a -> b) (l: List a) : List b =
    case l of
       | []     -> [] 
       | hd::tl -> Cons(f hd,map f tl)

  % like previous one, but remove elements mapped to None:

  op [a,b] mapPartial (f: a -> Option b) (l: List a) : List b =
    case l of
       | []     -> []
       | hd::tl -> (case f hd of
                       | Some x -> Cons(x,mapPartial f tl)
                       | None   -> mapPartial f tl)

  % fold from left/right:

  op [a,b] foldl (f: a * b -> b) (base:b) (l: List a) : b =
    case l of
       | []     -> base
       | hd::tl -> foldl f (f(hd,base)) tl

  op [a,b] foldr (f: a * b -> b) (base:b) (l: List a) : b =
    case l of
       | []     -> base
       | hd::tl -> f (hd, foldr f base tl)

  % true iff some/each element satisfies p:

  op [a] exists (p: a -> Boolean) (l: List a) : Boolean =
    case l of
       | []     -> false
       | hd::tl -> if (p hd) then true else (exists p tl)

  op [a] all (p: a -> Boolean) (l: List a) : Boolean =
    case l of
       | []     -> true
       | hd::tl -> if (p hd) then all p tl else false

  % filter away elements that do not satisfy p:

  op [a] filter (p: a -> Boolean) (l: List a) : List a =
    case l of
       | []     -> []
       | hd::tl -> if (p hd) then Cons(hd,filter p tl) else (filter p tl)

  % remove from l1 all the elements that occur in l2:

  op [a] diff (l1: List a, l2: List a) : List a =
    case l1 of
       | []     -> []
       | hd::tl -> if member(hd,l2) then diff(tl,l2) 
                                    else Cons(hd,diff(tl,l2))
  proof Isa "measure (\_lambda(l1,l2). length l1)" end-proof

  % reverse list:

  op [a] rev2 (l: List a, r: List a) : List a =  % auxiliary
    case l of
       | []     -> r
       | hd::tl -> rev2(tl,Cons(hd,r))
  proof Isa "measure (\_lambda(l,r). length l)" end-proof

  op [a] rev (l: List a) : List a =  % main
    rev2(l,[])

  % concatenate all the lists in the list, in order:

  op [a] flatten (l: List (List a)) : List a =
    case l of
       | []     -> []
       | hd::tl -> concat(hd,flatten tl)

  % find first element in list that satisfies p (None if none does):

  op [a] find (p: a -> Boolean) (l: List a) : Option(a) =
    case l of
       | []     -> None
       | hd::tl -> if (p hd) then Some hd else find p tl

  % create list [f 0, ..., f (n-1)]:

  op [a] tabulate (n:Nat, f: Nat -> a) : List a =
    let def tabulateAux (i : Nat, l : List a) : List a =
            if i = 0 then l
            else tabulateAux(i-1,Cons(f(i-1),l)) in
    tabulateAux(n,[])
  proof Isa tabulate__tabulateAux "measure (\_lambda(i,l,f). i)" end-proof

  % if some element in list satisfies p, return it and the list of elements
  % preceding its first occurrence in the list (e.g. firstUpTo even [1,2,3,4]
  % = Some ([1], 2)), otherwise return None:

  op [a] firstUpTo (p: a -> Boolean) (l: List a) : Option (a * List a) =
    case l of
       | []     -> None
       | hd::tl -> if p hd then Some(hd,Nil)
                   else case firstUpTo p tl of
                           | None       -> None
                           | Some(x,l1) -> Some(x,Cons(hd,l1))

  % if some element in list satisfies p, return the list elements preceding its
  % first occurrence, then the element, the list of elements following its first
  % occurrence (e.g. splitList even [1,2,3,4] = Some ([1], 2, [3,4])), otherwise
  % return None:

  op [a] splitList (p: a -> Boolean) (l: List a) : Option(List a * a * List a) =
    case l of
       | []     -> None
       | hd::tl -> if (p hd) then Some(Nil,hd,tl)
                   else case splitList p tl of
                           | None -> None
                           | Some(l1,x,l2) -> Some(Cons(hd,l1),x,l2)

  % if subl is a sublist of supl (in the sense that supl = ... ++ subl ++ ...),
  % return starting position of first occurrence of subl within supl (there could
  % be more than one), as well as the list of elements following subl within
  % supl (e.g. locationOf ([1,2], [7,8,1,2,4,5,1,2]) = Some (2, [4,5,1,2])),
  % otherwise return None:

  op [a] locationOf (subl: List a, supl: List a) : Option (Nat * List a) =
    let def checkPrefix (subl : List a, supl : List a) : Option(List a) =
            % checks if subl is prefix of supl and if so
            % returns what remains of supl after subl
            case (subl,supl) of
               | (subhd::subtl, suphd::suptl) -> if subhd = suphd
                                                 then checkPrefix(subtl,suptl)
                                                 else None
               | ([],_)                       -> Some supl
               | _                            -> None in
    let def locationOfNonEmpty
            (subl : List a, supl : List a, pos : Nat | subl ~= [])
            : Option (Nat * List a) =
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

  proof Isa locationOf__locationOfNonEmpty
    "measure (\_lambda(subl,supl,pos). length supl)"
  end-proof

  (* Given a comparison function over type a, type List a can be linearly
  ordered and compared element-wise and regarding the empty list smaller than
  any non-empty list. *)

  op [a] compare
         (comp: a * a -> Comparison) (l1: List a, l2: List a) : Comparison =
    case (l1,l2) of
       | (hd1::tl1,hd2::tl2) -> (case comp(hd1,hd2) of
                                    | Equal  -> compare comp (tl1,tl2)
                                    | result -> result)
       | ([],      []      ) -> Equal
       | ([],      _::_    ) -> Less
       | (_::_,    []      ) -> Greater


  % deprecated:

  op [a] app (f: a -> ()) (l: List a) : () =
    case l of
       | []     -> ()
       | hd::tl -> (f hd; app f tl)

   op [a,b] isoList: Bijection(a,b) -> Bijection(List a, List b) =
    fn iso_elem -> map iso_elem

  % mapping to Isabelle:
  proof Isa Thy_Morphism List
    type List.List \_rightarrow list
    List.nil \_rightarrow []
    List.cons \_rightarrow # Right 23
    List.insert \_rightarrow # Right 23
    List.length \_rightarrow length
    List.null \_rightarrow null
    List.hd \_rightarrow  hd  
    List.tl \_rightarrow  tl
    List.concat \_rightarrow  @ Left 25
    List.++ \_rightarrow  @ Left 25
    List.nth \_rightarrow ! Left 35
    List.last \_rightarrow  last
    List.butLast \_rightarrow  butlast
    List.rev \_rightarrow rev
    List.flatten \_rightarrow concat
    List.member \_rightarrow  mem Left 22
    List.map \_rightarrow map
    List.mapPartial \_rightarrow  filtermap  
    List.exists \_rightarrow list_ex  
    List.all \_rightarrow  list_all  
    List.filter \_rightarrow  filter  
  end-proof

endspec
