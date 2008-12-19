refine /Library/Base/List by {

(* This spec refines some of the ops in the base spec List for lists to be
executable and reasonably efficient when translated to Lisp by the Specware code
generator. We do not refine op definedOnInitialSegmentOfLength because it cannot
be made executable (it involves checking a function at every natural number);
this op is only used to express subtype constraints. Also, we do not refine ops
whose definition in spec List is already executable and reasonably efficient
(also considering the refined versions of the ops that are referenced in the
original definitions). All the other ops are re-defined below. *)

op List.list : [a] Bijection (ListFunction a, List a) =
  fn f: ListFunction a ->
    let def loop (i:Nat) : List a =
        case f i of
        | None   -> Nil
        | Some x -> Cons (x, loop (i+1))
    in
    loop 0

proof Isa list__loop ()
by (pat_completeness, auto)
termination
 apply
  (relation "measure (\<lambda>(i,f). List__lengthOfListFunction f - i)")
  apply auto
 apply (subgoal_tac "i < List__lengthOfListFunction f")
  apply auto
 apply (subgoal_tac "x = List__lengthOfListFunction f")
  apply (simp add: List__definedOnInitialSegmentOfLength_def)
  apply clarify
  apply (rotate_tac 2)
  apply (drule_tac x = i in spec)
  apply (auto simp add: Option__some_p_def Option__none_p_def)
 apply (subgoal_tac
        "f definedOnInitialSegmentOfLength (List__lengthOfListFunction f)")
  apply (auto simp add: List__unique_initial_segment_length)
 apply (auto simp add: List__lengthOfListFunction_def)
 apply (rule theI')
 apply (rule List__lengthOfListFunction_Obligation_the)
 apply auto
 done
end-proof

(* The bijectivity obligation for op list as refined above follows from the
injectivity of op list as defined in spec List (which must be proved as part of
establishing the well-formedness of spec List) and from the correctness of the
refinement expressed by theorem List__list__r_def. The current
Specware-Isabelle translator does not make the proof of the bijectivity of op
list as defined in spec List available for this spec here, but future versions
of Specware will, and will probably also automatically discharge the
obligation. For now, we just ignore the obligation via "sorry". *)
proof Isa List__list_Obligation_subsort
  sorry
end-proof

(* The obligation List__list__r_def_Obligation_subsort really pertains the
definition op list in spec List, and not its refinement in spec
List_Executable. In fact, an alpha-equivalent obligation is generated from spec
List. Therefore, for now we ignore this obligation via "sorry". Once the
Specware-Isabelle translator no longer generates this redundant obligation, the
following "sorry" will be removed. *)
proof Isa List__list__r_def_Obligation_subsort
end-proof

proof Isa List__list_subtype_constr
  by (unfold List__list_def, rule List__list_Obligation_subsort)
end-proof

op List.list_1 : [a] Bijection (List a, ListFunction a) =
  fn l: List a -> fn i:Nat -> l @@ i

op [a] List.tabulate (n:Nat, f: Nat -> a) : List a =
  let def loop (i:Nat) : List a =
      if i = n then Nil
               else Cons (f i, loop (i+1))
  in
  loop 0

op [a] List.@ (l: List a, i:Nat | i < length l) infixl 30 : a =
  let hd::tl = l in  % non-empty because length > i >= 0
  if i = 0 then hd else tl @ (i-1)
proof Isa List__e_at__def1
 by (auto simp add: nth_Cons, case_tac i, auto)
end-proof

op [a] List.@@ (l:List a, i:Nat) infixl 30 : Option a =
  case l of
  | []     -> None
  | hd::tl -> if i = 0 then Some hd else tl @@ (i-1)

op List.empty? : [a] List a -> Bool = fn
  | [] -> true
  | _  -> false
proof Isa List__empty_p__def1
  by (case_tac Wild__Var_0, auto)
end-proof

op List.nonEmpty? : [a] List a -> Bool = fn
  | [] -> false
  | _  -> true
proof Isa List__nonEmpty_p__def
  by (case_tac l, auto)
end-proof

op [a] List.theElement (l: List a | ofLength? 1 l) : a =
  let [hd] = l in hd

op [a] List.in? (x:a, l: List a) infixl 20 : Bool =
  case l of
  | []     -> false
  | hd::tl -> x = hd || x in? tl

op [a] List.nin? (x:a, l: List a) infixl 20 : Bool =
  case l of
  | []     -> true
  | hd::tl -> x ~= hd && x nin? tl

op [a] List.subFromLong (l: List a, i:Nat, n:Nat | i + n <= length l) : List a =
  prefix (removePrefix (l, i), n)

op [a] List.prefix (l: List a, n:Nat | n <= length l) : List a =
  let def loop (l: List a, i:Nat) : List a =
      if i = n then Nil
               else case l of
                    | hd::tl -> Cons (hd, loop (tl, i+1))
                    | []     -> Nil  % never happens because i < n <= length
  in
  loop (l, 0)

op [a] List.suffix (l: List a, n:Nat | n <= length l) : List a =
  removePrefix (l, length l - n)

op [a] List.removePrefix (l: List a, n:Nat | n <= length l) : List a =
  if n = 0 then l
  else let _::tl = l in removePrefix (tl, n - 1)

op [a] List.removeSuffix (l: List a, n:Nat | n <= length l) : List a =
  prefix (l, length l - n)

op [a] List.head (l: List1 a) : a =
  let hd::_ = l in hd

op [a] List.last (l: List1 a) : a =
  case l of
  | [hd]   -> hd
  | hd::tl -> last tl

op [a] List.tail (l: List1 a) : List a =
  let _::tl = l in tl

op [a] List.butLast (l: List1 a) : List a =
  case l of
  | [hd]   -> Nil
  | hd::tl -> Cons (hd, butLast tl)

op [a] List.++  (l1: List a, l2: List a) infixl 25 : List a =
  case l1 of
  | [] -> l2
  | hd::tl -> Cons (hd, tl ++ l2)

op [a] List.|> (x:a, l: List a) infixr 25 : List1 a =
  Cons (x, l)

op [a] List.<| (l: List a, x:a) infixl 25 : List1 a =
  case l of
  | []     -> [x]
  | hd::tl -> Cons (hd, tl <| x)

op [a] List.update (l: List a, i:Nat, x:a | i < length l) : List a =
  let hd::tl = l in  % non-empty because length > i >= 0
  if i = 0 then Cons (x, tl) else Cons (hd, update (tl, i-1, x))

op [a] List.forall? (p: a -> Bool) : List a -> Bool = fn
  | []     -> true
  | hd::tl -> p hd && forall? p tl

op [a] List.exists? (p: a -> Bool) : List a -> Bool = fn
  | []     -> false
  | hd::tl -> p hd || exists? p tl

op [a] List.exists1? (p: a -> Bool) : List a -> Bool = fn
  | []     -> false
  | hd::tl -> (p hd && ~ (exists? p tl)) || exists1? p tl

op [a] List.foralli? (p: Nat * a -> Bool) (l: List a) : Bool =
  let def loop (l: List a, i:Nat) : Bool =
      case l of
      | []     -> true
      | hd::tl -> p (i, hd) && loop (tl, i+1)
  in
  loop (l, 0)

op [a] List.filter (p: a -> Bool) : List a -> List a = fn
  | []     -> Nil
  | hd::tl -> if p hd then Cons (hd, filter p tl) else filter p tl

op [a,b] List.zip (l1: List a, l2: List b | l1 equiLong l2) : List (a * b) =
  case (l1,l2) of
  | ([],       [])       -> Nil
  | (hd1::tl1, hd2::tl2) -> Cons ((hd1,hd2), zip (tl1,tl2))

op [a,b,c] List.zip3 (l1: List a, l2: List b, l3: List c |
                 l1 equiLong l2 && l2 equiLong l3) : List (a * b * c) =
  case (l1,l2,l3) of
  | ([],       [],       [])       -> Nil
  | (hd1::tl1, hd2::tl2, hd3::tl3) -> Cons ((hd1,hd2,hd3), zip3 (tl1,tl2,tl3))

op List.unzip : [a,b] List (a * b) -> (List a * List b | equiLong) = fn
  | []            -> (Nil, Nil)
  | (hd1,hd2)::tl -> let (tl1,tl2) = unzip tl in
                     (Cons(hd1,tl1), Cons(hd2,tl2))

op List.unzip3 : [a,b,c] List (a * b * c) ->
                    {(l1,l2,l3) : List a * List b * List c |
                     l1 equiLong l2 && l2 equiLong l3} = fn
  | [] -> (Nil, Nil, Nil)
  | (hd1,hd2,hd3)::tl -> let (tl1,tl2,tl3) = unzip3 tl in
                         (Cons(hd1,tl1), Cons(hd2,tl2), Cons(hd3,tl3))

op [a,b] List.map (f: a -> b) : List a -> List b = fn
  | []     -> Nil
  | hd::tl -> Cons (f hd, map f tl)

op [a,b,c] List.map2 (f: a * b -> c)
                (l1: List a, l2: List b | l1 equiLong l2) : List c =
  case (l1,l2) of
  | ([],       [])       -> Nil
  | (hd1::tl1, hd2::tl2) -> Cons (f(hd1,hd2), map2 f (tl1,tl2))

op [a,b,c,d] List.map3 (f: a * b * c -> d)
                  (l1: List a, l2: List b, l3: List c |
                   l1 equiLong l2 && l2 equiLong l3) : List d =
  case (l1,l2,l3) of
  | ([],       [],       [])       -> Nil
  | (hd1::tl1, hd2::tl2, hd3::tl3) -> Cons (f(hd1,hd2,hd3),
                                            map3 f (tl1,tl2,tl3))

op List.removeNones : [a] List (Option a) -> List a = fn
  | []           -> Nil
  | (Some x)::tl -> Cons (x, removeNones tl)
  |  None   ::tl ->          removeNones tl

op List.matchingOptionLists? :
  [a,b] List (Option a) * List (Option b) -> Bool = fn
  | ([],            [])            -> true
  | ((Some _)::tl1, (Some _)::tl2) -> matchingOptionLists? (tl1, tl2)
  | ( None   ::tl1,  None   ::tl2) -> matchingOptionLists? (tl1, tl2)
  | _                              -> false

op [a,b] List.mapPartial (f: a -> Option b) : List a -> List b = fn
  | []     -> Nil
  | hd::tl -> (case f hd of
              | Some x -> Cons (x, mapPartial f tl)
              | None   ->          mapPartial f tl)

op [a,b,c] List.mapPartial2 (f: a * b -> Option c)
                       (l1: List a, l2: List b | l1 equiLong l2) : List c =
  case (l1,l2) of
  | ([],       [])       -> Nil
  | (hd1::tl1, hd2::tl2) -> (case f (hd1,hd2) of
                            | Some x -> Cons (x, mapPartial2 f (tl1,tl2))
                            | None   ->          mapPartial2 f (tl1,tl2))

op [a,b,c,d] List.mapPartial3 (f: a * b * c -> Option d)
                         (l1: List a, l2: List b, l3: List c |
                          l1 equiLong l2 && l2 equiLong l3) : List d =
  case (l1,l2,l3) of
  | ([],       [],       [])       -> Nil
  | (hd1::tl1, hd2::tl2, hd3::tl3) ->
    (case f (hd1,hd2,hd3) of
    | Some x -> Cons (x, mapPartial3 f (tl1,tl2,tl3))
    | None   ->          mapPartial3 f (tl1,tl2,tl3))

op [a] List.reverse (l: List a) : List a =
  let def loop (l: List a, r: List a) : List a =
      case l of
      | []     -> r
      | hd::tl -> loop (tl, Cons (hd, r))
  in
  loop (l, Nil)

op [a] List.repeat (x:a) (n:Nat) : List a =
  if n = 0 then Nil else Cons (x, repeat x (n-1))

op List.allEqualElements? : [a] List a -> Bool = fn
  | []     -> true
  | hd::tl -> forall? (fn x:a -> x = hd) tl

op [a] List.extendLeft (l: List a, x:a, n:Nat | n >= length l) : List a =
  let len = length l in
  if n = len then l else Cons (x, extendLeft (l, x, n-1))

op [a] List.unflattenL
       (l: List a, lens: List Nat | foldl (+) 0 lens = length l)
                       : List (List a) =
  case lens of
  | [] -> []
  | len::lens -> prefix(l,len) :: unflattenL (removePrefix(l,len), lens)

op [a] List.unflatten
       (l: List a, n:PosNat | n divides length l) : List (List a) =
  if empty? l then []
  else prefix(l,n) :: unflatten (removePrefix(l,n), n)

op List.noRepetitions? : [a] List a -> Bool = fn
  | []     -> true
  | hd::tl -> hd nin? tl && noRepetitions? tl

op List.increasingNats? : List Nat -> Bool = fn
  | []       -> true
  | [_]      -> true
  | x::y::tl -> x < y && increasingNats? (Cons(y,tl))

op [a] List.positionsSuchThat (l: List a, p: a -> Bool) : InjList Nat =
  let def loop (l: List a, i:Nat) : InjList Nat =
      case l of
      | []     -> []
      | hd::tl -> if p hd then Cons (i, loop (tl, i+1)) else loop (tl, i+1)
  in
  loop (l, 0)

op [a] List.leftmostPositionSuchThat (l: List a, p: a -> Bool) : Option Nat =
  let def loop (l: List a, i:Nat) : Option Nat =
      case l of
      | []     -> None
      | hd::tl -> if p hd then Some i else loop (tl, i+1)
  in
  loop (l, 0)

op [a] List.rightmostPositionSuchThat (l: List a, p: a -> Bool) : Option Nat =
  let def loop (l: List a, i:Nat, result: Option Nat) : Option Nat =
      case l of
      | []     -> result
      | hd::tl -> loop (tl, i+1, if p hd then Some i else result)
  in
  loop (l, 0, None)

op [a] List.positionOf (l: InjList a, x:a | x in? l) : Nat =
  let Some pos = leftmostPositionSuchThat (l, fn y:a -> y = x) in pos

% auxiliary op, not in spec List; true iff l1 is a prefix of l2:
op [a] List.prefixOf? (l1: List a, l2: List a) : Bool =
  case (l1,l2) of
  | ([],       _)        -> true
  | (hd1::tl1, hd2::tl2) -> hd1 = hd2 && prefixOf? (tl1, tl2)
  | _                    -> false

op [a] List.sublistAt? (subl: List a, i:Nat, supl: List a) : Bool =
  prefixOf? (subl, removePrefix (supl, i))

op [a] List.positionsOfSublist (subl: List a, supl: List a) : InjList Nat =
  let def loop (supl': List a, i:Nat) : InjList Nat =
      % invariant: supl' = removePrefix (supl, i)
      case supl' of
      | []    -> if empty? subl then [i] else []
      | _::tl -> if prefixOf? (subl, supl') then Cons (i, loop (tl, i+1))
                                            else          loop (tl, i+1)
  in
  loop (supl, 0)

op [a] List.leftmostPositionOfSublistAndFollowing
       (subl: List a, supl: List a) : Option (Nat * List a) =
  let def loop (supl': List a, i:Nat) : Option (Nat * List a) =
      % invariant: supl' = removePrefix (supl, i)
      case supl' of
      | []    -> if empty? subl then Some (i, Nil) else None
      | _::tl -> if prefixOf? (subl, supl')
                 then Some (i, removePrefix (supl', length subl))
                 else loop (tl, i+1)
  in
  loop (supl, 0)

op [a] List.rightmostPositionOfSublistAndPreceding
       (subl: List a, supl: List a) : Option (Nat * List a) =
  let def loop (supl': List a, i:Nat, lastPosFound: Option Nat) : Option Nat =
      % invariant: supl' = removePrefix (supl, i)
      case supl' of
      | []    -> if empty? subl then Some i else lastPosFound
      | _::tl -> if prefixOf? (subl, supl') then loop (tl, i+1, Some i)
                                            else loop (tl, i+1, lastPosFound)
  in
  case loop (supl, 0, None) of
  | Some i -> Some (i, prefix (supl, i))
  | None   -> None

op [a] List.findLeftmost (p: a -> Bool) (l: List a) : Option a =
  case l of
  | []     -> None
  | hd::tl -> if p hd then Some hd else findLeftmost p tl

op [a] List.findRightmost (p: a -> Bool) (l: List a) : Option a =
  let def loop (l: List a, result: Option a) : Option a =
      case l of
      | []     -> result
      | hd::tl -> if p hd then loop (tl, Some hd) else loop (tl, result)
  in
  loop (l, None)

op [a] List.delete (x:a) : List a -> List a = fn
  | []     -> Nil
  | hd::tl -> if x = hd then delete x tl else Cons (hd, delete x tl)

op [a] List.diff (l1: List a, l2: List a) : List a =
  case l1 of
  | []     -> Nil
  | hd::tl -> if hd in? l2 then diff (tl, l2) else Cons (hd, diff (tl, l2))

op [a] List.longestCommonPrefix (l1: List a, l2: List a) : List a =
  case (l1,l2) of
  | (hd1::tl1, hd2::tl2) -> if hd1 = hd2
                            then Cons (hd1, longestCommonPrefix (tl1, tl2))
                            else Nil
  | _                    -> Nil

op List.permutation? (prm: List Nat) : Bool =
  noRepetitions? prm &&
  (let n = length prm in
  forall? (fn i:Nat -> i < n) prm)

op [a] List.permute (l: List a, prm: Permutation | l equiLong prm) : List a =
  let n = length l in
  list (fn(i:Nat) -> if i < n then l @@ (positionOf(prm,i)) else None)

op [a] List.permutationOf (l1: List a, l2: List a) infixl 20 : Bool =
  let def deleteOne (x:a, l: List a) : Option (List a) =
      % delete exactly one (leftmost) occurrence of x in l,
      % return None if x does not occur in l:
      case l of
      | []     -> None
      | hd::tl -> if hd = x then Some tl
                  else (case deleteOne (x, tl) of
                       | Some l -> Some (Cons (hd, l))
                       | None   -> None)
  in
  case l1 of
  | []     -> empty? l2
  | x::l1' -> (case deleteOne (x, l2) of
              | Some l2' -> l1' permutationOf l2'
              | None     -> false)

}
