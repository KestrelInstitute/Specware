spec
import /Library/Base/List

(* This spec refines some of the ops in the base spec List for lists to be
executable and reasonably efficient when translated to Lisp by the Specware code
generator. We do not refine op definedOnInitialSegmentOfLength because it cannot
be made executable (it involves checking a function at every natural number);
this op is only used to express subtype constraints. Also, we do not refine ops
whose definition in spec List is already executable and reasonably efficient
(also considering the refined versions of the ops that are referenced in the
original definitions). All the other ops are re-defined below. *)

refine def list : [a] Bijection (ListFunction a, List a) =
  fn f: ListFunction a ->
    let def loop (i:Nat) : List a =
        case f i of
        | None   -> Nil
        | Some x -> Cons (x, loop (i+1))
    in
    loop 0

proof Isa list__1__loop ()
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

proof Isa -verbatim
lemma List__list__1__loop_Suc:
"(\<exists>l. f definedOnInitialSegmentOfLength l) \<Longrightarrow>
 List__list__1__loop (Suc i, f) = List__list__1__loop (i, \<lambda>j. f (Suc j))"
proof -
 def Lf \<equiv> "List__lengthOfListFunction f"
 assume fseg: "\<exists>l. f definedOnInitialSegmentOfLength l"
 with List__lengthOfListFunction_Obligation_the
  have "f definedOnInitialSegmentOfLength (List__lengthOfListFunction f)"
   by (auto simp: List__lengthOfListFunction_def intro: theI')
 with Lf_def have fseg_Lf: "f definedOnInitialSegmentOfLength Lf" by auto
 from fseg_Lf
  have "(\<lambda>j. f (Suc j)) definedOnInitialSegmentOfLength (Lf - 1)"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
 hence f'seg: "\<exists>l'.
                 (\<lambda>j. f (Suc j)) definedOnInitialSegmentOfLength l'"
  by auto
 show ?thesis
 proof (induct n \<equiv> "Lf - Suc i" arbitrary: i)
  case 0
  hence "Lf \<le> Suc i" by auto
  with fseg_Lf have "f (Suc i) = None"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  with fseg have "List__list__1__loop (Suc i, f) = []" by auto
  from `f (Suc i) = None` have "(\<lambda>j. f (Suc j)) i = None" by auto
  with f'seg have "List__list__1__loop (i, \<lambda>j. f (Suc j)) = []" by auto
  with `List__list__1__loop (Suc i, f) = []` show ?case by auto
 next
  case (Suc n)
  hence "Lf - Suc (Suc i) = n" by auto
  with Suc.hyps
  have IH: "List__list__1__loop (Suc (Suc i), f) =
            List__list__1__loop (Suc i, \<lambda>j. f (Suc j))" by auto
  from Suc have "Suc i < Lf" by auto
  with fseg_Lf obtain x where "f (Suc i) = Some x"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  with fseg have "List__list__1__loop (Suc i, f) =
                  x # List__list__1__loop (Suc (Suc i), f)" by auto
  from `f (Suc i) = Some x` have "(\<lambda>j. f (Suc j)) i = Some x" by auto
  with f'seg have "List__list__1__loop (i, \<lambda>j. f (Suc j)) =
                   x # List__list__1__loop (Suc i, \<lambda>j. f (Suc j))" by auto
  with `List__list__1__loop (Suc i, f) = x # List__list__1__loop (Suc (Suc i), f)` IH
   show ?case by auto
 qed
qed
end-proof

(* The bijectivity obligation for op list as refined above follows from the
injectivity of op list as defined in spec List (which must be proved as part of
establishing the well-formedness of spec List) and from the correctness of the
refinement expressed by theorem List__list__r_def. The current
Specware-Isabelle translator does not make the proof of the bijectivity of op
list as defined in spec List available for this spec here, but future versions
of Specware will, and will probably also automatically discharge the
obligation. For now, we just ignore the obligation via "sorry". *)
proof Isa List__list_Obligation_subtype
  sorry
end-proof

proof Isa List__list__r_def
proof (cases "f 0")
 case None
 assume fseg: "\<exists>(n::nat). f definedOnInitialSegmentOfLength n"
 with None show ?thesis by (auto simp: List__list_def)
next
 case (Some x)
 assume fseg: "\<exists>(n::nat). f definedOnInitialSegmentOfLength n"
 with Some have "List__list f = x # List__list__1__loop (1, f)"
  by (auto simp: List__list_def)
 also with fseg List__list__1__loop_Suc
  have "\<dots> = x # List__list__1__loop (0, \<lambda>i. f (i + 1))"
   by (auto simp del: List__list__1__loop.simps)
 also with Some
  have "\<dots> =
        (case f 0 of None \<Rightarrow> []
                   | Some x \<Rightarrow> x #
                                      (List__list (\<lambda>i. f (i + 1))))"
   by (auto simp: List__list_def)
 finally show ?thesis .
qed
end-proof

refine def list_1 : [a] Bijection (List a, ListFunction a) =
  fn l: List a -> fn i:Nat -> l @@ i

refine def [a] tabulate (n: Nat, f: Nat -> a) : List a =
  let def loop (i: Nat, result: List a) : List a =
      if i = 0 then result
               else let i = i-1 in
                    loop(i, f i :: result)
  in
  loop (n, [])

refine def [a] @ (l: List a, i:Nat | i < length l) : a =
  let hd::tl = l in  % non-empty because length > i >= 0
  if i = 0 then hd else tl @ (i-1)
proof Isa List__e_at__def1
 by (auto simp add: nth_Cons, case_tac i, auto)
end-proof

refine def [a] @@ (l:List a, i:Nat) : Option a =
  case l of
  | []     -> None
  | hd::tl -> if i = 0 then Some hd else tl @@ (i-1)

refine def empty? : [a] List a -> Bool = fn
  | [] -> true
  | _  -> false
proof Isa List__empty_p__def1
  by (case_tac Wild__Var_0, auto)
end-proof

refine def nonEmpty? : [a] List a -> Bool = fn
  | [] -> false
  | _  -> true
proof Isa List__nonEmpty_p__def
  by (case_tac l, auto)
end-proof

refine def [a] theElement (l: List a | ofLength? 1 l) : a =
  let [hd] = l in hd

refine def [a] in? (x:a, l: List a) : Bool =
  case l of
  | []     -> false
  | hd::tl -> x = hd || x in? tl

refine def [a] nin? (x:a, l: List a) : Bool =
  case l of
  | []     -> true
  | hd::tl -> x ~= hd && x nin? tl

refine def [a] subFromLong (l: List a, i:Nat, n:Nat | i + n <= length l) : List a =
  prefix (removePrefix (l, i), n)

%% Make tail-recursive so that it scales for very long lists at the expense of doing a reverse at end.
refine def [a] prefix (l: List a, n: Nat | n <= length l) : List a =
  let def loop (l: List a, i: Nat, result: List a) : List a =
      if i = 0 then result
               else case l of
                    | hd::tl -> loop (tl, i-1, hd::result)
                    | []     -> result  % never happens because i < n <= length
  in
  reverse(loop (l, n, []))

refine def [a] suffix (l: List a, n:Nat | n <= length l) : List a =
  removePrefix (l, length l - n)

refine def [a] removePrefix (l: List a, n:Nat | n <= length l) : List a =
  if n = 0 then l
  else let _::tl = l in removePrefix (tl, n - 1)

%refine def [a] removeSuffix (l: List a, n:Nat | n <= length l) : List a =
%  prefix (l, length l - n)

refine def [a] head (l: List1 a) : a =
  let hd::_ = l in hd

refine def [a] last (l: List1 a) : a =
  case l of
  | [hd]   -> hd
  | hd::tl -> last tl

refine def [a] tail (l: List1 a) : List a =
  let _::tl = l in tl

refine def [a] butLast (l: List1 a) : List a =
  case l of
  | [hd]   -> Nil
  | hd::tl -> Cons (hd, butLast tl)

refine def [a] ++  (l1: List a, l2: List a) : List a =
  case l1 of
  | [] -> l2
  | hd::tl -> Cons (hd, tl ++ l2)

refine def [a] |> (x:a, l: List a) : List1 a =
  Cons (x, l)

refine def [a] <| (l: List a, x:a) : List1 a =
  case l of
  | []     -> [x]
  | hd::tl -> Cons (hd, tl <| x)

refine def [a] update (l: List a, i:Nat, x:a | i < length l) : List a =
  let hd::tl = l in  % non-empty because length > i >= 0
  if i = 0 then Cons (x, tl) else Cons (hd, update (tl, i-1, x))

refine def [a] forall? (p: a -> Bool) : List a -> Bool = fn
  | []     -> true
  | hd::tl -> p hd && forall? p tl

refine def [a] exists? (p: a -> Bool) : List a -> Bool = fn
  | []     -> false
  | hd::tl -> p hd || exists? p tl

refine def [a] exists1? (p: a -> Bool) : List a -> Bool = fn
  | []     -> false
  | hd::tl -> (p hd && ~ (exists? p tl)) || exists1? p tl

refine def [a] foralli? (p: Nat * a -> Bool) (l: List a) : Bool =
  let def loop (l: List a, i:Nat) : Bool =
      case l of
      | []     -> true
      | hd::tl -> p (i, hd) && loop (tl, i+1)
  in
  loop (l, 0)

refine def [a] filter (p: a -> Bool) (l: List a): List a =
  reverse (foldl (fn (result, x) -> if p x then x::result else result) [] l)

refine def [a,b] zip (l1: List a, l2: List b | l1 equiLong l2) : List (a * b) =
  case (l1,l2) of
  | ([],       [])       -> Nil
  | (hd1::tl1, hd2::tl2) -> Cons ((hd1,hd2), zip (tl1,tl2))

refine def [a,b,c] zip3 (l1: List a, l2: List b, l3: List c |
                 l1 equiLong l2 && l2 equiLong l3) : List (a * b * c) =
  case (l1,l2,l3) of
  | ([],       [],       [])       -> Nil
  | (hd1::tl1, hd2::tl2, hd3::tl3) -> Cons ((hd1,hd2,hd3), zip3 (tl1,tl2,tl3))

refine def unzip : [a,b] List (a * b) -> (List a * List b | equiLong) = fn
  | []            -> (Nil, Nil)
  | (hd1,hd2)::tl -> let (tl1,tl2) = unzip tl in
                     (Cons(hd1,tl1), Cons(hd2,tl2))

refine def unzip3 : [a,b,c] List (a * b * c) ->
                    {(l1,l2,l3) : List a * List b * List c |
                     l1 equiLong l2 && l2 equiLong l3} = fn
  | [] -> (Nil, Nil, Nil)
  | (hd1,hd2,hd3)::tl -> let (tl1,tl2,tl3) = unzip3 tl in
                         (Cons(hd1,tl1), Cons(hd2,tl2), Cons(hd3,tl3))

refine def [a,b] map (f: a -> b) (l: List a): List b =
  reverse (foldl (fn (result, x) -> f x::result) [] l)

refine def [a,b,c] map2 (f: a * b -> c)
                (l1: List a, l2: List b | l1 equiLong l2) : List c =
  case (l1,l2) of
  | ([],       [])       -> Nil
  | (hd1::tl1, hd2::tl2) -> Cons (f(hd1,hd2), map2 f (tl1,tl2))

refine def [a,b,c,d] map3 (f: a * b * c -> d)
                  (l1: List a, l2: List b, l3: List c |
                   l1 equiLong l2 && l2 equiLong l3) : List d =
  case (l1,l2,l3) of
  | ([],       [],       [])       -> Nil
  | (hd1::tl1, hd2::tl2, hd3::tl3) -> Cons (f(hd1,hd2,hd3),
                                            map3 f (tl1,tl2,tl3))

refine def removeNones : [a] List (Option a) -> List a = fn
  | []           -> Nil
  | (Some x)::tl -> Cons (x, removeNones tl)
  |  None   ::tl ->          removeNones tl

refine def matchingOptionLists? :
  [a,b] List (Option a) * List (Option b) -> Bool = fn
  | ([],            [])            -> true
  | ((Some _)::tl1, (Some _)::tl2) -> matchingOptionLists? (tl1, tl2)
  | ( None   ::tl1,  None   ::tl2) -> matchingOptionLists? (tl1, tl2)
  | _                              -> false

refine def [a,b] mapPartial (f: a -> Option b) : List a -> List b = fn
  | []     -> Nil
  | hd::tl -> (case f hd of
              | Some x -> Cons (x, mapPartial f tl)
              | None   ->          mapPartial f tl)

refine def [a,b,c] mapPartial2 (f: a * b -> Option c)
                       (l1: List a, l2: List b | l1 equiLong l2) : List c =
  case (l1,l2) of
  | ([],       [])       -> Nil
  | (hd1::tl1, hd2::tl2) -> (case f (hd1,hd2) of
                            | Some x -> Cons (x, mapPartial2 f (tl1,tl2))
                            | None   ->          mapPartial2 f (tl1,tl2))

refine def [a,b,c,d] mapPartial3 (f: a * b * c -> Option d)
                         (l1: List a, l2: List b, l3: List c |
                          l1 equiLong l2 && l2 equiLong l3) : List d =
  case (l1,l2,l3) of
  | ([],       [],       [])       -> Nil
  | (hd1::tl1, hd2::tl2, hd3::tl3) ->
    (case f (hd1,hd2,hd3) of
    | Some x -> Cons (x, mapPartial3 f (tl1,tl2,tl3))
    | None   ->          mapPartial3 f (tl1,tl2,tl3))

refine def [a] reverse (l: List a) : List a =
  let def loop (l: List a, r: List a) : List a =
      case l of
      | []     -> r
      | hd::tl -> loop (tl, Cons (hd, r))
  in
  loop (l, Nil)

refine def [a] repeat (x:a) (n:Nat) : List a =
  if n = 0 then Nil else Cons (x, repeat x (n-1))

refine def allEqualElements? : [a] List a -> Bool = fn
  | []     -> true
  | hd::tl -> forall? (fn x:a -> x = hd) tl

refine def [a] extendLeft (l: List a, x:a, n:Nat | n >= length l) : List a =
  let len = length l in
  if n = len then l else Cons (x, extendLeft (l, x, n-1))

refine def [a] unflattenL
       (l: List a, lens: List Nat | foldl (+) 0 lens = length l)
                       : List (List a) =
  case lens of
  | [] -> []
  | len::lens -> prefix(l,len) :: unflattenL (removePrefix(l,len), lens)

refine def [a] unflatten
       (l: List a, n:PosNat | n divides length l) : List (List a) =
  if empty? l then []
  else prefix(l,n) :: unflatten (removePrefix(l,n), n)

refine def noRepetitions? : [a] List a -> Bool = fn
  | []     -> true
  | hd::tl -> hd nin? tl && noRepetitions? tl

refine def increasingNats? : List Nat -> Bool = fn
  | []       -> true
  | [_]      -> true
  | x::y::tl -> x < y && increasingNats? (Cons(y,tl))

refine def [a] positionsSuchThat (l: List a, p: a -> Bool) : InjList Nat =
  let def loop (l: List a, i:Nat) : InjList Nat =
      case l of
      | []     -> []
      | hd::tl -> if p hd then Cons (i, loop (tl, i+1)) else loop (tl, i+1)
  in
  loop (l, 0)

refine def [a] leftmostPositionSuchThat (l: List a, p: a -> Bool) : Option Nat =
  let def loop (l: List a, i:Nat) : Option Nat =
      case l of
      | []     -> None
      | hd::tl -> if p hd then Some i else loop (tl, i+1)
  in
  loop (l, 0)

refine def [a] rightmostPositionSuchThat (l: List a, p: a -> Bool) : Option Nat =
  let def loop (l: List a, i:Nat, result: Option Nat) : Option Nat =
      case l of
      | []     -> result
      | hd::tl -> loop (tl, i+1, if p hd then Some i else result)
  in
  loop (l, 0, None)

refine def [a] positionOf (l: InjList a, x:a | x in? l) : Nat =
  let Some pos = leftmostPositionSuchThat (l, fn y:a -> y = x) in pos

% auxiliary op, not in spec List; true iff l1 is a prefix of l2:
op [a] List.prefixOf? (l1: List a, l2: List a) : Bool =
  case (l1,l2) of
  | ([],       _)        -> true
  | (hd1::tl1, hd2::tl2) -> hd1 = hd2 && prefixOf? (tl1, tl2)
  | _                    -> false

refine def [a] sublistAt? (subl: List a, i:Nat, supl: List a) : Bool =
  prefixOf? (subl, removePrefix (supl, i))

refine def [a] positionsOfSublist (subl: List a, supl: List a) : InjList Nat =
  let def loop (supl': List a, i:Nat) : InjList Nat =
      % invariant: supl' = removePrefix (supl, i)
      case supl' of
      | []    -> if empty? subl then [i] else []
      | _::tl -> if prefixOf? (subl, supl') then Cons (i, loop (tl, i+1))
                                            else          loop (tl, i+1)
  in
  loop (supl, 0)

refine def [a] leftmostPositionOfSublistAndFollowing
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

refine def [a] rightmostPositionOfSublistAndPreceding
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

refine def [a] findLeftmost (p: a -> Bool) (l: List a) : Option a =
  case l of
  | []     -> None
  | hd::tl -> if p hd then Some hd else findLeftmost p tl

refine def [a] findRightmost (p: a -> Bool) (l: List a) : Option a =
  let def loop (l: List a, result: Option a) : Option a =
      case l of
      | []     -> result
      | hd::tl -> if p hd then loop (tl, Some hd) else loop (tl, result)
  in
  loop (l, None)

refine def [a] delete (x:a) : List a -> List a = fn
  | []     -> Nil
  | hd::tl -> if x = hd then delete x tl else Cons (hd, delete x tl)

refine def [a] diff (l1: List a, l2: List a) : List a =
  if l2 = [] then l1
  else
  case l1 of
  | []     -> Nil
  | hd::tl -> if hd in? l2 then diff (tl, l2) else Cons (hd, diff (tl, l2))

refine def [a] longestCommonPrefix (l1: List a, l2: List a) : List a =
  case (l1,l2) of
  | (hd1::tl1, hd2::tl2) -> if hd1 = hd2
                            then Cons (hd1, longestCommonPrefix (tl1, tl2))
                            else Nil
  | _                    -> Nil

refine def permutation? (prm: List Nat) : Bool =
  noRepetitions? prm &&
  (let n = length prm in
  forall? (fn i:Nat -> i < n) prm)

refine def [a] permute (l: List a, prm: Permutation | l equiLong prm) : List a =
  let n = length l in
  list (fn(i:Nat) -> if i < n then l @@ (positionOf(prm,i)) else None)

refine def [a] permutationOf (l1: List a, l2: List a) : Bool =
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

endspec
