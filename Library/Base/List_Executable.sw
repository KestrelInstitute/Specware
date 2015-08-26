List qualifying spec
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

proof Isa -hook list__1_lemmas end-proof

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

refine def [a] @@ (l:List a, i:Nat) : Option a =
  case l of
  | []     -> None
  | hd::tl -> if i = 0 then Some hd else tl @@ (i-1)

refine def empty? : [a] List a -> Bool = fn
  | [] -> true
  | _  -> false

refine def nonEmpty? : [a] List a -> Bool = fn
  | [] -> false
  | _  -> true

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

%% This isn't tail-recursive, so making this a refine def of butLast
%% will prevent butLast from executing on long lists (stack overflow).
%% Sticking with the original definition of butLast, which calls
%% removeSuffix, allows it to execute on long lists.  We could just
%% delete butLast_alt, but it might be handy to have this
%% recharacterization of butLast when we do proofs:

op [a] butLast_alt (l: List1 a) : List a =
  case l of
  | [hd]   -> Nil
  | hd::tl -> Cons (hd, butLast_alt tl)

theorem butLast_alt_lemma is [a]
  fa(l: List1 a) butLast_alt l = butLast l

%% This seems to execute without causing a stack overflow, even on very long lists.
refine def [a] ++  (l1: List a, l2: List a) : List a =
  case l1 of
  | [] -> l2
  | hd::tl -> Cons (hd, tl ++ l2)

refine def [a] |> (x:a, l: List a) : List1 a =
  Cons (x, l)

%% This isn't tail-recursive, so making this a refine def of <| will
%% prevent <| from executing on long lists (stack overflow).  Sticking
%% with the original definition of <|, which calls ++, allows it to
%% execute on very long lists.  We could just delete <|_alt, but it
%% might be handy to have this recharacterization of <| when we do
%% proofs:

op [a] <|_alt (l: List a, x:a) infixl 25 : List1 a =
  case l of
  | []     -> [x]
  | hd::tl -> Cons (hd, tl <|_alt x)

theorem <|_alt_lemma is [a]
  fa(l: List a, x:a) l <|_alt x = l <| x

%%TODO Not tail recursive.
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
  | hd::tl -> (p hd && ~ (exists? p tl)) || (~ (p hd) && exists1? p tl)

refine def [a] foralli? (p: Nat * a -> Bool) (l: List a) : Bool =
  let def loop (l: List a, i:Nat) : Bool =
      case l of
      | []     -> true
      | hd::tl -> p (i, hd) && loop (tl, i+1)
  in
  loop (l, 0)

refine def [a] filter (p: a -> Bool) (l: List a): List a =
  reverse (foldl (fn (result, x) -> if p x then x::result else result) [] l)

%%TODO Not tail recursive.
refine def [a,b] zip (l1: List a, l2: List b | l1 equiLong l2) : List (a * b) =
  case (l1,l2) of
  | ([],       [])       -> Nil
  | (hd1::tl1, hd2::tl2) -> Cons ((hd1,hd2), zip (tl1,tl2))

%%TODO Not tail recursive.
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

%% Non-tail recursive version:
refine def [a] repeat (x:a) (n:Nat) : List a =
  if n = 0 then Nil else Cons (x, repeat x (n-1))

%% Tail-recursive version.  Uses a tail-recursive helper function
%% with an accumulator: I am making the helper a separate function
%% because I want to prove lemmas about it.

op [a] repeat_aux (x:a, n:Nat, acc: List a) : List a =
  if n = 0 then acc else repeat_aux(x, n - 1, x::acc)

theorem repeat_aux_lemma is [a]
  fa(x:a, n:Nat, acc: List a)
    repeat_aux(x, n, acc) = (repeat x n) ++ acc

refine def [a] repeat (x:a) (n:Nat) : List a =
  repeat_aux(x, n, [])

refine def allEqualElements? : [a] List a -> Bool = fn
  | []     -> true
  | hd::tl -> forall? (fn x:a -> x = hd) tl

refine def [a] extendLeft (l: List a, x:a, n:Nat | n >= length l) : List a =
  let len = length l in
  if n <= len then l else Cons (x, extendLeft (l, x, n-1))

refine def [a] unflattenL
       (l: List a, lens: List Nat | foldl (Nat.+) 0 lens = length l)
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

% ------------------------------------------------------------------------------
% refine def [a] sublistAt? (subl: List a, i:Nat, supl: List a | i <= length supl) : Bool =
%  prefixOf? (subl, removePrefix (supl, i))

theorem prefixOf?_pred is [a]
  fa (subl: List a, l: List a) 
     prefixOf? (subl,l) = (ex (post: List a) subl ++ post = l)

refine def [a] sublistAt? (subl: List a, i:Nat, supl: List a) : Bool =
  i <= length supl  && prefixOf? (subl, removePrefix (supl, i)) 

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

%%TODO Not tail recursive.
refine def [a] delete (x:a) : List a -> List a = fn
  | []     -> Nil
  | hd::tl -> if x = hd then delete x tl else Cons (hd, delete x tl)

%%TODO Not tail recursive.
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

%% delete exactly one (leftmost) occurrence of x in l,
%% return None if x does not occur in l:
op [a] deleteOne (x:a, l: List a) : Option (List a) =
  case l of
  | []     -> None
  | hd::tl -> if hd = x then
                 Some tl
              else (case deleteOne (x, tl) of
                    | Some l -> Some (Cons (hd, l))
                    | None   -> None)


%% TODO: Name should end in a question mark:

%% Could use the delete1 operator here, except that one doesn't return
%% an Option.  This one combines the presence check and the deletion
%% and so should be faster:

refine def [a] permutationOf (l1: List a, l2: List a) : Bool =
  case l1 of
  | []     -> empty? l2
  | x::l1' -> (case deleteOne (x, l2) of
              | Some l2' -> l1' permutationOf l2'
              | None     -> false)

refine def [a] permutesTo? (l1: List a, l2: List a) : Bool =
  case l1 of
  | []     -> empty? l2
  | x::l1' -> x in? l2 && permutesTo? (l1', delete1 (x, l2))


% ------------------------------------------------------------------------------
% -----------------  The proofs ------------------------------------------------
% ------------------------------------------------------------------------------




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

(**********************************************************************
* I need the following lemmas right here - not later 
**********************************************************************)

declare List__list__1__loop.simps [simp del]

lemma List__list__1__loop_steps_aux:
  "\<lbrakk>f definedOnInitialSegmentOfLength n; k \<le> n \<rbrakk> \<Longrightarrow> 
    List__list__1__loop (n - k, f) = List__list (\<lambda>i. f (i + n - k))"
  apply (frule_tac x=n in exI) 
  apply (induct k)
  apply (frule_tac j=n in definedOnInitialSegmentOfLengthNone, simp)
  apply (subst List__list.simps,
         simp add:  List__list__1__loop.simps
                    List__definedOnInitialSegmentOfLength_def)
  apply (subgoal_tac 
         "\<exists>x. (\<lambda>i. f (i + n - Suc k)) definedOnInitialSegmentOfLength x")
  apply (subst List__list.simps, simp (no_asm_simp) add: List__list__1__loop.simps)
  apply (simp split: option.split)
  apply (rule_tac t="Suc (n - Suc k)" and s= "n - k" in subst,
         arith, simp)
  apply (rule_tac x="Suc k" in exI,
         simp add: List__definedOnInitialSegmentOfLength_def)
done

lemma List__list__1__loop_steps:
  "\<lbrakk>f definedOnInitialSegmentOfLength n; k \<le> n \<rbrakk> \<Longrightarrow> 
    List__list__1__loop (k, f) = List__list (\<lambda>i. f (i + k))"
 apply (drule_tac k="n-k" in List__list__1__loop_steps_aux, simp_all)
 done

end-proof



% ------------------------------------------------------------------------------
proof Isa list__1_lemmas 

lemma List__list__1__loop_Suc:
"(\<exists>l. f definedOnInitialSegmentOfLength l) \<Longrightarrow>
 List__list__1__loop (Suc i, f) = List__list__1__loop (i, \<lambda>j. f (Suc j))"

 apply (clarify, 
        subgoal_tac "(\<lambda>j. f (Suc j))  definedOnInitialSegmentOfLength (l - 1)")
 defer
 apply (simp add: List__definedOnInitialSegmentOfLength_def)
 apply (case_tac "Suc i \<le> l")
 apply (simp add: List__list__1__loop_steps)
 apply (frule_tac x=l in exI, rotate_tac 1, frule_tac x="l - 1" in exI)
 apply (simp add: List__list__1__loop.simps not_le)
 apply (drule_tac n=l and j="Suc i" in definedOnInitialSegmentOfLengthNone,
        simp_all)
 done

(**************** OLD PROOF - keep for now ----------------

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

*****************************************************************************)

end-proof


% ------------------------------------------------------------------------------

(* The bijectivity obligation for op list as refined above follows from the
injectivity of op list as defined in spec List (which must be proved as part of
establishing the well-formedness of spec List) and from the correctness of the
refinement expressed by theorem List__list__r_def. The current
Specware-Isabelle translator does not make the proof of the bijectivity of op
list as defined in spec List available for this spec here, but future versions
of Specware will, and will probably also automatically discharge the
obligation. For now, we just ignore the obligation via "sorry". *)


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


proof isa list__1_Obligation_subtype
  apply (cut_tac List__list_subtype_constr)
  apply (auto simp  add: bij_on_def bij_ON_def inj_on_def surj_on_def)
  apply (drule_tac x=x in spec, auto, drule_tac x=y in spec,
         auto simp add:  List__list__1__loop_steps)
  apply (drule_tac x=y in spec, clarify, rule exI,
         auto simp add:  List__list__1__loop_steps)
end-proof

proof isa List__list__1__obligation_refine_def
  by (auto simp add: List__list__1_def List__list__1__loop_steps)
end-proof

proof isa List__list_1__1_Obligation_subtype0
  by (auto simp add: List__e_at_at_def list_1_Isa_nth 
                     List__definedOnInitialSegmentOfLength_def)
end-proof

proof isa List__list_1__1_Obligation_subtype
  by (simp only: List__e_at_at_def List__list_1_subtype_constr)
end-proof

proof isa List__list_1__1__obligation_refine_def
  by (simp add: List__e_at_at_def List__list_1__1_def)
end-proof

proof isa List__tabulate__1__obligation_refine_def
  apply (subgoal_tac "\<forall>i l x.
                              List__tabulate__1__loop (i, l, f) @ [x] =
                              List__tabulate__1__loop (i, l @ [x], f)")
  apply (simp add: List__tabulate__1_def)
  apply (induct n)
  apply (simp add: List__tabulate_nil)
  apply (simp add: List__tabulate_snoc)
  apply (rule allI, rule nat_induct, auto)
end-proof

proof Isa List__e_at__def1
 by (auto simp add: nth_Cons, case_tac i, auto)
end-proof


proof isa List__e_at__1__obligation_refine_def 
  apply (induct l arbitrary: i, simp)
  apply (case_tac i, simp_all)
end-proof


proof isa List__e_at_at__1__obligation_refine_def 
  apply (rule sym)
  apply (induct l arbitrary: i, simp add:  List__e_at_at_def list_1_Isa_nth)
  apply (case_tac i, auto simp add:  List__e_at_at_def list_1_Isa_nth)
end-proof

proof Isa List__empty_p__def1
  by (case_tac Wild__Var_0, auto)
end-proof

proof isa List__empty_p__1__obligation_refine_def 
  by (induct l, auto)
end-proof

proof Isa List__nonEmpty_p__def
  by (case_tac l, auto)
end-proof

proof isa List__nonEmpty_p__1__obligation_refine_def 
  by (induct l, auto)
end-proof

proof isa List__theElement__1__obligation_refine_def 
  by (frule List__theElement_Obligation_the,
      auto simp add: List__theElement_def)
end-proof

proof isa List__in_p__1__obligation_refine_def 
  by (induct l, auto)
end-proof

proof isa List__nin_p__1__obligation_refine_def 
  by (induct l, auto)
end-proof

proof isa List__subFromLong__1__obligation_refine_def 
   apply (simp add: List__subFromLong__1_def)
   apply (auto simp add: list_eq_iff_nth_eq List__length_subFromLong)
   apply (simp add: List__subFromLong_def, subst List__list_nth,
          simp_all add: List__definedOnInitialSegmentOfLength_def)
end-proof


proof isa List__prefix__1__obligation_refine_def 
  apply (simp add: List__prefix__1_def)
  apply (induct l arbitrary: n, simp)
  apply (rotate_tac -1, erule rev_mp, induct_tac n, auto)
  apply (thin_tac ?P)+
  apply (subgoal_tac "\<forall>l r. a # rev (List__prefix__1__loop (l, na, r)) =
                                rev (List__prefix__1__loop (l, na, r @ [a]))",
        simp)
  apply (induct_tac na, auto)
  apply (induct_tac la, auto)
end-proof


proof isa List__suffix__1__obligation_refine_def 
  apply (simp add: List__suffix_def List__suffix__1_def)
  apply (auto simp add: list_eq_iff_nth_eq List__length_subFromLong)
  apply (simp add: List__subFromLong_def, subst List__list_nth,
         simp_all add: List__definedOnInitialSegmentOfLength_def)
end-proof

proof isa List__removePrefix__1__obligation_refine_def 
  apply (induct l arbitrary: n, simp)
  apply (rotate_tac -1, erule rev_mp, induct_tac n, auto)
end-proof

proof isa List__head__1__obligation_refine_def 
 by (induct l, auto)
end-proof

proof isa List__last__1_Obligation_exhaustive 
  by (induct l, auto)
end-proof

proof isa List__last__1__obligation_refine_def 
  by (induct l, simp, case_tac l, auto)
end-proof

proof isa List__tail__1__obligation_refine_def 
  by (induct l, auto)
end-proof

proof isa butLast_alt_Obligation_exhaustive 
  by (induct l, auto)
end-proof

proof isa butLast_alt_lemma
  by (induct l, simp, case_tac l, auto)
end-proof

proof isa List__e_pls_pls__1__obligation_refine_def 
  by (induct l1, auto)
end-proof

proof isa List__e_bar_gt__1__obligation_refine_def 
  by (simp add: List__e_bar_gt__1_def)
end-proof

proof isa e_lt_bar_alt_lemma
  by (simp add: List__e_lt_bar_def, induct l, auto)
end-proof

proof isa List__update__1__obligation_refine_def 
  by (induct l arbitrary: i, simp, case_tac i, auto)
end-proof

proof isa List__forall_p__1__obligation_refine_def 
  by (induct l, auto)
end-proof

proof isa List__exists_p__1__obligation_refine_def
  by (induct l, auto)
end-proof

proof isa List__exists1_p__1__obligation_refine_def
  apply (induct l, clarsimp simp add: List__exists1_p_def)
  apply (drule sym, simp, thin_tac ?P, rule iffI)
  apply (simp add: List__exists1_p_def List__exists_p__def Ex1_def,
         erule exE, case_tac x)
  apply (clarsimp, drule_tac x="Suc i" in spec, clarsimp)
  apply (rule disjI2, clarsimp, 
         frule_tac x=0 in spec, clarsimp,
         rule_tac x=nat in exI, clarsimp,
         drule_tac x="Suc y" in spec, clarsimp)
  (* Simp/Auto tries too much, go back to safe mode for now *)
  apply (simp add: List__exists1_p_def List__exists_p__def Ex1_def, safe)
  apply (rule_tac x=0 in exI, clarsimp, case_tac y, simp_all)
  apply (rule_tac x="Suc x" in exI, safe)
  apply (metis nth_Cons_Suc)   
  apply (case_tac y, metis nth_Cons_0, simp) 
end-proof

proof isa List__foralli_p__1__obligation_refine_def 
  apply (subgoal_tac "\<forall>p. List__foralli_p p l = List__foralli_p__1 p l",
         simp)
  apply (simp add: List__foralli_p__1_def List__foralli_p_def)
  apply (induct l, clarsimp, clarify)
  apply (rule_tac t="\<forall>i<length (a # l). p (i, (a # l) ! i)" 
              and s="p(0,a) \<and> (\<forall>i<length l. p (i+1, l ! i))"
         in subst)
  apply (rule iffI, clarsimp, case_tac i, simp_all)
  apply (frule_tac x=0 in spec, clarsimp, drule_tac x="Suc i" in spec, simp)
  apply (subgoal_tac "\<forall>i. List__foralli_p__1__loop (l, i+1, p)
                        = List__foralli_p__1__loop (l, i,  \<lambda>(j,a). p (j+1,a))")
  apply (drule_tac x= "\<lambda>(j,x). p (j+1,x)" in spec, simp)
  apply (rule list.induct, simp, clarsimp)
end-proof

proof isa List__filter__1__obligation_refine_def 
  apply (simp add: List__filter__1_def rev_swap [symmetric])
  apply (induct l, auto, thin_tac ?P)
  apply (subgoal_tac "\<forall>s. foldl (\<lambda>b a. if p a then a # b else b) s l @ [a] =
                          foldl (\<lambda>b a. if p a then a # b else b) (s @ [a]) l",
        simp)
  apply (induct_tac l, auto)
end-proof

proof isa List__zip__1_Obligation_exhaustive 
  by (induct l1, auto, induct l2, auto)
end-proof

proof isa List__zip__1__obligation_refine_def
  by (induct l1 arbitrary: l2, auto, case_tac l2, simp_all)
end-proof

proof isa List__zip3__1_Obligation_exhaustive 
  by (induct l1, auto, case_tac l2, simp_all, case_tac l3, simp_all)
end-proof

proof isa List__zip3__1__obligation_refine_def 
  by (induct l1 arbitrary: l2 l3, auto simp add: List__zip3_alt,
      case_tac l2, simp_all, case_tac l3, simp_all)
end-proof

proof isa List__unzip__1_Obligation_subtype
  by (induct tl__v arbitrary: tl1 tl2, auto, 
      case_tac "List__unzip__1 tl__v", auto)
end-proof

proof isa List__unzip__1__obligation_refine_def 
  by (induct x0, auto, case_tac "List__unzip__1 x0", auto)
end-proof

proof isa List__unzip3__1_Obligation_subtype 
  by (induct tl__v arbitrary: tl1 tl2 tl3, simp_all,
      case_tac "List__unzip3__1 tl__v", auto)
end-proof

proof isa List__unzip3__1__obligation_refine_def 
    apply (case_tac "List__unzip3__1 x0", simp,
         frule List__unzip3__1_Obligation_subtype, clarsimp)
  apply (simp only:  List__unzip3_def)
  apply (rule sym, rule  Function__fxy_implies_inverse__stp2)
  apply (rule List__unzip3_Obligation_subtype, simp_all add: List__zip3_alt)
  apply (induct x0, auto)
  apply (case_tac "List__unzip3__1 x0", clarsimp)
end-proof

proof isa List__map__1__obligation_refine_def
  (* I had a similar proof before - need lemmas about foldl *)
  apply (simp add: List__map__1_def rev_swap [symmetric])
  apply (induct l, auto, thin_tac ?P)
  apply (subgoal_tac "\<forall>s. foldl (\<lambda>b a. f a # b) s l @ [f a] =
                          foldl (\<lambda>b a. f a # b) (s @ [f a]) l",
        simp)
  apply (induct_tac l, auto)
end-proof

proof isa List__map2__1_Obligation_exhaustive 
  by (induct l1, auto, induct l2, auto)
end-proof

proof isa List__map2__1__obligation_refine_def 
  by (simp add: List__map2_def,
      induct l1 arbitrary: l2, auto, case_tac l2, simp_all)
end-proof

proof isa List__map3__1_Obligation_exhaustive 
  by (induct l1, auto, case_tac l2, simp_all, case_tac l3, simp_all)
end-proof


proof isa List__map3__1__obligation_refine_def 
  by (simp add: List__map3_def List__zip3_alt,
      induct l1 arbitrary: l2 l3, auto,
      case_tac l2, simp_all, case_tac l3, simp_all)
end-proof

proof isa List__removeNones__1_Obligation_exhaustive 
  by (case_tac xx, auto)
end-proof

proof isa List__removeNones__1__obligation_refine_def 
  apply (simp add:  List__removeNones_def, 
         rule the1I2, rule List__removeNones_Obligation_the)
  apply (induct l, auto, case_tac a, auto)
end-proof

proof isa List__matchingOptionLists_p__1__obligation_refine_def 
  apply (subgoal_tac "\<forall>s. List__matchingOptionLists_p(l1, s) 
                        = List__matchingOptionLists_p__1(l1, s)",
         drule spec, simp)
  apply (induct l1, simp_all add: List__matchingOptionLists_p_def)
  apply (clarify, case_tac s, simp_all)
  apply (clarify, case_tac s, simp, clarsimp)
  apply (drule_tac x="list" in spec, drule sym)
  apply (case_tac a, simp_all, case_tac aa)
  (* case 1a: None / None *)
  apply (clarsimp, thin_tac ?P, rule iffI)
  apply (clarsimp, drule_tac x="Suc i" in spec, clarsimp)
  apply (clarsimp, case_tac i, clarsimp, clarsimp)
  (* case 1b: None / Some *)
  apply (clarsimp, rule_tac x=0 in exI, simp)
  (* case 2a: Some / None *)
  apply (case_tac aa)
  apply (clarsimp, rule_tac x=0 in exI, simp)
  (* case 2b: Some / Some *)
  apply (clarsimp, thin_tac ?P, rule iffI)
  apply (clarsimp, drule_tac x="Suc i" in spec, clarsimp)
  apply (clarsimp, case_tac i, clarsimp, clarsimp)
end-proof

proof isa List__mapPartial__1__obligation_refine_def 
  by (induct l, auto, case_tac "f a", auto)
end-proof

proof isa List__mapPartial2__1_Obligation_exhaustive 
  by (induct l1, auto, induct l2, auto)
end-proof


proof isa List__mapPartial2__1__obligation_refine_def 
  by (simp add: List__mapPartial2_def,
      induct l1 arbitrary: l2, auto, case_tac l2, simp_all,
      case_tac "f (a, aa)", simp_all)
end-proof

proof isa List__mapPartial3__1_Obligation_exhaustive
  by (induct l1, auto, case_tac l2, simp_all, case_tac l3, simp_all)
end-proof


proof isa List__mapPartial3__1__obligation_refine_def 
  by (simp add: List__mapPartial3_def List__zip3_alt,
      induct l1 arbitrary: l2 l3, auto,
      case_tac l2, simp_all, case_tac l3, simp_all,
      case_tac "f (a, aa, ab)", simp_all)
end-proof

proof isa List__reverse__1__obligation_refine_def 
  apply (simp add: List__reverse__1_def, induct l, auto)
  apply (subgoal_tac "\<forall>s. List__reverse__1__loop (l, s) @ [a] 
                        = List__reverse__1__loop (l, s @ [a])", simp)
  apply (induct_tac l, auto)  
end-proof

proof isa List__repeat__1__obligation_refine_def
  by (induct n, auto)
end-proof

proof Isa List__repeat_aux_lemma
  apply(induct n arbitrary: acc__v)
  apply(simp)
  by (metis append_Cons List__repeat_aux.simps(2) replicate_Suc replicate_app_Cons_same)
end-proof

proof isa List__repeat__2__obligation_refine_def
  apply(simp add: List__repeat__2_def List__repeat_aux.simps List__repeat_aux_lemma)
end-proof

proof isa List__allEqualElements_p__1__obligation_refine_def 
  apply (induct l, simp_all add: list_all_length List__allEqualElements_p_def)
  apply (thin_tac ?P, auto simp add: list_eq_iff_nth_eq)
end-proof


proof isa List__extendLeft__1__obligation_refine_def 
  apply (subgoal_tac "\<forall>k. List__extendLeft(l, x, length l + k)
                        = List__extendLeft__1(l, x, length l +  k)",
         drule_tac x="n - length l" in spec, simp)
  apply (clarsimp simp only: List__extendLeft_def, induct_tac k, auto)
end-proof

proof isa List__unflattenL__1_Obligation_subtype1
  apply (simp, drule sym, simp, thin_tac ?P)
  apply (subgoal_tac "\<forall>k. foldl op + k lens0
                         = foldl op + (len + k) lens0 - len",
         drule_tac x=0 in spec, simp)
  apply (induct lens0, simp, clarify)
  apply (drule_tac x="k+a" in spec, simp add: algebra_simps)
  done
end-proof

proof isa List__unflattenL__1_Obligation_subtype0 
  apply (simp, drule sym, simp, thin_tac ?P)
  apply (subgoal_tac "\<forall>k. len \<le> foldl op + (len + k) lens0", 
         drule_tac x=0 in spec, simp)
  apply (induct lens0, auto)
  apply (drule_tac x="k+a" in spec, simp add: algebra_simps)
end-proof

proof isa List__unflattenL__1_Obligation_subtype 
  by (erule List__unflattenL__1_Obligation_subtype0)
end-proof


proof isa List__unflattenL__1__obligation_refine_def 
  apply (cut_tac l=l in List__unflattenL_Obligation_the, simp,
         simp add:  List__unflattenL_def, rule the1I2, simp)
  apply (thin_tac "\<exists>!l. ?P l", clarsimp)
  apply (induct lens arbitrary: x l, simp_all, case_tac x, simp_all)
  apply (frule_tac x=0 in spec, simp)  
  apply (subgoal_tac "\<forall>k. foldl op + (a + k) lens
                        = foldl op + k lens + a",
         rotate_tac -1, drule_tac x=0 in spec, simp)
  apply (subgoal_tac "\<forall>i<length lens. length (list ! i) = lens ! i",
         simp)
  apply (rule allI, drule_tac x="Suc i" in spec, simp)
  apply (thin_tac ?P)+ 
  apply (induct_tac lens, simp, clarify,
         drule_tac x="k+ab" in spec, simp add: algebra_simps)
end-proof

proof isa List__unflatten__1_Obligation_subtype1 
  by (simp add: zdvd_int [symmetric])
end-proof

proof isa List__unflatten__1_Obligation_subtype0 
  by (simp add: zdvd_int [symmetric] dvd_imp_le  List__empty_p_length)
end-proof

proof isa List__unflatten__1_Obligation_subtype 
  by (erule List__unflatten__1_Obligation_subtype0)
end-proof

proof Isa List__unflatten__1 ()
  by auto
termination
  apply (relation "measure (\<lambda>(l, n). length l)", auto)
  apply (rule diff_less, auto)
  (** TRANSLATION ISSUE: Information n>0 got lost in translation **)  
sorry
end-proof


proof isa List__unflatten__1__obligation_refine_def
  apply (simp add: zdvd_int [symmetric] del: List__unflatten__1.simps)
  apply (rule sym, induct l rule: length_induct)
  apply (case_tac "null xs")
  apply (drule_tac List__unflatten_length, simp, simp add: List__empty_p_length)
  apply (subst  List__unflatten__1.simps,
         drule_tac x="drop n xs" in spec,
         simp add: null_def del: List__unflatten__1.simps)
  apply (drule_tac l="drop n xs" and x="take n xs" in List__unflatten_cons)
  apply (simp_all, drule dvd_imp_le, simp_all)
end-proof

proof isa List__noRepetitions_p__1__obligation_refine_def 
  by (induct l, auto)
end-proof

proof isa List__increasingNats_p__1_Obligation_exhaustive
  by (cases xx, simp, case_tac "list", simp_all)
end-proof

proof isa List__increasingNats_p__1__obligation_refine_def 
  apply (case_tac nats, simp, clarsimp)
  apply (subgoal_tac "\<forall>a. List__increasingNats_p (a # list)
                        = List__increasingNats_p__1 (a # list)", simp)
  apply (induct_tac list, simp, clarsimp)
  apply (drule_tac x=aa in spec, auto)
end-proof

proof Isa positionsSuchThat__1__loop_Obligation_subtype
  sorry
end-proof

proof isa List__positionsSuchThat__1__obligation_refine_def 
  apply (simp add: List__positionsSuchThat__1_def)
  apply (induct l, simp)
  apply (subgoal_tac "\<forall>k. map Suc (List__positionsSuchThat__1__loop (l, k, p)) =
                          List__positionsSuchThat__1__loop (l, Suc k, p)", simp)
  apply (induct_tac l, simp, clarsimp)
end-proof

proof isa List__leftmostPositionSuchThat__1__obligation_refine_def 
  apply (simp add: List__leftmostPositionSuchThat_def 
                   List__leftmostPositionSuchThat__1_def)
  apply (induct l, auto simp add: Let_def null_def hd_map)
  apply (subgoal_tac 
         "\<forall>k. (None = List__leftmostPositionSuchThat__1__loop (l, k, p))
            = (None = List__leftmostPositionSuchThat__1__loop (l, Suc k, p))",
        simp)
  apply (induct_tac l, simp, clarsimp)
  apply (subgoal_tac 
         "\<forall>k i. (Some i
                    = List__leftmostPositionSuchThat__1__loop (l, k, p))
              = (Some (Suc i)
                    = List__leftmostPositionSuchThat__1__loop (l, Suc k, p))",
        simp)
  apply (induct_tac l, simp, clarsimp)
end-proof

proof isa List__rightmostPositionSuchThat__1__obligation_refine_def 
sorry
end-proof

proof isa List__positionOf__1__obligation_refine_def 
  apply (frule  List__positionOf_Obligation_subtype)
  apply (simp_all add: List__positionsOf_subtype_constr length_1_hd_conv 
                  del: One_nat_def)
  apply (simp add: List__positionOf__1_def List__positionOf_def 
                   List__leftmostPositionSuchThat_def null_def
                   List__positionsOf_def)
  apply (erule ssubst, simp add: Let_def)
end-proof

proof isa List__prefixOf_p_pred
  by (induct subl arbitrary: l, auto, case_tac l, auto)
end-proof

proof isa List__sublistAt_p__1__obligation_refine_def 
  apply (auto simp add: List__sublistAt_p__1_def List__prefixOf_p_pred
       List__sublistAt_p_def)
  apply (rule_tac x="take i supl" in exI, auto,
         rule_tac x=post in exI, simp)
end-proof

proof Isa positionsOfSublist__1__loop_Obligation_subtype1
  sorry
end-proof

proof isa List__positionsOfSublist__1__obligation_refine_def 
sorry
end-proof

proof isa List__leftmostPositionOfSublistAndFollowing__1__loop_Obligation_subtype 
  by (induct subl, auto simp add: List__prefixOf_p_pred)  
end-proof

proof isa List__leftmostPositionOfSublistAndFollowing__1__obligation_refine_def 
sorry
end-proof

proof isa List__rightmostPositionOfSublistAndPreceding__1_Obligation_subtype
 apply (induct supl, simp_all split: split_if_asm)
 (** need a technique for induction on two arguments ***) 
sorry
end-proof

proof isa List__rightmostPositionOfSublistAndPreceding__1__obligation_refine_def 
sorry
end-proof

proof isa List__findLeftmost__1__obligation_refine_def 
  by (induct l, simp_all  add: List__findLeftmost_def)
end-proof

proof isa List__findRightmost__1__obligation_refine_def 
  apply (induct l, auto simp add: List__findRightmost_def 
                                  List__findRightmost__1_def null_def )
  apply (rotate_tac -2, erule rev_mp, induct_tac l, auto)+
end-proof

proof isa List__delete__1__obligation_refine_def 
  by (induct l, auto simp add: List__delete_def)
end-proof

proof isa List__diff__1__obligation_refine_def 
  by (simp add: List__diff_def, case_tac "l2=[]", auto,
      induct l1, auto)
end-proof

proof isa List__longestCommonPrefix__1__obligation_refine_def 
  apply (simp add: List__longestCommonPrefix_def)
  apply (rule the1I2, rule List__longestCommonPrefix_Obligation_the)
  apply (clarsimp, induct l2 arbitrary: l1 x, induct_tac l1, simp_all)
  apply (case_tac x, simp_all)
  apply (erule disjE, simp_all, case_tac l1, simp_all)+
end-proof

proof isa List__permutation_p__1__obligation_refine_def 
  by (simp add: List__permutation_p_def List__permutation_p__1_def 
                list_all_iff Ball_def)
end-proof

proof isa List__permute__1_Obligation_subtype1 
  by (simp add:  List__permutation_mem)
end-proof

proof isa List__permute__1_Obligation_subtype0
  by (simp add: List__permutation_p_def)
end-proof

proof isa List__permute__1_Obligation_subtype2
  by (simp add: List__permutation_p_def)

(*** and an explicit version of  List__permute__1_Obligation_subtype ***)
lemma List__permute__1_Obligation_subtype_explicit: 
  "\<lbrakk>List__permutation_p prm; l equiLong prm\<rbrakk>
   \<Longrightarrow> 
    (\<lambda> (i::nat). if i < length l then l @@ List__positionOf(prm, i) else None) 
       definedOnInitialSegmentOfLength (length l)"
  apply (auto simp add: List__definedOnInitialSegmentOfLength_def)
  by (metis (mono_tags, hide_lams) List__e_at_at_def List__equiLong_def List__permutation_mem
            List__permutation_p_def List__positionOf_length2 list_1_Isa_nth)
end-proof

proof isa List__permute__1_Obligation_subtype 
  by (rule_tac x="length l" in exI, 
      erule List__permute__1_Obligation_subtype_explicit, simp)
end-proof

proof isa List__permute__1__obligation_refine_def
  apply (simp add: List__permute_def, rule the1I2,
         drule_tac l=l in List__permute_Obligation_the, auto)
  apply (frule_tac l=l in List__permute__1_Obligation_subtype_explicit, simp)
  apply (clarsimp simp add: List__permute__1_def list_eq_iff_nth_eq 
                            List__length_is_SegmentLength,
         subst List__list_nth, simp_all)
  apply (frule List__permute__1_Obligation_subtype1, simp_all,
         drule List__permutation_distinct, 
         frule List__positionOf_exists2, auto,
         simp add: List__e_at_at_def list_1_Isa_nth 
                   List__positionOf_length2 List__positionOf_val2)
end-proof

proof Isa List__deleteOne ()
by (pat_completeness, auto)
termination 
by (lexicographic_order)

(******************************************************************
* The above proof is trivial and could have been found by Isabelle
* I need this proof object only to be able to insert the following 
* lemmas before the main obligation about List__permutationOf
*******************************************************************)

lemma List__deleteOne_refine1:
  "x \<in> set l \<Longrightarrow> List__deleteOne (x, l) = Some (remove1 x l)"
  by (induct l, auto)

lemma List__deleteOne_refine2:
  "x \<notin> set l \<Longrightarrow> List__deleteOne (x, l) = None"
  by (induct l, auto)
(****************************************************************************
* The main proof also depends on the following lemma which is known to be
* true but quite difficult to prove formally. Once that proof is finished
* the lemma should be moved into the more fiundamental List.sw 
****************************************************************************)

lemma List__permutationOf_cons:
   "a # l1 permutationOf l2 = (a mem l2 \<and> l1 permutationOf (remove1 a l2))"
  apply (auto simp add: List__permutationOf_def)
  (** Induction step \<longrightarrow> a mem l2 **)
  apply (simp (no_asm_simp) add: List__permute_def)
  apply (rule the1I2)
  apply (cut_tac l="a#l1" and prm=prm in List__permute_Obligation_the, simp_all)
  apply (clarify, drule_tac x=0 in spec, simp, rule nth_mem) 
  apply (frule_tac List__permutation_bounded2)
  apply (drule_tac x=0 in bspec, simp_all)
  apply (rule_tac l=prm in List__permutation_mem, simp_all)
  (** Induction step \<longrightarrow> l1 permutationOf (remove1 a l2)) **)
  (** need to remove location of a from prm **)
  (** Induction step \<longleftarrow> a # l1 permutationOf l2 **)
  (** need to insert location of a into prm ***)
sorry

end-proof

proof isa List__permutationOf__1__obligation_refine_def 
  apply (subgoal_tac "\<forall>l2. l1 permutationOf l2 = l1 permutationOf__1 l2", simp)
  apply (induct l1)
  apply (clarsimp simp add: List__permutationOf_nil null_def)
  apply (clarsimp simp add: List__permutationOf_cons split: option.split)
  apply (thin_tac ?P, rule conjI)
  apply (clarsimp simp add: List__deleteOne_refine1)
  apply (clarsimp, case_tac "a \<in> set l2")
  apply (simp add: List__deleteOne_refine1)
  apply (simp add: List__deleteOne_refine2)
end-proof

proof Isa List__permutesTo_p__1__obligation_refine_def
  apply (induct l1 arbitrary: l2)
  apply (simp_all add: List__permutesTo_p_def null_def)
  proof -
    fix a l1 l2
    assume asmp:"\<And> l2 . ((l1 <~~> l2) = List__permutesTo_p__1 (l1, l2))"
    show "(a # l1 <~~> l2) = (a \<in> set l2 \<and> List__permutesTo_p__1 (l1, remove1 a l2))"
      apply (rule subst[OF asmp[of "remove1 a l2"]])
      apply auto
      apply (simp add: subst[OF perm_set_eq[of "a#l1"]])
      apply (rule subst[of _ l1, OF remove_hd[of a]])
      apply (rule perm_remove_perm)
      apply simp
      apply (simp_all add: trans[OF _ perm_sym[OF perm_remove], of _ a])
    done
  qed
end-proof

end-spec
