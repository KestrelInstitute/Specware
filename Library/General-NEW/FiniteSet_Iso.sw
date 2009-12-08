(* This file contains an isomorphic type refinement (isotyperef) of finite sets
(as defined in spec Set) as lists. This refinement is useful when targeting
functional languages with built-in lists, like Lisp. *)



(* We extend spec Set with the isomorphic representation, along with the
isomorphisms. *)

Step1 = SetList qualifying spec

import Set

(* We represent a finite set as an equivalence class of lists without repeated
elements, where we regard two lists as equivalent if they are the same up to
permutation. The following unqualified type FSet is isomorphic to type Set.FSet
from spec Set. Note that the qualifier SetList of this spec will qualify the
following type FSet in any spec that imports this spec. *)

type FSet a = (InjList a) / permutationOf

(* The isomorphic image of a set s is defined as the equivalence class ls of the
injective lists l whose conversion yields s (the quotient type notation is a bit
heavy).

Note that the following op is not and cannot be made executable because s is a
(boolean-valued) function and there is no way to execute a polymorphic iteration
through the elements for which the function returns true (even though the
subtype FSet guarantees that there is a finite number of such elements).
Therefore, in order to generate executable functional code, all occurrences (as
generated by the isotyperef) of the following op will have to be refined away
prior to code generation. *)

op isoFSet : [a] Bijection (Set.FSet a, FSet a) =
  fn s:Set.FSet a ->
    the(ls:FSet a) choose[FSet] (fn l:InjList a -> s = list2set l) ls

(* On the other hand, the inverse isomorphism can be easily defined to be
executable. Given an equivalence class of injective lists (which have the same
elements), we return the predicate that is true exactly for the elements of the
lists. *)

op osiFSet : [a] Bijection (FSet a, Set.FSet a) =
  fn ls:FSet a ->
    fn x:a -> choose[FSet] (fn l:InjList a -> x in? l) ls

(* Necessary relation between direct and inverse isomorphism. *)

theorem isomorphism is [a]
  (osiFSet: Bijection(FSet a, Set.FSet a)) = inverse isoFSet

endspec



(* We apply the isotyperef transformation to generate isomorphic counterparts of
all the types and ops that depend, directly or indirectly, on type Set.FSet. *)

Step2 = transform Step1 by
        {isomorphism ((isoFSet, osiFSet))}











%%%%%%%%%% IN PROGRESS %%%%%%%%%%

(*

(* Since type Set.FSet is defined as a subtype of type Set.Set, ops that
manipulate values of type Set.Set can be used to manipulate values of type
Set.FSet (subject to the subtype restrictions, of course). The isomorphic type
FSet is not a subtype of type Set.Set, and therefore those ops cannot be used
directly for values of type FSet. However, those ops can be used for the
isomorphic counterparts of such values (which have type Set.FSet).

For instance, while we cannot apply op Set.\/ to FSet values ls1 and ls2, we can
apply it to the Set.FSet values osiFSet(ls1) and osiFSet(ls2), obtaining a
Set.FSet result s that can be turned into the FSet value isoFSet(s). It is the
case that, by operating on the lists in the equivalence classes ls1 and ls2, we
can construct the equivalence class ls that corresponds to the union of ls1 and
ls2, which is a provable theorem. In fact, we can introduce an unqualified op \/
(which is qualified by the qualifier SetList in any spec that imports this spec)
that operates directly on type FSet, along with a theorem relating op \/ to op
Set.\/ and the isomorphisms. The theorem can be used to refine away the
isomorphisms in expressions generated by the isomorphic type refinement
transformation.

The following are ops, and associated theorems, that correspond to ops in spec
Set that manipulate values of type Set.Set and can also manipulate values of
type Set.FSet. The only ops in spec Set that do not have

 *)

op [a] in? (x:a, ls:FSet a) infixl 20 : Bool =
  choose[FSet] (fn l:InjList a ->
    x List.in? l
  ) ls

theorem in? is [a]
  fa (x:a, ls:FSet a)
    (x Set.in? (osiFSet ls)) = (x in? ls)

op [a] nin? (x:a, ls:FSet a) infixl 20 : Bool =
  choose[FSet] (fn l:InjList a ->
    x List.nin? l
  ) ls

theorem nin? is [a]
  fa (x:a, ls:FSet a)
    (x Set.nin? (osiFSet ls)) = (x nin? ls)

op [a] <= (ls1:FSet a, ls2:FSet a) infixl 20 : Bool =
  choose[FSet] (fn l1:InjList a ->
  choose[FSet] (fn l2:InjList a -> 
    List.forall? (fn x -> x in? l2) l1
  ) ls2
  ) ls1

theorem <= is [a]
  fa (ls1:FSet a, ls2:FSet a) 
    (osiFSet ls1 Set.<= osiFSet ls2) = (ls1 <= ls2)

op [a] < (ls1:FSet a, ls2:FSet a) infixl 20 : Bool =
  choose[FSet] (fn l1:InjList a ->
  choose[FSet] (fn l2:InjList a -> 
    List.forall? (fn x -> x in? l2) l1 && length l1 < length l2
  ) ls2
  ) ls1

theorem < is [a]
  fa (ls1:FSet a, ls2:FSet a) 
    (osiFSet ls1 Set.< osiFSet ls2) = (ls1 < ls2)

op [a] >= (ls1:FSet a, ls2:FSet a) infixl 20 : Bool =
  choose[FSet] (fn l1:InjList a ->
  choose[FSet] (fn l2:InjList a -> 
    List.forall? (fn x -> x in? l1) l2
  ) ls2
  ) ls1

theorem >= is [a]
  fa (ls1:FSet a, ls2:FSet a) 
    (osiFSet ls1 Set.>= osiFSet ls2) = (ls1 >= ls2)

op [a] > (ls1:FSet a, ls2:FSet a) infixl 20 : Bool =
  choose[FSet] (fn l1:InjList a ->
  choose[FSet] (fn l2:InjList a -> 
    List.forall? (fn x -> x in? l1) l2 && length l2 < length l1
  ) ls2
  ) ls1

theorem > is [a]
  fa (ls1:FSet a, ls2:FSet a) 
    (osiFSet ls1 Set.> osiFSet ls2) = (ls1 > ls2)

op [a] /\ (ls1:FSet a, ls2:FSet a) infixr 25 : FSet a =
  choose[FSet] (fn l1:InjList a ->
  choose[FSet] (fn l2:InjList a ->
  quotient[FSet]
    (List.filter (fn x -> x in? l2) l1)
  ) ls2
  ) ls1

theorem /\ is [a]
  fa (ls1:FSet a, ls2:FSet a) 
    isoFSet ((osiFSet ls1) Set./\ (osiFSet ls2)) = ls1 /\ ls2

op [a] \/ (ls1:FSet a, ls2:FSet a) infixr 24 : FSet a =
  choose[FSet] (fn l1:InjList a ->
  choose[FSet] (fn l2:InjList a ->
  quotient[FSet]
    (l1 ++ diff (l1, l2))
  ) ls2
  ) ls1

theorem \/ is [a]
  fa (ls1:FSet a, ls2:FSet a) 
    isoFSet ((osiFSet ls1) Set.\/ (osiFSet ls2)) = ls1 \/ ls2

op [a] -- (ls1:FSet a, ls2:FSet a) infixl 25 : FSet a =
  choose[FSet] (fn l1:InjList a ->
  choose[FSet] (fn l2:InjList a ->
  quotient[FSet]
   (diff (l1, l2))
  ) ls2
  ) ls1

theorem --_FSet is [a]
  fa (ls1:FSet a, ls2:FSet a) 
    isoFSet ((osiFSet ls1) Set.-- (osiFSet ls2)) = ls1 -- ls2

op [a,b] * (ls1:FSet a, ls2:FSet b) infixl 27 : FSet (a * b) =
  choose[FSet] (fn l1:InjList a ->
  choose[FSet] (fn l2:InjList b ->
  quotient[FSet]
    (flatten (List.map (fn x:a -> List.map (fn y:b -> (x,y)) l2) l1))
  ) ls2
  ) ls1

theorem * is [a,b]
  fa (ls1:FSet a, ls2:FSet b) 
    isoFSet ((osiFSet ls1) Set.* (osiFSet ls2)) = ls1 * ls2

op empty : [a] FSet a = quotient[FSet] []

theorem empty is [a]
  isoFSet Set.empty = (empty:FSet a)

op [a] empty? (ls:FSet a) : Bool =
  choose[FSet] (fn l:InjList a ->
    empty? l
  ) ls

theorem empty? is [a]
  fa (ls:FSet a)
    Set.empty? (osiFSet ls) = empty? ls

op [a] nonEmpty? (ls: FSet a) : Bool =
  choose[FSet] (fn l:InjList a ->
    nonEmpty? l
  ) ls



*)

(*

//\\

\\//

op [a] power (ls:FSet a) : FSet (FSet a) =
  choose[FSet] (fn l:InjList a ->
  quotient[FSet] 
    (case l of
    | [] -> [quotient[FSet] []]
    | hd::tl -> 

    if empty? l then single empty
    else let tailSets = power (quotient[FSet] (tail l)) in
         tailSets \/ map (fn subset -> subset <| (head l)) tailSets

  ) ls

type NonEmptyFSet a = (FSet a | nonEmpty?)

op [a] single (x:a) : FSet a = quotient[FSet] (single x)

op [a] single? (s: FSet a) : Bool =
choose[FSet] (fn l -> ofLength? 1 l) s

op [a] onlyMemberOf (x:a, s: FSet a) infixl 20 : Bool = (s = single x)

type SingletonFSet a = (FSet a | single?)

op [a] theMember (s: SingletonFSet a) : a =
  choose[FSet] (fn l -> head l) s

op [a] <| (s: FSet a, x:a) infixl 25 : FSet a =
  choose[FSet] (fn l ->
  quotient[FSet] (if x in? l then l else l <| x)
  ) s

op [a] - (s: FSet a, x:a) infixl 25 : FSet a =
  choose[FSet] (fn l -> 
  quotient[FSet] (filter (fn y -> y ~= x) l)
  ) s

op [a,b] map (f: a -> b) (s: FSet a) : FSet b =
  choose[FSet] (fn l -> 
  (quotient[FSet] (map f l))
  ) s

op [a,b] mapPartial (f: a -> Option b) (s: FSet a) : FSet b =
  choose[FSet] (fn l -> 
  quotient[FSet] (mapPartial f l)
  ) s

op [a] size (s: FSet a) : Nat = choose[FSet] length s

op [a,b] foldable? (c:b, f: b * a -> b, s: FSet a) : Bool =
  foldable? (c, f, fromFSet s)  % not executable

op [a,b] fold (c: b, f: b * a -> b, s: FSet a | foldable?(c,f,s)): b =
  choose[FSet] (foldl f c) s

op [a] //\\ (ss: NonEmptyFSet (FSet a)) : FSet a =
  choose[FSet] (fn ls -> 
  foldl (/\) (head ls) (tail ls)
  ) ss

op [a] \\// (ss: FSet (FSet a)) : FSet a =
  choose[FSet] (fn ls -> 
  foldl (\/) empty ls
  ) ss

op powerf : [a] FSet a -> FSet (FSet a) = power

op [a] forall? (p: a -> Bool) (s: FSet a) : Bool =
  choose[FSet] (forall? p) s

op [a] exists? (p: a -> Bool) (s: FSet a) : Bool =
  choose[FSet] (exists? p) s

op [a] exists1? (p: a -> Bool) (s: FSet a) : Bool =
  choose[FSet] (exists? p) s

op [a] filter (p: a -> Bool) (s: FSet a) : FSet a =
  choose[FSet] (fn l -> 
  quotient[FSet] (filter p l)
  ) s

 op [a] List.toSet (l: List a) : FSet a =  foldl (<|) empty l

 op [a] List.//\\ (ls: List1 (FSet a)) : FSet a = foldl (/\) (head ls) (tail ls)

 op [a] List.\\// (ls: List (FSet a)) : FSet a = foldl (\/) empty ls

endspec
*)
