(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

FSet qualifying spec

  import Set

  % sets as equivalence classes of lists without repeated elements:
  type FSet a = (InjList a) / permutationOf

  op toFSet : [a] Bijection (FiniteSet a, FSet a) =  % not executable
    fn fs -> the(s) 
      choose[FSet] (fn l -> 
      fs = (fn x -> x in? l)
      ) s

  op [a] fromFSet (s: FSet a) : FiniteSet a =
    fn x -> choose[FSet] (fn l -> x in? l) s

  op [a] in? (x:a, s: FSet a) infixl 20 : Bool =
    choose[FSet] (fn l -> x in? l) s

  op [a] nin? (x:a, s: FSet a) infixl 20 : Bool = ~ (x in? s)

  op [a] <= (s1: FSet a, s2: FSet a) infixl 20 : Bool =
    choose[FSet] (fn l1 ->
    choose[FSet] (fn l2 -> 
    forall? (fn x -> x in? l2) l1
    ) s2
    ) s1

  op [a] < (s1: FSet a, s2: FSet a) infixl 20 : Bool = (s1 <= s2 && s1 ~= s2)

  op [a] >= (s1: FSet a, s2: FSet a) infixl 20 : Bool = (s2 <= s1)

  op [a] > (s1: FSet a, s2: FSet a) infixl 20 : Bool = (s2 < s1)

  op [a] /\ (s1: FSet a, s2: FSet a) infixr 25 : FSet a =
    choose[FSet] (fn l1 ->
    choose[FSet] (fn l2 ->
    quotient[FSet] (filter (fn x -> x in? l2) l1)
    ) s2
    ) s1

  op [a] \/ (s1: FSet a, s2: FSet a) infixr 24 : FSet a =
    choose[FSet] (fn l1 ->
    choose[FSet] (fn l2 ->
    quotient[FSet] (l1 ++ filter (fn x -> x nin? l1) l2)
    ) s2
    ) s1

  op [a] -- (s1: FSet a, s2: FSet a) infixl 25 : FSet a =
    choose[FSet] (fn l1 ->
    choose[FSet] (fn l2 ->
    quotient[FSet] (filter (fn x -> x nin? l2) l1)
    ) s2
    ) s1

  op empty : [a] FSet a = quotient[FSet] empty

  op [a] empty? (s: FSet a) : Bool = (s = empty)

  op nonEmpty? : [a] FSet a -> Bool = ~~ empty?

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
    quotient[FSet] (if x in? l then l else x :: l)
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

  op [a,b] * (s1: FSet a, s2: FSet b) infixl 27 : FSet (a * b) =
    \\// (map (fn x -> map (fn y -> (x,y)) s2) s1)

  op [a] power (s: FSet a) : FSet (FSet a) =
    choose[FSet] (fn l ->
    if empty? l then single empty
    else let tailSets = power (quotient[FSet] (tail l)) in
         tailSets \/ map (fn subset -> subset <| (head l)) tailSets
    ) s

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


proof isa List__permutationOf_transitive
sorry
end-proof

proof isa List__permutationOf_symmetric
sorry
end-proof

proof isa List__permutationOf_reflexive
sorry
end-proof

proof isa FSet__toFSet_Obligation_subtype
sorry
end-proof

proof isa FSet__toFSet_Obligation_the
sorry
end-proof

proof isa FSet__toFSet_Obligation_subtype0
sorry
end-proof

proof isa FSet__fromFSet_Obligation_subtype
sorry
end-proof

proof isa FSet__fromFSet_Obligation_subtype0
sorry
end-proof

proof isa FSet__in_p_Obligation_subtype
  by (simp add: FSet__fromFSet_Obligation_subtype)
end-proof

proof isa FSet__e_lt_eq_Obligation_subtype
sorry
end-proof

proof isa FSet__e_lt_eq_Obligation_subtype0
 by (auto simp add: list_all_iff FSet__fromFSet_Obligation_subtype)
end-proof

proof isa FSet__e_fsl_bsl_Obligation_subtype
sorry
end-proof

proof isa FSet__e_fsl_bsl_Obligation_subtype0
sorry
end-proof

proof isa FSet__e_fsl_bsl_Obligation_subtype1
by auto
end-proof

proof isa FSet__e_bsl_fsl_Obligation_subtype
sorry
end-proof

proof isa FSet__e_bsl_fsl_Obligation_subtype0
sorry
end-proof

proof isa FSet__e_bsl_fsl_Obligation_subtype1
by auto
end-proof

proof isa FSet__e_dsh_dsh_Obligation_subtype
sorry
end-proof

proof isa FSet__e_dsh_dsh_Obligation_subtype0
sorry
end-proof

proof isa FSet__e_dsh_dsh_Obligation_subtype1
  by auto
end-proof

proof isa FSet__single_Obligation_subtype
  by auto
end-proof

proof isa FSet__single_p_Obligation_subtype
  sorry
end-proof

proof isa FSet__theMember_Obligation_subtype
sorry
end-proof

proof isa FSet__theMember_Obligation_subtype0
sorry
end-proof

proof isa FSet__e_lt_bar_Obligation_subtype
sorry
end-proof

proof isa FSet__e_dsh_Obligation_subtype
 sorry
end-proof

proof isa FSet__e_dsh_Obligation_subtype0
(** thm is not correct **)
sorry
end-proof

proof isa FSet__map_Obligation_subtype
sorry
end-proof

proof isa FSet__map_Obligation_subtype0
sorry
end-proof

proof isa FSet__mapPartial_Obligation_subtype
sorry
end-proof

proof isa FSet__mapPartial_Obligation_subtype0
(** thm is not correct **)
sorry
end-proof

proof isa FSet__size_Obligation_subtype
sorry
end-proof

proof isa FSet__fold_Obligation_subtype
sorry
end-proof

proof isa FSet__e_fsl_fsl_bsl_bsl_Obligation_subtype
sorry
end-proof

proof isa FSet__e_fsl_fsl_bsl_bsl_Obligation_subtype0
sorry
end-proof

proof isa FSet__e_fsl_fsl_bsl_bsl_Obligation_subtype1
sorry
end-proof

proof isa FSet__e_bsl_bsl_fsl_fsl_Obligation_subtype
sorry
end-proof

proof isa FSet__power_Obligation_subtype0
  by (simp add: distinct_tl)
end-proof

proof Isa power ()
sorry
termination sorry
end-proof

proof Isa power__stp ()
sorry
termination sorry
end-proof

proof isa FSet__power_Obligation_subtype1
sorry
end-proof

proof isa FSet__power_Obligation_subtype
sorry
end-proof

proof isa FSet__power_Obligation_subtype2
sorry
end-proof

proof isa FSet__forall_p_Obligation_subtype
sorry
end-proof

proof isa FSet__exists_p_Obligation_subtype
sorry
end-proof

proof isa FSet__exists1_p_Obligation_subtype
 by (simp add: FSet__exists_p_Obligation_subtype)
end-proof

proof isa FSet__filter_Obligation_subtype
sorry
end-proof

proof isa FSet__filter_Obligation_subtype0
sorry
end-proof

proof Isa List__permutationOf_equiv
sorry
end-proof

endspec
