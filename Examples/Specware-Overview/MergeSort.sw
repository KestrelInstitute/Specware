Sorting = spec

  import /Library/Base/List_Executable

%% TODO: Generalize the Nat here?
  op sorted? (lst : List Nat) : Bool =
    case lst of
      | [] -> true
      | hd::[] -> true
%%FIXME: I want to write this, but I get an Isabelle error:
%%    | hd::(rest as next::_) -> (hd <= next) && sorted? rest
      | hd::next::rest -> (hd <= next) && sorted? (next::rest)

  proof Isa sorted_p_Obligation_exhaustive
    apply(metis list.exhaust)
  end-proof

  theorem sorted_of_cons is
    fa(hd : Nat, tl : List Nat) sorted? (hd::tl) = (if tl = [] then true else ((hd <= head tl) && sorted? tl))

  %TODO: Does this already exist somewhere?
  theorem equiLong_self is [a]
    fa(lst : List a) lst equiLong lst

  theorem permutationOf_self is [a]
    fa(lst : List a) lst permutationOf lst

  theorem permutationOf_symmetric is [a]
    fa(x : List a, y : List a) (x permutationOf y) = (y permutationOf x)

  theorem permutationOf_cons_and_cons is [a]
    fa(hd:a, tla : List a, tlb : List a) (hd::tla permutationOf hd::tlb) = (tla permutationOf tlb)

  theorem permutationOf_cons_and_cons_lemma is [a]
    fa(hd:a, other : a, tla : List a, tlb : List a) (other::hd::tla permutationOf hd::tlb) = (other::tla permutationOf tlb)

  theorem permutationOf_append_cons is [a]
    fa(hd:a, tl : List a, x : List a) x++(hd::tl) permutationOf hd::(x++tl)

  theorem permutationOf_append_cons_2 is [a]
    fa(hd:a, tl : List a, x : List a) hd::(x++tl) permutationOf x++(hd::tl)

  theorem permutationOf_transitive is [a]
    fa(x : List a, y : List a, z : List a) (x permutationOf y && y permutationOf z) => x permutationOf z

  theorem div_2_bound is
    fa(n:Nat) ~(n = 0) => n div 2 < n

  theorem permutationOf_append is [a]
    fa(x: List a, y: List a, z: List a) x permutationOf y => (x ++ z permutationOf y ++ z)

  theorem permutationOf_append_2 is [a]
    fa(x: List a, y: List a, z: List a) x permutationOf y => (z ++ x permutationOf z ++ y)

  %% Proofs start here:

  proof Isa permutationOf_append
    sorry
  end-proof

  proof Isa permutationOf_append_2
    sorry
  end-proof


  proof Isa permutationOf_self
    apply(simp add: List__permutationOf__1__obligation_refine_def)
    apply(induct lst )
    apply(simp)
    apply(simp)
  end-proof

  proof Isa div_2_bound
    sorry
  end-proof

  proof Isa sorted_of_cons
    apply(case_tac "tl__v")
    apply(auto)
  end-proof

  proof Isa permutationOf_transitive
    sorry
  end-proof

  proof Isa permutationOf_cons_and_cons
    apply(auto simp add: List__permutationOf__1__obligation_refine_def)
  end-proof

  proof Isa permutationOf_append_cons
    sorry
  end-proof

  proof Isa permutationOf_append_cons_2
    sorry
  end-proof

  proof Isa permutationOf_cons_and_cons_lemma
    sorry
  end-proof

  proof Isa permutationOf_symmetric
    sorry
  end-proof

end-spec


MergeSort0 = spec

  import /Library/General/EndoRelation
  import /Library/General/Pred
  import Sorting
 
  %% Problems and Solutions are both NatLists:

  type NatList = List Nat

  %% s is a solution to p if it is a sorted permutation of p:

  op solution? (p:NatList) (s:NatList) : Bool = permutationOf(s,p) && sorted? s

  %% A list of length 0 or 1 is already sorted:

  op directly_solvable? (p:NatList) : Bool = length p < 2

  %% To sort a list of length 0 or 1, just return it:

  op solve_directly (p:(NatList | directly_solvable?)) : NatList = p

  %% The decompose operation splits a list into two pieces:

  op splitList (lst : NatList | length lst > 1) : NatList * NatList = 
    let n = (length lst) div 2 in
      (prefix(lst,n), suffix(lst,n))

  %% To test whether a list is smaller than another list, we compare the lengths:

  op smaller? (p1:NatList, p2:NatList) : Bool = length p1 < length p2

  %% The compose operation merges two sorted lists:

  op mergeLists (lst1 : NatList) (lst2 : NatList) : NatList =
   case lst1 of
   | [] -> lst2
   | hd1::tl1 -> (case lst2 of
                  | [] -> lst1
                  | hd2::tl2 -> (if hd1 < hd2 then hd1::(mergeLists tl1 lst2) else hd2::(mergeLists lst1 tl2)))

  theorem sorted_of_mergeLists is
    fa(s1:NatList, s2:NatList) (sorted? s1) && (sorted? s2) => sorted? (mergeLists s1 s2)

  theorem mergeLists_perm is
    fa(x:NatList, y:NatList) (mergeLists x y) permutationOf x ++ y

  theorem splitList_perm is
    fa(p:NatList) ~(length p < 2) => p permutationOf (splitList p).1 ++ (splitList p).2


  proof Isa sorted_of_mergeLists
    apply(induct s1 s2 rule: mergeLists.induct)
    apply(simp add: mergeLists.simps)
    apply(simp add: mergeLists.simps)
    apply(auto simp add: sorted_of_cons)
    apply(case_tac "tl2")
    apply(auto)
    apply(case_tac "tl1")
    apply(auto)
    apply(case_tac "tl1")
    apply(auto)
    apply(case_tac "tl2")
    apply(auto)
  end-proof

  proof Isa mergeLists_perm
     apply(induct x y rule: mergeLists.induct)
     apply(simp add: mergeLists.simps permutationOf_self)
     apply(simp add: permutationOf_self)
     apply(case_tac "hd1 < hd2")
     apply(simp add: permutationOf_cons_and_cons)
     apply(auto)
     apply(cut_tac hd__v=hd2 and tla = "mergeLists (hd1 # tl1) tl2" and tlb = "hd1 # tl1 @ tl2" in permutationOf_cons_and_cons)
     apply(rule permutationOf_transitive)
     apply(auto simp add: permutationOf_cons_and_cons_lemma)
     apply(rule permutationOf_append_cons_2)
  end-proof

  proof Isa splitList_perm
    sorry
  end-proof

end-spec

M = morphism DivideAndConquer#Params -> MergeSort0 {Solution +-> NatList, Problem +-> NatList, compose +-> mergeLists, decompose +-> splitList}

proof Isa SolveDirectly
  apply(simp add: directly_solvable_p_def solution_p_def solve_directly_def permutationOf_self)
  apply(case_tac "length p")
  apply(simp)
  apply(case_tac "nat")
  apply(simp add: sorted_p.simps)
  apply(case_tac "p")
  apply(simp)
  apply(simp add: sorted_p.simps)
  apply(metis Zero_neq_Suc lessI less_2_cases less_Suc0)
end-proof

proof Isa Decompose_Obligation_subtype
  apply(simp add: Pred__e_tld_tld_def)
end-proof

proof Isa Decompose
  apply(simp add: smaller_p_def directly_solvable_p_def splitList_def)
  apply(auto simp add: Let_def)
end-proof

proof Isa WellFounded
  apply(auto simp add:wf_def smaller_p_def)
  apply(metis (full_types) length_induct)
end-proof

proof Isa Compose_Obligation_subtype
  apply(simp add: Pred__e_tld_tld_def)
end-proof

proof Isa Compose
  apply(auto simp add: solution_p_def directly_solvable_p_def)
  defer
  apply(rule sorted_of_mergeLists)
  apply(simp_all)
  apply(cut_tac x=s1 and y=s2 in mergeLists_perm)
  apply(rule permutationOf_transitive [of "mergeLists s1 s2" "s1 @ s2"])
  apply(simp)
  apply(cut_tac p=p in splitList_perm)
  apply(simp)
  apply(simp)
  apply(metis permutationOf_append permutationOf_append_2 permutationOf_symmetric permutationOf_transitive)
end-proof


MergeSort = DivideAndConquer#Algorithm[M]
