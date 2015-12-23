(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Sorting = spec

  import /Library/General/ListFacts

%% TODO: Generalize the Nat here?  pass in an ordering?
  op sorted? (lst : List Nat) : Bool =
    case lst of
      | [] -> true
      | hd::[] -> true
%%TODO: I want to write this, but I get an Isabelle error:
%%    | hd::(rest as next::_) -> (hd <= next) && sorted? rest
      | hd::next::rest -> (hd <= next) && sorted? (next::rest)

  proof Isa sorted_p_Obligation_exhaustive
    apply(metis list.exhaust)
  end-proof

  theorem sorted_of_cons is
    fa(hd : Nat, tl : List Nat) sorted? (hd::tl) = (if tl = [] then true else ((hd <= head tl) && sorted? tl))

  theorem div_2_bound is
    fa(n:Nat) ~(n = 0) => n div 2 < n

  %% Proofs start here:

  proof Isa div_2_bound
    by (metis div_less_dividend gr0I one_less_numeral_iff semiring_norm(76))
  end-proof

  proof Isa sorted_of_cons
    apply(case_tac "tl__v")
    apply(auto)
  end-proof

end-spec


MergeSort0 = spec

  import /Library/General/EndoRelation
  import /Library/General/Pred
  import Sorting
 
  %% Problems and Solutions are both NatLists:

  type NatList = List Nat

  %% s is a solution to p if it is a sorted permutation of p:

  op solution? (p:NatList) (s:NatList) : Bool = permutesTo?(s,p) && sorted? s

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
  %% TODO: Add sortedness to the types?

  op mergeLists (lst1 : NatList) (lst2 : NatList) : NatList =
   case lst1 of
   | [] -> lst2
   | hd1::tl1 -> (case lst2 of
                  | [] -> lst1
                  | hd2::tl2 -> (if hd1 < hd2 then hd1::(mergeLists tl1 lst2) else hd2::(mergeLists lst1 tl2)))

  theorem sorted_of_mergeLists is
    fa(s1:NatList, s2:NatList) (sorted? s1) && (sorted? s2) => sorted? (mergeLists s1 s2)

  theorem mergeLists_perm is
    fa(x:NatList, y:NatList) permutesTo?(mergeLists x y,  x ++ y)

  theorem splitList_perm is
    fa(p:NatList) ~(length p < 2) => permutesTo?(p, (splitList p).1 ++ (splitList p).2)

   theorem SolveDirectly is fa(p: NatList) directly_solvable? p => solution? p (solve_directly p)
 
  theorem Decompose is 
    fa(p: NatList, p1: NatList, p2: NatList) 
     ~(directly_solvable? p) && splitList p = (p1, p2) => smaller?(p1, p) && smaller?(p2, p)
 
  theorem WellFounded is EndoRelation.wellFounded? smaller?
 
  theorem Compose is 
    fa(p: NatList, pa: NatList, pb: NatList, sa: NatList, sb: NatList) 
     ~(directly_solvable? p) && splitList p = (pa, pb) 
                             && solution? pa sa 
                             && solution? pb sb => solution? p (mergeLists sa sb)
 
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
    apply(case_tac "tl1")
    apply(auto)
    apply(case_tac "tl1")
    apply(auto)
    apply(case_tac "tl2")
    apply(auto)
    apply(case_tac "tl2")
    apply(auto)
  end-proof

  proof Isa mergeLists_perm
     apply(induct x y rule: mergeLists.induct)
     apply(simp add: mergeLists.simps permutesTo_p_reflexive)
     apply(simp add: permutesTo_p_reflexive)
     apply(case_tac "hd1 < hd2")
     apply(simp add: permutesTo_p_cons_and_cons)
     apply(auto)
     apply(cut_tac hd__v=hd2 and tla = "mergeLists (hd1 # tl1) tl2" and tlb = "hd1 # tl1 @ tl2" in permutesTo_p_cons_and_cons)
     apply(rule permutesTo_p_transitive)
     apply(auto simp add: permutesTo_p_cons_and_cons_lemma)
     apply(rule permutesTo_p_append_cons_2)
  end-proof

  proof Isa splitList_perm
    sorry
  end-proof

proof Isa SolveDirectly
  apply(simp add: directly_solvable_p_def solution_p_def solve_directly_def permutesTo_p_reflexive)
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
  apply(simp add: directly_solvable_p_def)
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
  apply(simp add: directly_solvable_p_def)
end-proof

proof Isa Compose
  apply(auto simp add: solution_p_def directly_solvable_p_def)
  defer
  apply(rule sorted_of_mergeLists)
  apply(simp_all)
  apply(cut_tac x=sa and y=sb in mergeLists_perm)
  apply(rule permutesTo_p_transitive [of "mergeLists sa sb" "sa @ sb"])
  apply(simp)
  apply(cut_tac p=p in splitList_perm)
  apply(simp)
  apply(simp)
  apply(metis permutesTo_p_append_cancel permutesTo_p_append_cancel2 permutesTo_p_symmetric permutesTo_p_transitive)
end-proof

end-spec

M = morphism DivideAndConquer#Params -> MergeSort0 {Solution +-> NatList, 
                                                    Problem +-> NatList,
                                                    compose +-> mergeLists,
                                                    decompose +-> splitList,
                                                    smaller? +-> smaller?,
                                                    directly_solvable? +-> directly_solvable?, 
                                                    solve_directly +-> solve_directly}


MergeSort = DivideAndConquer#Algorithm[M]

%% Termination proof for solve:
proof Isa solve ()
  by (pat_completeness, auto)
  termination
  apply(relation "{ x . smaller_p x}")
  apply(metis WellFounded)
  apply (metis Decompose mem_Collect_eq)
  apply (metis Decompose mem_Collect_eq)
end-proof

%% FIXME: the theorem Solution__Predicate_of_solve seems to be
%% incorrectly present in the Isabelle translation of MergeSort
%% (Isa/MergeSort.thy).  It mentions Problem__Predicate and
%% Solution__Predicate, which are not defined in that Isabelle theory.
%% This theorem seems to be incorrectly carried over from the abstract
%% DivideAndConquer theory.

%% TODO: Finish this proof (FIXME: really we should get it for free
%% from the spec substitution, but that may require specs to be
%% translated to locales).  Here we attempt to override the proof
%% pragma of the same name from DivideAndConquer#Algorithm.  
proof Isa solution_solve
  sorry
end-proof

%% Top-level spec of what we want:
MergeSortSpec = spec 
  import Sorting
  op mergeSort (lst : List Nat) : List Nat
  axiom mergeSort_correct is
    fa(x: List Nat) sorted? (mergeSort x) && permutesTo?(x, mergeSort x)
end-spec

%% The proof of the axiom should follow from the proof of correctness of the solver in spec MergeSort.
final = morphism MergeSortSpec -> MergeSort {mergeSort +-> solve}
