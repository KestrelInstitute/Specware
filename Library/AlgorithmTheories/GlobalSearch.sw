(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*  New formulation of GS theory to clarify/simplify
    pruning, propagation (both necessary and consistency-preserving)
*)

GlobalSearchTheory = spec
  import ProblemTheory#DROfPartial
  type State
  axiom StateInhabited is ex(st: State) true
  op InitialState : D -> State

  (*  Satisfies(z,s) means that z is "in" the space denoted by s *)
  op Satisfies : R * State -> Bool

  (*  All feasible solutions are "in" the initial space ... *)

  axiom initial_space_contains_all_solutions is
     fa(x:D,z:R)(O(x,z) => Satisfies(z,InitialState(x)))

   (* ... and the elements in a space are either directly extractable
   or can be extracted after splitting into subspaces.  We want the
   least fixpoint of this recursive def. *)

  op Extract : State -> Option R
  type SplitInfo
  op Subspaces : State -> List SplitInfo
  op Split : State * SplitInfo -> State

   axiom definition_of_satisfies is
     fa(x:D, s:State, z:R)
      Satisfies(z, s) =
        ((Extract(s) = Some z)
	    || 
	 (ex (si:SplitInfo)
             (si in? Subspaces(s) && Satisfies(z, Split(s,si)))))

  (* Phi is a pruning test in backtracking.  It is defined as a
  necessary condition on existence of a feasible solution in the
  current subspace. *)

   op Phi : State -> Bool
   axiom characterization_of_necessary_pruning_test_phi is
     fa(x:D,z:R,s:State)(Satisfies(z,s) && O(x,z) => Phi(s))

 end-spec


(*****************   GS Scheme with pruning   ************************)

GlobalSearch = spec 
  import GlobalSearchTheory

  (* This is the top level of the Global Search algorithm to find one
  feasible solution.  *)

  def f(x:D): Option R = 
    if Phi(InitialState(x))
    then GS(x,InitialState(x))
    else None

  (* GS explores the search tree using a depth-first strategy.  *)

  def GS(x:D, r:State| Phi(r) ) : Option R = 
    let sol: Option R = Extract(r) in
    case sol of
      | Some z | O(x,z) -> Some z
      | _ -> GSAux(x, r, Subspaces(r))

  (* GSAux explores the children of a space.  *)

  def GSAux(x:D, r:State, rs:List SplitInfo | Phi(r)) : Option R = 
    case rs of
      | []   -> None 
      | hd::tl -> if Phi(Split(r,hd))
                  then (case GS(x,Split(r,hd)) of
                         | None -> GSAux(x,r,tl)
                         | Some r -> Some r)
                  else  GSAux(x,r,tl)

  theorem correcness_of_GS is
   fa(x:D) (case f(x) of 
              | Some z -> O(x,z) 
              | None -> ~(ex(z)O(x,z)))

end-spec
