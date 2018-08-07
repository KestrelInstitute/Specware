(*  

    Algorithm Theory for Global Search

    Global Search (GS) is based on a recursive partitioning of the output
    type R.  The State type is used to represent sets of solutions,
    and the Subspaces/Split operations generate representations for
    subsets.  The search space is then organized as a tree with the
    InitialState as the root, denoting the set of all candidate
    solutions; i.e. R.  An enumeration of the output type can be
    performed by, say, breadth-first search of the tree.  A key
    advantage of global searh algorithms is the possibility of pruning
    internal nodes of the tree, which has the effect of eliminating
    large areas of the search space from further consideration.

    This simple GS theory is extended to handle constraint
     propagation, conflict-directed backjumping, and learning in
     GS_CDBL_Theory (which was used to generate SAT algorithms).

*)

GlobalSearchTheory = spec
  import ProblemTheory#DRO
  type State
  op InitialState : D -> State

  (*  Satisfies(z,s) means that z is "in" the space denoted by s *)
  op Satisfies : R * State -> Bool

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

  (*  All feasible solutions are "in" the initial space ... *)
  axiom reachable_R is
     fa(x:D,z:R)(O(x,z) => Satisfies(z,InitialState(x)))

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

  (* abstract Global Search algorithm to find one feasible solution. *)
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

  theorem correctness_of_GS is
   fa(x:D) (case f(x) of 
              | Some z -> O(x,z) 
              | None -> ~(ex(z)O(x,z)))

end-spec

(*  References

Smith, D.R., Structure and Design of Global Search Algorithms,
Kestrel Technical Report, 1988.
https://www.researchgate.net/publication/239056031_The_structure_and_design_of_global_search_algorithms

Smith, D.R., KIDS: A Semi-Automated Program Development System, IEEE
Transactions on Software Engineering 16(9), Special Issue on Formal
Methods, September 1990, 1024-1043.

Smith, D.R. and Lowry, M.R., Algorithm Theories and Design Tactics,
Science of Computer Programming 14(2-3), Special Issue on the
Mathematics of Program Construction, October 1990, 305-321.

Smith, D.R., KIDS: A Knowledge-Based Software Development System, in
{\em Automating Software Design}, Eds. M. Lowry and R. McCartney, MIT
Press, 1991, 483-514.

Smith, D.R., Constructing Specification Morphisms, Journal of Symbolic
Computation, Special Issue on Automatic Programming, Vol 16, No 5-6,
1993, 571-606.

*)



(*******  Algorithm Taxonomy: Refinement of GenerateAndTest  **********

Intuitively, GS provides a tree-structured generator for a G&T
algorithm.  The extra structure provided by a tree structure allows
pruning at intermediate nodes to preclude exploring large regions of R
that cannot contain feasible solutions.

GT_to_GS = morphism GenerateAndTestTheory -> GlobalSearchTheory
         { State        +-> State
         , InitialState +-> InitialState
         , NextState    +-> breadth-first traversal of the tree
         , FinalState   +-> queue is empty
         , Extract      +-> Extract
         , Reachable    +-> Reachable
         }

*)
