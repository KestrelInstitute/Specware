(* Copyright 2018 Kestrel Institute. See file LICENSE for license details *)

(*
    A collection of the most common Problem Reduction Algorithm schemes.

  The intuitive idea of Problem Reduction (PR) algorithms is
  divide-and-conquer: to solve a hard problem, decompose it into
  parts, solve the parts, then compose the solutions to the parts.
  The PR theory here is really just the optimization version of
  Divide-and-Conquer.

  Problem reduction structure is founded on a set of constructors that
  can be used to constructor any solution.  As with homomorphisms,
  there are an infinite class of signatures (corresponding to
  endofunctors) and one algorithm theory per signature.  This file
  lists two of the most commonly used signatures and there PR
  theories.


Each problem-reduction theory corresponds to a particular signature
for the (co)algebras on its input and output types.  A
problem-reduction solver is essentially a homomorphism from the input
type to the output type.

  The first scheme is simple singleton-split PR theory.  PR_01 is
based on the signature implicit in the type functor

    F(T) = 1 + E*T,
for auxilliary type E.

The input type is treated as coinductive (based on destructors);
The output type is treated as inductive (based on constructors).

PR_01 specifies the problem structure that is sufficient to justify a
problem-reduction solution to the given problem.  PR_01_scheme then
provides a schematic solver algorithm and specifications for
subalgorithms.  The hard work in applying PR theory is constructing a
morphism from PR_01 to the problem domain.  In the references, we use
deductive calculation to perform key parts of the construction.  Once
a morphism from PR_01 has been built, the instantiation of the
algorithm scheme in PR_01_scheme is an automatic pushout/substitution
operation.

We construct a morphism (interpret) from PR_01 by either

(1) selecting a library coalgebra (destructor set) for input type D
and then calculate a algebra (constructor set) for output type R,

or, conversely,

(2) selecting a library algebra (constructor set) for output type R
and then calculate a coalgebra (destructor set) for input type D.

*)

PR_01 = spec
 import DivideAndConquer#DC_01

(* completeness ensures that every feasible solution can be
 constructed from feasible solutions to subproblems. *)
 axiom Completeness0 is
   fa(x:D,z:R) I0(x) => (O(x,z) => O_D0(x) && O_C0(z))

 axiom Completeness1 is
   fa(x0:D) fa(z0:R)
   I1(x0)
   => (O(x0,z0)
       =>
       (ex(e:E,x1:D,z1:R)
         O_D1(x0,e,x1)
         && O(x1, z1)
         && O_C1(z0,e,z1)))

 end-spec

PR_01_scheme = spec
  import PR_01

% empty/constant case

  op D0(x0:D | I0 x0): ()
  op C0:{z:R | O_C0 z}

% singleton split
  op D1(x0:D | I1 x0):{ed:E*D | O_D1(x0, ed.1, ed.2)}
  op C1(e:E,z1:R | ex(x1:D) O(x1,z1)):
       {z0:R | O_C1(z0, e, z1)}

% PR scheme (same as D&C)
  op F: D->R
  def F(x:D) =
     if I0(x) then C0
     else let (e,x1) = D1(x) in
          C1(e, F x1)

  theorem correctness_of_F is
    fa(x:D) O(x, F x)

end-spec

(*******************************************************************
                 Optimization version of PR_01
********************************************************************)

PR_01_opt = spec
 import PR_01, ProblemTheory#DROOpt % add cost to PR_01

(* This is the essence of Bellman's Principle of Optimality: An
 optimal solution (z0 for instance x0) can be composed from an optimal
 (z1) to a subproblem instance (x1) *)
 axiom Optima_Completeness1 is
   fa(x0:D) fa(z0:R)
   I1(x0)
   => (
       O(x0,z0) && (fa(z0') O(x0,z0') => (cost(x0,z0) <= cost(x0,z0')))
       =>
       (ex(e:E,x1:D,z1:R)
          O_D1(x0,e,x1)
          && O(x1, z1) && (fa(z1')(O(x1,z1') => cost(x1,z1) <= cost(x1,z1')))
          && O_C1(z0,e,z1))
      )

 end-spec

PR_01_optimization_scheme = spec
  import PR_01_opt

% empty/constant case
  op D0(x0:D | I0 x0): ()
  op C0:{z:R | O_C0 z}

% singleton split into all decompositions
  op D1(x0:D | I0 x0):
      {ds: List (E*D) | fa(decomp:E*D) decomp in? ds
                        => O_D1(x0,decomp.1,decomp.2)
                        && measure decomp.2 < measure x0}
  op C1(e:E,z1:R | ex(x1:D) O(x1,z1)):
       {z0:R | O_C1(z0, e, z1)}

% PR_opt scheme
  def F(x:D):{z:R | O(x,z)} =
     if I0(x) then C0
     else (let ds:List (E*D) = D1(x) in
           let d1 = head ds in
           let dtail = tail ds in
           let e:E = d1.1 in
           let x1:D = d1.2 in
           let z1:R = C1(e, F x1) in
           F1_gt(ds, z1, cost(x,z1)))

% GT_opt subalgorithm to find an optimal composition
  def F1_gt(ds:List (E*D),
            currentBestSol:R,
            currentBestCost:Nat) : R =
    case ds of
      | Nil -> currentBestSol
      | ed::tl -> let e:E = ed.1 in
                  let x1:D = ed.2 in
                  let z1:R = C1(e, F x1) in
                  let cost1:Nat = cost(x1,z1) in
                  let b:Boolean = cost1 < currentBestCost in
                  let nextBestSol  = (if b then z1 else currentBestSol) in
                  let nextBestCost = (if b then cost1 else currentBestCost) in
                  F1_gt(tl, nextBestSol, nextBestCost)

  theorem correctness_of_F is
   fa(x:D)fa(z:R) z=F x => O(x,z) && (fa(z')(O(x,z') => cost(x,z) <= cost(x,z')))

end-spec




(* ===================================================================

  This is simple binary-split PR theory.
  Instances include quicksort, mergesort,...

PR_012 is based on the signature implicit in the type functor
    F(T) = 1 + E + T*T,
for auxilliary type E.

The input type is treated as coinductive (based on destructors);
The output type is treated as inductive (based on constructors).

PR_012 specifies the problem structure that is sufficient to justify a
problem-reduction solution to the given problem.  PR_012_scheme then
provides a schematic solver algorithm and specifications for
subalgorithms.  The hard work in applying PR theory is constructing a
morphism from PR_012 to the problem domain.  In the references, we use
deductive calculation to perform key parts of the construction.  Once
a morphism from PR_012 has been built, the instantiation of the
algorithm scheme in PR_012_scheme is an automatic pushout/substitution
operation.

We construct a morphism (interpret) from PR_012 by either

(1) selecting a library coalgebra (destructor set) for input type D
and then calculate a algebra (constructor set) for output type R,

or, conversely,

(2) selecting a library algebra (constructor set) for output type R
and then calculate a coalgebra (destructor set) for input type D.

*)

PR_012 = spec
 import DivideAndConquer#DC_012

 axiom Completeness0 is
   fa(x:D,z:R) I0(x) => (O(x,z) => O_D0(x) && O_C0(z))

 axiom Completeness1 is
   fa(x:D,z:R) I1(x) => (ex(e:E)(O(x,z) => O_D1(x,e) && O_C1(z, e)))

 axiom Completeness2 is
   fa(x0:D) fa(z0:R)
   I2(x0)
   => (O(x0,z0)
       =>
       (ex(x1:D,x2:D)ex(z1:R,z2:R)
         O_D2(x0,x1,x2)
         && O(x1, z1) && O(x2, z2)
         && O_C2(z1, z2, z0)))

 end-spec


(* This abstract program provides top-down control when searching for
a single feasible solution. For a classical dynamic programming
solution, develop a bottom-up control strategy with tabulation of
intermediate results.  *)

PR_012_scheme = spec
  import PR_012

% empty/constant case
  op D0(x0:D | I0 x0): ()
  op C0:{z:R | O_C0 z}

% singleton split
  op D1(x0:D | I1 x0):{e:E | O_D1(x0,e)}
  op C1(e:E): {z0:R | O_C1(z0, e)}

% binary split case, also need wfo
  op D2(x0:D | I2 x0):
       {(x1,x2):D*D | O_D2(x0,x1,x2)
                    && measure x0 > measure x1
                    && measure x0 > measure x2
       }
  op C2(z1:R,z2:R): {z0:R | O_C2(z0, z1,z2)}

% PR scheme
  def F(x) =
     if I0(x) then C0
     else if I1(x) then C1(D1(x))
     else let x1x2 = D2(x) in
             C2(F(x1x2.1), F(x1x2.2))

  theorem correctness_of_F is fa(x:D) O(x, F(x))

end-spec

(*******************************************************************
                 Optimization version of PR_012
********************************************************************)

PR_012_opt = spec
 import ProblemTheory#DROOpt, ProblemReduction#PR_012

(* This is the essence of Bellman's Principle of Optimality: An
 optimal solution (z0 for instance x0) can be composed from optimal
 instances (z1 for instance x1 and z2 for instance x2) *)

 axiom Optima_Completeness2 is
   fa(x0:D) fa(z0:R)
   I1(x0)
   => (
       O(x0,z0) && (fa(z0') O(x0,z0') => (cost(x0,z0) <= cost(x0,z0')))
       =>
       (ex(x1:D,z1:R,x2:D,z2:R)
          O_D2(x0,x1,x2)
          && O(x1, z1) && (fa(z1')(O(x1,z1') => cost(x1,z1) <= cost(x1,z1')))
          && O(x2, z2) && (fa(z2')(O(x2,z2') => cost(x2,z2) <= cost(x2,z2')))
          && O_C2(z0,z1,z2))
      )

 end-spec

(* This abstract program provides top-down control when searching for
a single feasible solution. For a classical dynamic programming
solution, develop a bottom-up control strategy with tabulation of
intermediate results.  *)

PR_012_opt_scheme = spec
  import PR_012_opt

% empty/constant case
  op D0(x0:D | I0 x0): ()
  op C0:{z:R | O_C0 z}

% singleton split for all decompositions, constructed output
%  op D1(x0:D | I0 x0): { es:List E | fa(e:E) O_D1(x0,e)}
  op D1(x0:D | I0 x0): { e:E | O_D1(x0,e)}
  op C1(e:E): {z0:R | O_C1(z0, e)}

% binary split case, also need wfo
  op D2(x0:D | I2 x0):
       {ds:List (D*D) | fa(decomp:D*D) decomp in? ds =>
                          O_D2(x0,decomp.1,decomp.2)
                          && measure x0 > measure decomp.1
                          && measure x0 > measure decomp.2 }
  op C2(z1:R,z2:R): {z0:R | O_C2(z0, z1,z2)}

  def F(x:D):{z:R | O(x,z)} =
     if I0(x)      then C0
     else if I1(x) then C1(D1(x))
     else (let ds:List(D*D) = D2 x in
           let d1 = head ds in
           let dtail = tail ds in
           let x1:D = d1.1 in
           let x2:D = d1.2 in
           let z1:R = F x1 in
           let z2:R = F x2 in
           let z0:R = C2(z1,z2) in
           F2_gt(x,dtail, z0, cost(x,z0)))


% GT_opt subalgorithm to find an optimal composition
  def F2_gt(x:D, ds:List (D*D),
            currentBestSol:R,
            currentBestCost:Nat) : R =
    case ds of
      | Nil -> currentBestSol
      | dd::tl -> let x1:D = dd.1 in
                  let x2:D = dd.2 in
                  let z1:R = F x1 in
                  let z2:R = F x2 in
                  let z0:R = C2(z1,z2) in
                  let z0cost:Nat = cost(x,z0) in
                  let b:Boolean = z0cost < currentBestCost in
                  let nextBestSol  = (if b then z0 else currentBestSol) in
                  let nextBestCost = (if b then z0cost else currentBestCost) in
                  F2_gt(x, tl, nextBestSol, nextBestCost)

  theorem correctness_of_F is
    fa(x:D)fa(z:R) z=F x => O(x,z) && (fa(z')(O(x,z') => cost(x,z) <= cost(x,z')))

end-spec


(*   References

Smith, D.R., Structure and Design of Problem Reduction Generators, in
{\em Constructing Programs from Specifications}, Ed. B. Moeller,
North-Holland, Amsterdam, 1991, 91-124.

*)

(*******  Algorithm Taxonomy: Refinement of GenerateAndTest  **********

Intuitively, PR directly constructed a feasible solution, if one
exists, rather than searching for one.  It is a special case of
AND-reduction search in which we can guide the search directly to a
feasible solution.   We illustrate the taxonomy refinement by example:

GT_to_PR = morphism GenerateAndTestTheory -> PR_01
         { State        +->
         , InitialState +->
         , Extract      +->
         , NextState    +->
         , Reachable    +->
         }

*)
