(* Copyright 2018 Kestrel Institute. See file LICENSE for license details *)

(*

        Algorithm Theory for Generate-and-Test algorithms

The specification starts by importing basic problem theory DRO,
which characterizes problems in terms of
   D - input type, the given data
   R - output type, the results
   O - satisfaction predicate, which decides when an output z:R is
   feasible (acceptable) with respect to input instance x:D.

Interpreting these symbols into a problem domain gives us enough
information to specify a problem-solver:

  op f(x:D):{z:R | O(x,z)}

although this function spec is not part of DRO itself.  DRO is so
simple as to seem vacuous, but it allows us to specify abstract
algorithms, such as generate-and-test, that solve a given problem
without concern for the details of a concrete problem.

Generate-and-test (G&T) is the most general algorithm strategy in that
it assumes the weakest of all possible structure in defining a
problem:

1. the output type is enumerable
2. the satisfaction predicate (input/output relation) is decidable

G&T works by enumerating the output type, testing whether each
candidate element is feasible.  G&T is the essential tool used in
computability theory, used to prove that a function is computable.
All recursive partial functions can be computed using a G&T algorithm.
Moreover, if the output type is finite, then G&T can be used to
enumerate/count all feasible solutions or to find optimal solutions
relative to a specified cost function.

The characteristic operation of a G&T algorithm is the generator that
enumerates the output type.  We treat it as a transformer of a cotype
whose behavior is to generate a sequence of states that project to
exactly the set of elements in the output type R (via the Extract
operator).

The G&T theory has a ghost or specification variable, Reachable, that
helps to specify a key property of the algorithm, but is not (usually)
needed in actual computation.  Ghost variables and functions specify
properties of a computation, but are not needed in the computation
itself.  Other typical ghost variables might reflect time/space
utilization or the history of a computation.

For proof of correctness, we assume that the output domain is finite.
We do that by the axioms reachable_R (all elements of output type R
are generable via the NestState transformer), and finite_reachability
whcih asserts that the generation process terminates.

For real-world problems where the domain is infinite, we usually apply
G&T to a finite approximation, where the output domain is a finite
subset of the real-world domain.

Issues:
 - typically R is a dependent-type R(x)
 - all refinements of G&T must implement InitialState and NextState
   so that the reachable_R axiom is provable.  This is cumbersome, but
   needed to fully formalize the refinement relation.

*)

GenerateAndTestTheory = spec
  import ProblemTheory#DRO

  type State
  op InitialState : D -> State
  op NextState :  D*State -> Option State     % generate the next state
  op Extract : State -> R   % extract an R value from state

  (* ghost function to test whether a state dest can be reached
  from state st in k steps *)
  op Reachable(x:D, dest:State, st:State, k:Nat): Boolean =
    if dest = st
      then true
    else if k=0
      then false
    else (case NextState(x,st) of
           | None     -> false
           | Some st' -> Reachable(x,dest, st', k-1))

  (*  All elements of R are reachable via NextState. *)
  axiom reachable_R is
     fa(x:D,z:R)
     ex(k:Nat,dest:State)
     Reachable(x,dest,InitialState x, k)
     && Extract dest = z

  (* NextState can be iterated only finitely many times. *)
  axiom finite_reachability is
     fa(x:D)ex(k:Nat, st:State)
     NextState(x,st) = None
     && Reachable(x,st,InitialState x, k)

(* reachable_R && finite_reachability => R is finite *)

 end-spec


(*****************   G&T Scheme   ************************)

GenerateAndTest = spec
  import GenerateAndTestTheory

  def f(x:D): Option R =
    GT(x, InitialState x)

  def GT(x:D, st:State) : Option R =
    let z = Extract st in
    (if O(x,z)
       then Some z                 % success case
     else (case NextState(x,st) of
             | None     -> None    % failure case
             | Some st' -> GT(x, st')))

  theorem correctness_of_GT is
   fa(x:D) (case f(x) of
              | Some z -> O(x,z)
              | None -> ~(ex(z)O(x,z)))

end-spec


(* ========================================================
    Generate-and-Test for optimization problems
   ========================================================
*)


GenerateAndTestOptTheory = spec
  import GenerateAndTestTheory, ProblemTheory#DROOpt
 end-spec


(*****************   G&T Optimization Scheme   ************************)

GenerateAndTestOpt = spec
  import GenerateAndTestOptTheory

  def f(x:D): Option R =
    GT(x, InitialState x, Extract(InitialState x))

  def GT(x:D, st:State, currentBest:R) : Option R =
    let z:R = Extract st in
    let nextBest:R = (if O(x,z) && cost(x,z) < cost(x,currentBest)
                        then z
                      else currentBest) in
    case NextState(x,st) of
      | None     -> Some nextBest          %% success
      | Some st' -> GT(x, st', nextBest)

  theorem correctness_of_GTOpt is
   fa(x:D) (case f(x) of
              | Some z -> O(x,z)
                          && (fa(x1:D,z1:R) O(x1,z1) => cost(x,z)<=cost(x1,z1))
              | None -> ~(ex(z)O(x,z)))

end-spec
