%% This file is based on the "relational, binary" version of
%% divide-and-conquer from Alessandro Coglio's Hyperproperties work.

%% The following pair of specs captures the version of D&C in which
%% each problem has one or more solutions (i.e. there is a relation
%% between problems and their solutions) and each problem is
%% decomposed % into two smaller problems.

Params = spec

import /Library/General/EndoRelation

type Problem

type Solution

%% Check whether p is a solution to s:

op solution? (p:Problem) (s:Solution) : Bool

%% Test whether p is directly solvable, without decomposition:

op directly_solvable? (p:Problem) : Bool

op not_directly_solvable? (p:Problem) : Bool = ~(directly_solvable? p)

%% Solve a directly solvable problem:

op solve_directly (p:(Problem | directly_solvable?)) : Solution

%% Decompose a (not directly solvable) problem into two (smaller) problems:

op decompose (p:(Problem | not_directly_solvable?)) : (Problem * Problem)

%% Test whether p1 is a smaller problem than p2:
%% TODO: This one can't be curried because of how wellFounded? is defined?

op smaller? (p1:Problem, p2:Problem) : Bool

%% Compose s1 and s2 give a solution to a larger problem:

op compose (s1:Solution) (s2:Solution) : Solution

%% The direct solution of directly solvable problems is correct:

axiom SolveDirectly is
 fa(p:Problem) directly_solvable? p => solution? p (solve_directly p)

%% Decomposition yields a smaller problem:

axiom Decompose is
 fa(p:Problem, p1:Problem, p2:Problem)
   (not_directly_solvable? p) && decompose p = (p1, p2) =>
     smaller?(p1, p) && smaller?(p2, p)

%% The ordering over problems is well-founded:

axiom WellFounded is
 wellFounded? smaller?

%% Solution composition is correct:

axiom Compose is
 fa(p:Problem,p1:Problem,p2:Problem,s1:Solution,s2:Solution)
   ~ (directly_solvable? p) &&
   decompose p = (p1, p2) &&
   (solution? p1 s1) &&
   (solution? p2 s2) =>
   (solution? p (compose s1 s2))

proof Isa Compose_Obligation_subtype
  apply(auto simp add: not_directly_solvable_p_def)
end-proof

end-spec


Algorithm = spec

import Params

%% Under the assumptions captured by spec Params', the following
%% function produces a solution to every problem via recursive
%% decomposition and composition.

op solve (p:Problem) : Solution =
 if directly_solvable? p then solve_directly p
 else let (p1, p2) = decompose p in (compose (solve p1) (solve p2))

theorem solution_solve is
 fa(p:Problem) solution? p (solve p)

proof Isa solve_Obligation_subtype
  apply(auto simp add: not_directly_solvable_p_def)
end-proof

end-spec
