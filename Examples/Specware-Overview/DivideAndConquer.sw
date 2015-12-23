(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% This file is based on the "relational, binary" version of
%% divide-and-conquer from Alessandro Coglio's Hyperproperties work.

%% The following pair of specs captures the version of D&C in which
%% each problem has one or more solutions (i.e. there is a relation
%% between problems and their solutions) and each problem is
%% decomposed % into two smaller problems.

Params = spec

import /Library/General/EndoRelation
import /Library/General/Pred

type Problem

type Solution

%% Check whether p is a solution to s:

op solution? (p:Problem) (s:Solution) : Bool

%% Test whether p is directly solvable, without decomposition:

op directly_solvable? (p:Problem) : Bool

%% Solve a directly solvable problem:

op solve_directly (p:(Problem | directly_solvable?)) : Solution

%% Decompose a (not directly solvable) problem into two (smaller) problems:

op decompose (p:Problem | ~(directly_solvable? p)) : (Problem * Problem)

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
   (~(directly_solvable? p)) && decompose p = (p1, p2) =>
     smaller?(p1, p) && smaller?(p2, p)

%% The ordering over problems is well-founded:

axiom WellFounded is
 wellFounded? smaller?

%% Solution composition is correct:

axiom Compose is
 fa(p:Problem,pa:Problem,pb:Problem,sa:Solution,sb:Solution)
   ~(directly_solvable? p) &&
   decompose p = (pa, pb) &&
   (solution? pa sa) &&
   (solution? pb sb) =>
   (solution? p (compose sa sb))

end-spec


Algorithm = spec

import Params

%% Under the assumptions captured by spec Params', the following
%% function produces a solution to every problem via recursive
%% decomposition and composition.

op solve (p:Problem) : Solution =
 if directly_solvable? p then solve_directly p
 else let (p1, p2) = decompose p in (compose (solve p1) (solve p2))

proof Isa -hook Solution__Predicate_of_solve end-proof

theorem solution_solve is
 fa(p:Problem) solution? p (solve p)

%% start of proofs

proof Isa solve_Obligation_subtype
  apply(auto)
end-proof

%% The parens here cause translation to Isabelle's 'function' construct, rather than 'fun':
proof Isa solve ()
by (pat_completeness, auto)
  termination
  proof (relation "{ x . smaller_p x}")
     show " wf {x . smaller_p x}" by (metis WellFounded)
     next
       fix p x xa y
       assume a1: "Problem__Predicate p"
       assume a2: "\<not> directly_solvable_p p"
       assume a3: "x = decompose p"
       assume a4: "(xa, y) = x"
       from a1 and a2 and a3 and a4 show "(xa, p) \<in> {x. smaller_p x}" 
         by (metis Decompose mem_Collect_eq)
     next     
       fix p x xa y
       assume a1: "Problem__Predicate p"
       assume a2: "\<not> directly_solvable_p p"
       assume a3: "x = decompose p"
       assume a4: "(xa, y) = x"
       from a1 and a2 and a3 and a4 show "(y, p) \<in> {x. smaller_p x}" by (metis Decompose mem_Collect_eq)
  qed
end-proof

proof Isa Solution__Predicate_of_solve
theorem Solution__Predicate_of_solve: 
  "\<lbrakk>Problem__Predicate p\<rbrakk> \<Longrightarrow> Solution__Predicate (solve p)"
  apply(induct rule: solve.induct)
  apply(cut_tac p=p in solve.simps(1))
  apply(simp del: solve.simps)
  apply(case_tac "directly_solvable_p p")
  apply(simp del: solve.simps)
  apply(rule solve_directly_subtype_constr)
  apply(simp)
  apply(simp)
  apply(simp del: solve.simps)
  apply(case_tac "decompose p")
  apply(simp del: solve.simps)
  apply(rule compose_subtype_constr)
  apply (metis bool_Compl_def decompose_subtype_constr)
  apply (metis bool_Compl_def decompose_subtype_constr1)
  done
end-proof

proof Isa solution_solve
  apply(induct rule: solve.induct)
  apply(cut_tac p=p in solve.simps(1))
  apply(simp del: solve.simps)
  apply(case_tac "directly_solvable_p p")
  apply(simp del: solve.simps)
  apply(rule SolveDirectly)
  apply(simp)
  apply(simp)
  apply(simp del: solve.simps)
  apply(case_tac "decompose p")
  apply(simp del: solve.simps)
  apply(rule Compose)
  apply(simp)
  apply(rule Solution__Predicate_of_solve)
  apply(simp)
  apply (metis decompose_subtype_constr)
  apply (metis Solution__Predicate_of_solve bool_Compl_def decompose_subtype_constr1)
  apply (metis decompose_subtype_constr)
  apply(auto)[1]
  apply (metis bool_Compl_def decompose_subtype_constr)
  apply (metis bool_Compl_def decompose_subtype_constr1)
end-proof




end-spec
