(*   

     Algorithm Theory for Workset-Based Small-Step Fixpoint Iteration

     This spec formalizes the small-step Kleene fixpoint iteration,
     instantiated to the powerset lattice.

            D ----- O ------> R
            |                 ^
            |                 |
       initialSet          extract
            |                 |
            v                 |
            S0 - lfp(S0,F) -> Sn

   The problem is solved by a fixpoint of F above a given element of
   the partial order.  Then, we use an appropriate iterator (lfp here)
   to compute a least fixpoint as an algorithm solution.  To compute a
   gfp, simply interpret the <= operator in a contravariant way, as >=
   in the problem domain.

   Because the partial order is finite we have immediately that it is
   complete, therefore the lfp is well-defined.

  To apply this algorithm theory, we need to construct a classification morphism
      FixpointIterationWorksetTheory -> Problem Domain  (see below)
  and then compute the pushout with FixpointIterationWorksetAlgorithm. 

  See the References for work on a dynamic state-based generalization
  of Tarski's fixpoint theorem and corresponding algorithm.

*)

FixpointIterationWorksetTheory = 
spec
  import ProblemTheory#DRO
  import ../DataStructures/Sets
  type X
  type SetX = Set X
  import translate ../Math/PartialOrder#MonotoneFn by {A +-> SetX, <= +-> subset}

  op initialSet: D -> SetX
  op extract : SetX -> R
  op F : D -> SetX -> SetX
  axiom F_is_monotone is
     fa(x:D) monotone (F x)

  (* This axiom asserts that any fixpoint that includes the initial set
  also solves the specified problem (not necessarily a least fixpoint).  *)
  axiom fixpoint_solves_the_problem is
     fa(x:D, s:SetX) (F x s = s) && initialSet(x) subset s => O(x,extract s)
  
end

(*  
  The scheme below is functional despite the nondeterministic choice
  in the select operator.  We need to expose the components of the
  algorithm to facilitate optimizations and DTRs.  Effectively it is
  an expression of a chaotic fixpoint operator. 

  After simplification, the first, obvious derivational step is to
  form the workset by finite differencing the expression (F x S) -- S.
  *)

FixpointIterationWorksetAlgorithm =
spec
  import FixpointIterationWorksetTheory
  import translate ../Math/fixpoint by {A +-> SetX, <= +-> subset}

  op select: SetX -> Option X
  def nextSet(elt:X, S:SetX):SetX = set_insert_new(elt,S)

  def f(x:D):R =
    extract(FI_loop(x, initialSet(x)))

  def FI_loop (x:D, S:SetX): SetX =
    case select( (F x S) -- S ) of
      |  None     -> S
      |  Some elt -> FI_loop(x, nextSet(elt,S))   

  theorem correctness is
   fa(x:D,z:R)( f(x)=z => O(x,z) )

end

(*  References

Dusko Pavlovic, Peter Pepper, Douglas R. Smith, Colimits for Concurrent
Collectors, in {\em Verification: Theory and Practice: Festschrift for Zohar
Manna}, N. Dershowitz (Ed.), Springer-Verlag LNCS 2772, 2003, 568--597.

Dusko Pavlovic, Peter Pepper, and Doug Smith, Formal Derivation of Concurrent
Garbage Collectors, in Mathematics of Program Construction 2010 (MPC10),
Springer LNCS 6120, July 2010, 353-376 (long version at
http://arxiv.org/abs/1006.4342).

*)

(*  Refinement morphism in Algorithm Taxonomy

morphism ../../AlgorithmTheories/LocalSearchTheory -> FixpointIterationWorksetTheory
     {D            +-> D,
      R            +-> SetX, 
      O            +-> O,
      State        +-> State,
      InitialState +-> initialSet,
      NextState    +-> F,
      Extract      +-> extract
     }

*)

(*  template for classification morphism

morphism ../../AlgorithmTheories/FIW_classical#FixpointIterationWorksetTheory -> problem domain
     {D          +-> ,
      R          +-> , 
      O          +-> ,
      f          +-> ,
      X          +-> ,
%      SetX       +-> NodeSet,
      initialSet +-> ,
      extract    +-> ,
      F          +->
     }

*)
