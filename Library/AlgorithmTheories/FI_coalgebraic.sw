(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*   

     Algorithm Theory for State-Based Large-Step Fixpoint Iteration

     This spec formalizes the large-step Tarski/Kleene fixpoint
     iteration, instantiated to the powerset lattice (Set X).

            D ------ O -------> R
            |                   ^
            |                   |
       initialState          extract
            |                   |
            v                   |
         State -- sblfp F --> State


   The crux of the algorithm theory: the problem is solved by a
   fixpoint of F above a given element of the partial order.  Then, we
   can use an appropriate iterator (sblfp here) to compute a least
   fixpoint as an algorithm solution.

  To apply this algorithm theory, we need to construct a classification morphism
      SBFixpointIterationTheory -> Problem Domain  (see pattern below)
  and then compute the pushout with SBFixpointIterationAlgorithm.   

*)

SBFixpointIterationTheory = 
spec
  import ProblemTheory#DROfTotal
%  import ../DataStructures/Sets
  import translate ../Math/PartialOrder#MonotoneFn by {A +-> State, <= +-> stle, monotone +-> monotoneState}

  op initialState: D -> State
  op extract : State -> R
  op F : State -> State
  axiom F_is_monotone is
      monotoneState F

  axiom SBFIT_correctness is 
    fa(x:D, y:State, z:R)( F(initialState(x)) = y         % a fixpoint y
                           && initialState(x) stle y      % that is above an initial PO element
                           => O(x, extract(y)))           % solves the problem instance

end

SBFixpointIterationAlgorithm =
spec
  import SBFixpointIterationTheory
  import translate ../Math/fixpoint_coalgebraic by {}

  def f(x:D):R = extract(sblfp(initialState(x),F))

  theorem correctness_of_f is  % follows trivially from SBFIT_correctness
   fa(x:D,z:R)( f(x)=z => O(x,z) )

end

(*  template for classification morphism

morphism ../../AlgorithmTheories/FI_coalgebraic#SBFixpointIterationTheory -> problem domain
     {D            +-> ,
      R            +-> , 
      O            +-> ,
      f            +-> ,
      State        +-> ,
      stle         +-> ,
      initialState +-> ,
      extract      +-> ,
      F            +-> 
     }

*)
