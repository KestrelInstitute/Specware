(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*   

     Algorithm Theory for State-Based Small-Step/Chaotic Fixpoint Iteration

     This spec formalizes the small-step Tarski/Kleene fixpoint
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

  Issues
   - select is arb of a set: can't implement as function

*)

SBFixpointIterationWorksetTheory = 
spec
  import translate ../Math/PartialOrder#MonotoneFn by {A +-> State, <= +-> stle, monotone +-> monotoneState}

  type X   % type of increments to workset;   but it's odd to put it here ...

  import ProblemTheory#DROfTotal
  import ../DataStructures/Collections

  op delta: State*State -> Collection X  
  op nextState: State -> X -> State   %(elt:X, S:State):State

  op initialState: D -> State
  op select: State -> Option X
  op extract : State -> R

  op F : State -> State
  axiom F_is_monotone is
      monotoneState F

  axiom SBFIWT_correctness is 
    fa(x:D, y:State, z:R)( F(initialState(x)) = y         % a fixpoint y
                           && initialState(x) stle y      % that is above an initial PO element
                           => O(x, extract(y)))           % solves the problem instance

%   fa(x:D, z:R)  O(x, extract(lfp(initialState(x),
%                                  F (Fparam(initialState(x))) (initialState(x))
%                                  ))))

end

SBFixpointIterationWorksetAlgorithm =
spec
  import SBFixpointIterationWorksetTheory

  def f (x:D):R =
    let y:State = f_loop(initialState(x)) in
    extract(y)

  def f_loop (st:State):State =
    case select st of
      |  None -> st
      |  Some elt -> f_loop(nextState st elt)   

%  axiom correctness0 is
%   fa(x:D,z:R)( f(x)= extract(lfp(initialState(x),(F (initialI(x))))) )

  axiom correctness1 is
   fa(x:D,z:R)( f(x)=z => O(x,z) )

end


(*  template for classification morphism

morphism ../../AlgorithmTheories/FIW_coalgebraic#FixpointIterationWorksetAlgorithm -> problem domain
     {D            +-> ,
      R            +-> , 
      O            +-> ,
      f            +-> ,
      State        +-> ,
      stle         +-> ,
      initialState +-> ,
      select       +-> ,
      extract      +-> ,
      X            +-> ,
      delta        +-> ,
      nextState    +-> ,
     monotoneState +-> ,
      F            +-> 
     }

*)
