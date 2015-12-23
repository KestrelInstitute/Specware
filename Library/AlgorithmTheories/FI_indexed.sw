(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*   

     Algorithm Theory for Classical Fixpoint Iteration Theory

    The idea here is to combine problem theory and (large-step)
    Tarski/Kleene fixpoint iteration theory, but specialized to a
    finite powerset lattice:

            D ----- O ------> R
            |                 ^
            |                 |
       initialSet          extract
            |                 |
            v                 |
            S0 -- lfp S0 F -> Sn

   The crux of the algorithm theory: the problem is solved by a
   fixpoint of F above a given element of the partial order.  Then, we
   can use an appropriate iterator (lfp here) to compute a least
   fixpoint as an algorithm solution.

   Because the partial order is finite we have immediately that it is
   complete, therefore the lfp is well-defined.

  To apply this algorithm theory, we need to construct a classification morphism
      FixpointIterationTheory -> Problem Domain  (see below)
  and then compute the pushout with FixpointIterationAlgorithm.   

*)

IndexedFixpointIterationTheory = 
spec
  import ProblemTheory#DROfTotal, ../DataStructures/Sets
  type X
  type SetX = Set X
  type I

  import translate ../Math/PartialOrder#MonotoneFn by {A +-> SetX, <= +-> subset}

  op initialSet: D -> Set X
  op getI: D -> I
  op extract : Set X -> R
  op F : I -> Set X -> Set X
  axiom F_is_monotone is
     fa(i:I) monotone (F i)

  axiom FIT_correctness is 
    fa(x:D, y:Set X, z:R)
      ( (F (getI x) y)=y             % a fixpoint y
         && initialSet(x) subset y   % that is above an initial PO element
         => O(x, extract(y)))        % solves the problem instance

end

% note the distinction between F the monotone function, and f the problem-solver.

IndexedFixpointIterationAlgorithm =
spec
  import IndexedFixpointIterationTheory
  import translate ../Math/fixpoint_indexed by {A +-> SetX, <= +-> subset}

  def f(x:D):R = 
    let y:Set X = (ilfp (getI x) (initialSet x) F) in
    extract(y)

  theorem correctness_of_f is  % follows easily from FIT_correctness
     fa(x:D,z:R)( f(x)=z => O(x,z) )

end


(*  template for classification morphism

morphism ../../AlgorithmTheories/FI_indexed#IndexedFixpointIterationTheory -> problem domain
     {D          +-> ,
      R          +-> , 
      O          +-> ,
      f          +-> ,
      X          +-> ,
%      SetX       +-> ,
      I          +-> ,
      F          +-> , 
      initialSet +-> ,
      initialI   +-> ,
      extract    +-> 
     }

*)
