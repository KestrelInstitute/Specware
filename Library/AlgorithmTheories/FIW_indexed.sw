(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*   

     Algorithm Theory for Indexed Workset-Based Chaotic Fixpoint Iteration Theory

     Conceptually this spec can be viewed as the instantiation of
     (large-step) Tarski/Kleene fixpoint iteration to the powerset
     lattice (Set X), which is then refines to

       (1) the fine-grain (small-step) scheme 
       (2) introduce a workset as f(S)\S (which sets up the FD opportunity)

            D ----- O ------> R
            |                 ^
            |                 |
       initialSet          extract
            |                 |
            v                 |
            S0 - lfp(S0,F) -> Sn

   The crux of the algorithm theory: the problem is solved by a
   fixpoint of F above a given element of the partial order.  Then, we
   can use an appropriate iterator (lfp here) to compute a least
   fixpoint as an algorithm solution.

   Because the partial order is finite we have immediately that it is
   complete, therefore the lfp is well-defined.

  To apply this algorithm theory, we need to construct a classification morphism
      FixpointIterationWorksetTheory -> Problem Domain  (see below)
  and then compute the pushout with FixpointIterationWorksetAlgorithm.   

*)

IndexedFixpointIterationWorksetTheory = 
spec
  import ProblemTheory#DROfTotal
  import ../DataStructures/Sets
  type X
  type SetX = Set X
  type I
  import translate ../Math/PartialOrder#MonotoneFn by {A +-> SetX, <= +-> subset}

  op getI: D -> I
  op initialSet: D -> Set X
  op extract : Set X -> R
  op F : I -> Set X -> Set X
  axiom F_is_monotone is
     fa(i:I) monotone (F i)

  axiom FIT_correctness is 
    fa(x:D, y:Set X, z:R)( (F (getI x) y)=y           % a fixpoint y,
                          && initialSet(x) subset y   % that is above an initial PO element,
                          => O(x, extract(y)))        % solves the problem instance
  
end

(*  
  The scheme below is functional despite the nondeterministic choice
  in the select operator.  We need to expose the components of the
  algorithm to facilitate optimizations and DTRs.  Effectively it is
  an expression of a chaotic fixpoint operator.  
*)

IndexedFixpointIterationWorksetAlgorithm =
spec
  import IndexedFixpointIterationWorksetTheory
  import translate ../Math/fixpoint by {A +-> SetX, <= +-> subset}

  op select: Set X -> Option X
  def nextSet(elt:X, S:Set X):Set X = set_insert_new(elt,S)

  def f(x:D):R =
    let y:Set X = FI_loop(x, initialSet(x)) in
    extract(y)

  def FI_loop (x:D, S:Set X): Set X =
    case select( (F (getI x) S) -- S ) of
      |  None -> S
      |  Some elt -> FI_loop(x, nextSet(elt,S))   

  theorem correctness0 is
   fa(x:D,z:R)(f(x)= extract(lfp(initialSet(x), (F (getI x)) )))

  theorem correctness1 is
   fa(x:D,z:R)( f(x)=z => O(x,z) )

end

(*  template for classification morphism

morphism ../../AlgorithmTheories/FIW_indexed#IndexedFixpointIterationWorksetAlgorithm -> problem domain
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
