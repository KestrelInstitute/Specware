(*   

     Algorithm Theory for State-Based Small-Step/Chaotic Fixpoint Iteration

     This spec formalizes the small-step Tarski/Kleene fixpoint
     iteration, instantiated to the powerset lattice (Bag X).

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

  Notes
   - This theory assumes that the iteration is on Set X, with subset as partial order
   - note that select is arb of a collection, but it's a function because it depends on State
   - The alg thy introduces the "workset" as a State observer, but cannot provide coinductive
     axioms for the effect of the observation on all transformers until the alg thy is applied
     to a concrete problem - this is the job for FD: to derive those axioms.
   - The import of a partial order State: is this just PO-Local Search?

*) 

SBFixpointIterationWorksetTheory = 
spec
  import translate ProblemTheory#DROfTotal by {D +-> State}
  import ../DataStructures/StructuredTypes

  import translate ../Math/PartialOrder by {A +-> State, <= +-> stle, monotone +-> monotoneState}
  axiom def_of_stle is
     fa(st1:State, st2:State) ( stle(st1,st2) = ((obs st1) subset (obs st2)) )

  type X   % the type of increments to workset
  op obs: State -> Set X  

  op nextState(st:State)(x:X):{st':State | obs st' = set_insert(x, obs(st))}
  op extract : State -> R

  op F : State -> Set X -> Set X
  axiom F_is_monotone is 
     fa(st:State,s1:Set X, s2:Set X) s1 subset s2 => (F st s1) subset (F st s2)


end

foo = morphism SBFixpointIterationWorksetTheory -> SBFixpointIterationWorksetAlgorithm {}

SBFixpointIterationWorksetAlgorithm =
spec
  import SBFixpointIterationWorksetTheory

  op WS(st:State): Set X = (F st (obs st)) -- (obs st) 
  axiom WS_invariant_uniq is
     fa (st:State)(WS st = (F st (obs st)) -- (obs st))

  op initialState(st:State): {st':State | WS st' = F st empty_set}

% "nondeterministic" select from WS
  op selectWS (st:State):{(st',ox):State*Option(X) | 
                            if (WS st) = empty_set
                            then WS st' = WS st 
                                 &&  ox = None
                            else ex(y:X)(y in? WS st 
                                         && WS st' = set_delete(y, WS st)
                                         &&     ox = Some y )}

  op f(x:State|pre(x)):{z:R|post(x,z)} =
    let y:State = f_iterate(initialState(x)) in
    extract(y)

  op f_iterate (st:State):State =
    case selectWS st of
      | (st',None) -> st'      % convergence when WorkSet is empty
      | (st',Some y) -> f_iterate(nextState st' y)   

  theorem correctness1 is
   fa(x:State,z:R)( f(x)=z => O(x,z) )

%  axiom SBFIWT_correctness is 
%    fa(x:State, st:State, z:R)( B2S(F st (obs st)) = (obs st)  % (obs st) is a fixpoint
%                           && initialState(x) stle st          % that is above an initial PO element
%                           => O(x, extract(st)))               % solves the problem instance

end


(*  template for classification morphism

morphism ../../AlgorithmTheories/SBFIW#FixpointIterationWorksetAlgorithm -> problem domain
     {D            +-> ,
      pre          +->
      post         +->
      R            +-> , 
      O            +-> ,
      f            +-> ,
      State        +-> ,
      stle         +-> ,
     monotoneState +-> ,
      X            +-> ,
      obs          +-> ,
      initialState +-> ,
      nextState    +-> ,
      extract      +-> ,
      F            +->  
     }

*)
