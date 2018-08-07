(*

     Algorithm Theory for State-Based Small-Step Fixpoint Iteration

     This spec formalizes the small-step Kleene fixpoint iteration,
     instantiated to the powerset lattice.

     The crux of the algorithm theory : the problem is solved by a
     fixpoint of F above a given element of the partial order.  Then,
     we can use an appropriate iterator to compute a least fixpoint as
     an algorithm solution.

     To apply this algorithm theory, we need to construct a classification
     morphism SBFixpointIterationTheory -> Problem Domain (see pattern below)
     and then compute the pushout with SBFixpointIterationAlgorithm.

  Notes
   - This theory assumes that the iteration is on Set X, with subset as partial order

   - The alg thy introduces the "workset" as a State observer, but cannot
     provide coinductive axioms for the effect of the observation on all
     transformers until the alg thy is applied to a concrete problem - this is
     the job for FD: to derive those axioms.

   - workset as phased invariant: this spec treats the workset as an invariant
     to be maintained only while p is executing.  E.g. in garbage collection, we
     don't want the collector or the mutator to maintain the workset when the
     collector is either idle or in its sweep phase

*)

SBFixpointIterationWorksetTheory =
spec
  import /Library/DataStructures/StructuredTypes

% we have a dynamical problem over a partially ordered state space
  import SBPT#SSP
  op obs: State -> Set X
  type X   % the type of increments to workset
  op F : State -> Set X -> Set X
  axiom F_is_monotone is
     fa(st:State,s1:Set X, s2:Set X) s1 subset s2 => (F st s1) subset (F st s2)

  op nextState0(st:State)(x:X):{st':State | obs st' = set_insert(x, obs(st))}
end-spec


SBFixpointIterationWorksetAlgorithm =
spec
  import SBFixpointIterationWorksetTheory

proof Isa -defaultProof
sorry
end-proof

% observer flag to reify the execution phase of p
 op p? : State -> Bool
 type P_State  = {S: State |   p? S}
 type NP_State = {S: State | ~(p? S)}

 op startp (st:NP_State) :{st':State | p? st'}
 op finishp (st:P_State) :{st':State | ~(p? st')}

 op WS(st:State): Set X = if p? st then (F st (obs st)) -- (obs st) else empty_set
    % (F st (obs st)) -- (obs st)

% initialState is obviated by startp
% op initialState(st:P_State | p? st): {st':P_State | WS st' = F st empty_set}

  op nextState(st:P_State)(x:X| ~(x in? WS st))
            :{st':P_State | obs st' = set_insert(x, obs(st))}
     = nextState0 st x

% "nondeterministic" select from WS
  op selectWS (st:P_State):{(st',ox): P_State * Option(X) |
                            if WS st = empty_set
                            then WS st' = WS st
                                 &&  ox = None
                            else ex(y:X)(y in? WS st
                                         && WS st' = set_delete(y, WS st)
                                         && ox = Some y)}

  def p (st:State | pre st):
       {st':State | post st st'
                    && (WS st') = empty_set
                    && (F st' (obs st')) = (obs st')
                    } =
    let st1: P_State = startp st in
    let st2: P_State = f_iterate st1 in
    finishp st2

  op f_iterate (st: P_State): P_State =
    case selectWS st of
      | (st',None) -> st'      % convergence when WorkSet is empty
      | (st',Some y) -> let st'' = nextState st' y in
                        f_iterate st''

  theorem correctness_of_p is
    fa (st:State,st':State)(pre st
                              && st' = p st
                              => post st st')

proof Isa f_iterate ()
by auto
(* f_iterate is non-terminating *)
termination sorry
end-proof

end-spec



(*  A variant that does not set a flag during the iteration.
    This is useful when we do not need phase-dependent invariants.
*)

SBFIW_nophase_Algorithm =
spec
  import SBFixpointIterationWorksetTheory

 op WS(st:State): Set X = (F st (obs st)) -- (obs st)

 op initialState(st:State): {st':State | WS st' = F st empty_set}

  op nextState(st:State)(x:X):{st':State | obs st' = set_insert(x, obs(st))}
     = nextState0 st x

% "nondeterministic" select from WS
  op selectWS (st:State):{(st',ox): State * Option(X) |
                            if WS st = empty_set
                            then WS st' = WS st
                                 &&  ox = None
                            else ex(y:X)(y in? WS st
                                         && WS st' = set_delete(y, WS st)
                                         && ox = Some y)}

  def p (st:State | pre st):
       {st':State | (WS st') = empty_set
                    && (F st' (obs st')) = (obs st')} =
     let st1 = initialState st in   % is this needed?
     f_iterate st1

  op f_iterate (st: State): State =
    case selectWS st of
      | (st',None) -> st'      % convergence when WorkSet is empty
      | (st',Some y) -> let st'' = nextState st' y in
                        f_iterate st''

  theorem correctness_of_p is
    fa (st:State,st':State)(pre st
                              && st' = p st
                              => post st st')
end-spec  % SBFIW_nophase_Algorithm


(*  template for classification morphism

morphism SBFIW#FixpointIterationWorksetAlgorithm -> problem domain
     {pre          +-> ,
      post         +-> ,
      p            +-> ,
      State        +-> ,
%      stle         +-> ,
%     monotoneState +-> ,
      X            +-> ,
      obs          +-> ,
%     initialState +-> ,
      nextState    +-> ,
      extract      +-> ,
      F            +->
     }

*)

(* ========================================================================

   Coalgebraic, Small-step Fixpoint Iteration Theory over a Semilattice

   The algorithm iterates towards the lfp of the state-based function F
   over the semilattice SL.
   The workset is a set of increment descriptors (of type X) where the
   increments are generated by the Delta function where
         (Delta p q = {})  iff p <= q
   The increments are applied to a semilattice element p by
         (p <= increment p x)  where (x in? WS st)
*)

CSSFITSTheory =
spec
  import /Library/DataStructures/StructuredTypes

% we have a dynamical problem over a partially ordered state space;
% here the input value is ...
% and currentElt observes the evolving output value
  import /Library/AlgorithmTheories/SBPT#SSP

  import translate /Library/Math/Semilattice#BoundedJoinSemilattice
         by {A    +-> SL,
             <=   +-> SLle,
             join +-> SLjoin,
             bot  +-> SLbot}

  op currentElt: State -> SL                     % observe the current semilattice elt

  op F : State -> SL -> SL
  axiom F_is_monotone is
     fa(st:State,s1:SL, s2:SL)
       (s1 SLle s2) => (F st s1) SLle (F st s2)

  type X                                     % increment-descriptors in the workset
  op Delta: State -> SL -> SL -> Set X       % generate increment-descriptors
  axiom Delta_characterization is            % typical usage:  Delta st (F st p) p
     fa(st:State,p:SL,q:SL)( ((Delta st p q) = empty_set) => (p SLle q))

  op increment(st:State)(x:X):{st':State |    % increment a semilattice element
                                (currentElt st) SLle (currentElt st')}

  axiom strict_increment_characterization is
     fa(st:State,x:X)
       (x in? (Delta st (F st (currentElt st)) (currentElt st))
        => % p SLlt (increment st p x) &&
       (currentElt (increment st x)) SLle SLjoin(currentElt st, F st (currentElt st)))

end-spec


CSSFITSAlgorithm =
spec
  import CSSFITSTheory

% observer flag to reify the execution phase of p
 op p? : State -> Bool
 type P_State  = {S: State |   p? S}
 type NP_State = {S: State | ~(p? S)}

 op startp (st:NP_State) :{st':State | p? st'}
 op finishp (st:P_State) :{st':State | ~(p? st')}

 op WS(st:State): Set X =
   if p? st
     then Delta st (F st (currentElt st)) (currentElt st)
   else empty_set

% "nondeterministic" select from WS
  op selectWS (st:P_State):{(st',ox): P_State * Option(X) |
                            if WS st = empty_set
                            then WS st' = WS st
                                 &&  ox = None
                            else ex(y:X)(y in? WS st
                                         && WS st' = set_delete(y, WS st)
                                         && ox = Some y)}

  def p (st :State | pre st):
        {st':State | (WS st') = empty_set
                    && (F st' (currentElt st')) = (currentElt st')} =
    let st1: P_State = startp st in
    let st2: P_State = f_iterate st1 in
    finishp st2

  op f_iterate (st: P_State): P_State =
    case selectWS st of
      | (st',None) -> st'      % convergence when WorkSet is empty
      | (st',Some y) -> let st'' = increment st' y in
                        f_iterate st''

  theorem correctness_of_p is
    fa (st:State,st':State)(pre st
                              && st' = p st
                              => post st st')
end-spec
