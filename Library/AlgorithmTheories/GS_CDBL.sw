(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*

   Algorithm Theory for Global Search with Conflict-Directed Backjumping and
   Learning applied to Constraint Satisfaction Problems (with constraints given
   at runtime)

   State is introduced to package up local state of the solver, including the
   stack of subspaces and alternatives

   CDBL theory should be parametric on an overapproximating abstract domain for
   search and propagation.  The concrete domain is fixed as (Set Valuation). 
   Not clear if an underapproximating GC is needed for conflict analysis (ala
   DHK).

  This spec is intended for abstract proof of correctness of the algorithm theory.

*)


GS_CDBL_Theory = spec
  import ProblemTheoryC#CSP,          % constraint satisfaction problem thy 
         GS_Galois_Connection,        % Rhat: parametric abstract domain for search&propagate
         /Library/DataStructures/StructuredTypes   % using Specware library
%%         ../Library/StructuredTypes   % using CW library

  type State      % problem-solving state
  axiom StateInhabited is ex(st: State) true
  type InferenceStack
  type RefinementReason   % sum type 

  op input             : State -> D
  op constraints       : State -> Set Constraint   % dynamic set of constraints
  op currentDepth      : State -> Nat
  op currentRhat       : State -> Rhat
  op currentInferences : State -> InferenceStack
  op bindingDepth      : State -> Map(Variable, Nat)
  op stk               : State -> Map(Nat, Rhat*InferenceStack) % for explicit backjumping

  op initialVariables   : D -> Set Variable

  (* phi is a pruning test.  It is a necessary condition on existence
    of a feasible solution in the current subspace. For CSPs in which 
    constraints are given as input data, this test is simply that no constraint
    fails under the current partial assignment.                               
    op phi(x:D)(rhat:Rhat):
          {b:Bool | fa(z:R)(z in? (concretize rhat) && (O x z) => b)}        
    or    {b:Bool | fa(z:R)(RefinesTo(rhat,beta z) && (O x z) => b)}     *)

   op phi : D*Rhat -> Bool
   axiom characterization_of_necessary_pruning_test_phi is
     fa(x:D,z:R,st:State)(z in? (concretize (currentRhat st)) && (O x z) 
                            => phi (input st,currentRhat st))

  (* psi is a monotone function on spaces that adds necessary constraints to the
  current space.  By construction it preserves all feasible solutions.  This
  spec for psi is equivalent to the Abstract Interpretation characterization of
  a sound abstract operator (for the concrete operator that filters for models).
  Monotonicity allows us to iterate it to a fixpoint.  We can generate psi by a
  standard procedure to formulate and simplify arc-consistency variants of each
  constraint, yielding a definite constraint system (cf Rehof-Mogenson). *)

  op psi : Rhat -> Rhat   	 % necessary propagator
  op [a] monotone? (f:a->a, le:a*a->Bool):Bool  % needs axiom, not def

  axiom characterization_of_necessary_propagator_psi is   % i.e. soundness of inference
    monotone?(psi, RefinesTo) &&
    (fa(x:D,r:Rhat,z:R)(z in? (concretize r) && (O x z) => (z in? concretize (psi r))))

  (* xi is a monotone function that generates a consistent refinement of a
  space. By construction it preserves the existence of feasible solutions.*)

  op xi : Rhat -> Rhat	 % consistent refinement
  axiom characterization_of_consistent_refinement_xi is
    monotone?(xi, RefinesTo) &&
    (fa(x:D,r:Rhat) (ex(z:R)(z in? (concretize r)      && (O x z)) 
                  = (ex(z:R)(z in? (concretize (xi r)) && (O x z)))))
 
 end-spec


(********************************   GS Scheme with CDBL   ****************************

  Propagate computes a refinement of the current space by iterating psi and xi
  to a (least) fixpoint.  the properties of psi and xi are preserved under
  iteration.  at each iteration, propagate applies phi to test for emptiness.
  key enablers are that psi and xi are monotone functions of rhat, and phi is
  antitone.  *)

GS_CDBL = spec 
  import GS_CDBL_Theory

  op InitialState(x:D):{st:State | 
                          input st = x
                          && constraints st = initialConstraints x
                          % && currentRhat st = RhatBot   needs to be a fn of x
                          && currentDepth st = 0
                          && currentInferences st = empty_stack
                          && stk st = empty_map}

  type PropagateFailInfo = Constraint
  type PropagateResult  = | Ok State | Fail State*PropagateFailInfo

(* Propagate iterates abstract operators psi and xi until either 
  (Ok case) a fixpoint it reached, or 
  (Fail case) we have that the current partial assignment (rhat) does not 
              satisfy some constraint.  
  Missing: how to specify that the inference stack records the
           propagation inferences made... 
  Design Tactic:  Apply Definite Constraint Solver tactic to synthesize this spec.
*)

  op Propagate (st:State | phi (input st,currentRhat st))
                       : {pr:PropagateResult |
                               (case pr of
                                  | Ok st' -> RefinesTo(currentRhat st, currentRhat st')
                                              && input st' = input st
                                              && currentDepth st' = currentDepth st 
                                              && psi(currentRhat st') = currentRhat st'
                                              &&  xi(currentRhat st') = currentRhat st'
                                              && phi(input st, currentRhat st')
                                  | Fail (st',cc) ->  
                                              RefinesTo(currentRhat st, currentRhat st')
                                              && input st' = input st
                                              && currentDepth st' = currentDepth st 
                                              && ~(phi(input st',currentRhat st'))
                                              && cc in? constraints st' 
                                              && ~(satisfiesRhat (currentRhat st') cc)
                                              )
                              }

  (* Attempt to extract a feasible solution from rhat and return it as the
     answer.  Otherwise, analyze the reason for the failure of extract
     (typically as a disjunction) and use it to pick a disjunct from the
     alternatives and refine currentRhat by enforcing the disjunct. If there is
     no feasible refinement of rhat then prune it (i.e. fail).   *)

  type AFCResult = | Answer R | Extrapolate ExtrapolateInfo | Fail Constraint

  op AnalyzeForCompleteness(st:State | phi (input st,currentRhat st)):
       {er:AFCResult | let rhat = (currentRhat st) in
                       case er of
                         | Answer z -> (O (input st) z)
                         | Extrapolate (vr,vl) -> 
                                   RefinesTo(rhat, RhatJoin(rhat,beta (singletonMap vr vl)))
                                   && phi((input st),RhatJoin(rhat,beta (singletonMap vr vl)))
                         | Fail lc -> (fa(shat)(RefinesTo(rhat,shat) => ~(phi(input st,shat))))
                                      && ~(satisfiesRhat rhat lc)
                                      && (entailsCs (constraints st) lc)}

  type ExtrapolateInfo = Variable*Value
  op incorporateE(rhat:Rhat)((vr,vl):ExtrapolateInfo): Rhat 
          = RhatJoin(rhat, beta(singletonMap vr vl))

  type Inference = {assignee:Variable, depth:Nat, reason:RefinementReason}
  type InferenceStack = Stack Inference

  op EnforceE(st :State)((vr,vl):ExtrapolateInfo)
            :{st':State | currentRhat st' = incorporateE (currentRhat st) (vr,vl)
                       && currentDepth st' = (currentDepth st) + 1
                       && currentInferences st' = empty_stack
                       && bindingDepth st' = update (bindingDepth st) vr (1 + currentDepth st)
                       && stk st' = (update (stk st) (currentDepth st) 
                                           (currentRhat st, currentInferences st))}

(* Analyze the reason for the failure of the current partial solution; return a
   new constraint and backjump depth if there is a depth at which a proper
   propagation refinement can occur (satisfying phi), else return None
   signifying unsatisfiability (i.e. false is a consequence of the current
   constraints).

   The learned constraint satisfies: (1) it is a consequence of the current
   constraints, (2) it fails the conflict constraint, and (3) it allows
   propagation inference at an earlier depth.  The backjump depth bjd should be
   the least depth at which a propagation step could be made (although more
   generally, it should be the least depth at which the search would take a
   different direction than if the lc were not learned; e.g. if a heuristic
   would make a different choice.  This is effectively restarting.
*)

  op satisfiesRhat(rhat:Rhat)(c:Constraint):Bool % abstractSatisfies?
  axiom satisfiesRhat_def is
      fa(rhat:Rhat,c:Constraint) ex(z:Valuation)(z in? (concretize rhat) && (satisfiesC c z))

  type ConflictConstraint = Constraint
  op refinable(st:State)(pc:ConflictConstraint)(bjd:Nat):Bool

  op AnalyzeConflict(st:State)
                    (cc:PropagateFailInfo | cc in? constraints st 
                                          && ~(satisfiesRhat(currentRhat st) cc)):
           {opcc:Option (ConflictConstraint*Nat) 
             | case opcc of 
                | Some (lc,bjd) -> (entailsCs (constraints st) lc)
                                   && ~(satisfiesRhat(currentRhat st) lc)
                                   && (refinable st lc bjd)
                | None         -> ~(ex(lc:ConflictConstraint,d:Nat)(refinable st lc d))}

  op EnforceC(st :State)(bjd:Nat)(lc:ConflictConstraint | ~(lc in? (constraints st))): 
             {st':State | currentDepth st' = bjd
                       && constraints  st' = set_insert_new(lc, constraints st)
                       && currentRhat  st' = (TMApply(stk st, bjd)).1
                       && currentInferences st' = (TMApply(stk st, bjd)).2
                       && bindingDepth st' = bindingDepth st
              } 

  op feasible(x:D)(ov: Option R): Bool =
       case ov of
         | None -> ~(ex(z)(O x z))
         | Some z -> (O x z) 

  def f (x:D): {ov: Option R | feasible x ov } =  % was CDBL_Solve
      let is = InitialState x in
      if phi(x, currentRhat is) then (GS is) else None

  type PEResult  = | Answer R | Fail (State*PropagateFailInfo)
  op PropagateExtrapolate(st:State | phi (input st,currentRhat st)): 
    {per:PEResult | case per of
                       | Answer z       -> (O (input st) z)
                       | Fail (st',cc)  -> RefinesTo(currentRhat st, currentRhat st')
                                           && input st' = input st
                                           && currentDepth st' >= currentDepth st 
                                           % && psi(currentRhat st') = currentRhat st'
                                           % &&  xi(currentRhat st') = currentRhat st'
                                           && ~(phi (input st', currentRhat st'))
                                           && (entailsCs (constraints st) cc)
                                           && ~(satisfiesRhat (currentRhat st') cc)}
     = case Propagate st of
        | Ok st1 -> (case AnalyzeForCompleteness st1 of % can we extract a (relaxed) solution?
                       | Answer z -> Answer z           % if so, we're done
                       | Extrapolate (vr,vl) -> let st2 = EnforceE st1 (vr,vl) in
                                                PropagateExtrapolate st2
                       | Fail cc -> Fail (st1,cc))
        | Fail stcc -> Fail stcc     % returns a named pair: (st',cc)

  def GS (st:State | phi (input st,currentRhat st) ): 
         {ov:Option R | feasible (input st) ov } = 
    case PropagateExtrapolate st of                         % propagate in current stack frame
      | Answer z ->  Some z                                 % if so, we're done
      | Fail (st1, cc) ->                                   % propagation fails on constraint c
         (case AnalyzeConflict st1 cc of                    % analyze reason for failure
          | Some (lc,bjd) -> GS (EnforceC st1 bjd lc)       % learn lc and backjump to bjd
          | None         -> None)                           % no solutions

end-spec
