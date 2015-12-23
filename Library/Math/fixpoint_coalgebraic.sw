(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*                 
             State-Based/Coalgebraic Fixpoint Iterators

  This specification introduces notation for State-Based Fixpoints of
  a monotone state transformer.  The spec refines the state by adding
  a new observation of a partial order (Set X).  The iterator evolves
  the state to a least/greatest fixpoint of the new observation.

  See also the notes on iterators in fixpoint.sw

  issues: sblfp should leave the state unchanged except for the st2po
  value?  but if the state has complex invariants, the the iteration
  must make necessary/minimal updates to state to preserve them.  For
  GC, the problem is to compute the reachability set of live nodes
  from the roots; there are no invariant that entangle the live nodes
  with the underlying state, so the rest of the state remains fixed
  (in a stw collector).  The point of using a coalgebraic spec is to
  force single-threadedness on the iteration and
  state-changing/side-effecting updates.

  Are the intermediate states along the iteration visible?  i.e. so
  that invariant properties must be maintained?

*)

spec 
  import ../DataStructures/Sets
%  type State
%  op stle infixl 20: State * State -> Boolean
  import translate PartialOrder#MonotoneFn by {A +-> State, <= +-> stle, monotone +-> monotoneState}

(* In this iterator, F is a state transformer that is monotone wrt stle.  *)

  op sblfp (st0:State, F:State->State | monotoneState F && st0 stle F(st0)): State =
     the (stn)( st0 stle stn      %  simpler:  lfp(st0,F) = stn
                 && F(stn)=stn 
                 && (fa(st:State)(st0 stle st && F(st)=st => stn stle st)))

end


(*  For now, we don't specify further how the state transformer is monotone
  type X
  type SetX = Set X
  op st2po: State -> Set X     % introduce new observer of the the state
  def stle(st0,st1) = (st2po st0) subset (st2po st1)   

  op sblfp (a:State, F:State->State | monotone F && a stle F(a)): State =
     the (stn)( fa(a0,an,a)
                  ( a0 = st2po st0
                    && an = st2po stn
                    => (a0 subset a)      %  simpler:  lfp a0 F = an
                    && F(stn)=stn 
                    && (fa(st:State)(st0 stle st && F(st)=st => stn stle st))))

*)
