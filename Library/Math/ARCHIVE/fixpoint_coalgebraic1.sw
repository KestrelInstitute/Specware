(*                 
                      State-Based Fixpoint Iterators

  This specification introduces notation for State-Based Fixpoints of
  a monotone endofunction.  The spec refines the state by adding a new
  observation of a partial order.  The iterators evolve the state to a
  least/greatest fixpoint of the new observation.

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
  import PartialOrder
  type State
  op st2po: State -> A      % new observer of the the state

  op sblfp :  State -> {F:State->State | fa(st:State) monotone (st2po F))} -> State
  def sblfp st0 F = 
       the (stn)( fa(a0,an,a)
                    (   a0 = st2po st0
                     && an = st2po stn
                     => (a0<=a)      %  simpler:  lfp a0 F = an
                     && F stn an =an 
                     && (fa(a:A)(a0<=a && (F stn a)=a => an<=a))))

%  op sbgfp :  State -> {f:A->A | monotone f} -> State 
%  axiom gfp_characterization is
%     fa(a,f,b)(gfp a f = b => (b<=a && f(b)=b & (fa(c:State)(c<=a && f(c)=c => c<=b))))

end
