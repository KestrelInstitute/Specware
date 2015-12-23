(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*

		    State-Based Problem Theories
                     Dynamical System Theories


In algebraic problems, we specify an input/output relation and we desire a
functional realization of the input/output relation (aka uniformization).  In
coalgebraic problems, we specify a state transformer, possibly with an output.

Note how SSP combines both the "spec" (pre/post) and the "solver" p.

Another consideration is whether the input and/or output is an observer.
The state-input must be initialized by the caller of p.
The state-output observer (e.g. the iteration variable in a fixpoint)
must be extracted by the caller.

That is, we can distinguish between the input/output being locals (as in Mealy,
Moore) versus globals (as is implicitly in SSP).

Global input/output is appropriate for Garbage Collection which operates on a
shared heap.

For most CSP it seems appropriate to use Moore, so the input and output is
local.  However, the use of definite constraints (Rehof-Mogensen) for constraint
propagation requires an ongoing usage of the constraint set and ongoing
iteration of the current partial solution, so a SSP spec seems appropriate.

*)

SSP = spec
 type State
 axiom StateInhabited is ex(st: State) true
 op pre  : State -> Bool
 op post : State -> State -> Bool
 op p (st:State | pre st): {st':State | post st st'}
end-spec

Mealy = spec
 type State
 axiom StateInhabited is ex(st: State) true
 type In
 op pre  : State -> Bool
 op post : State -> In -> State -> Bool
 op p (st:State | pre st)(i:In): {st':State | post st i st'}
end-spec

Moore = spec
 type State
 axiom StateInhabited is ex(st: State) true
 type In
 type Out
 op pre  : State -> Bool
 op post : State -> In -> Out -> State -> Bool
 op p (st:State | pre st)(i:In): {(o,st'):Out*State | post st i o st'}
end-spec

