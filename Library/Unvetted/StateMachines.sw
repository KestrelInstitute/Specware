(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
2005:06:24
AC

This is a spec for a kind of state machines. It also defines state and
transition traces in time, using spec Traces.

Perhaps this spec could be part of a taxonomy of specs for various kind of
state machines.
*)


StateMachine qualifying spec

  (* In this spec, a state machine is a directed graph whose nodes are the
  states and whose edges are the transitions. We define a record type for such
  machines, polymorphic in the types of the states and transitions. The record
  components specify the initial state as well as the source (i.e. old) state
  and target (i.e. new) state of each transition. *)

  type StateMachine(state,transition) =
    {init : state,
     old  : transition -> state,
     new  : transition -> state}

  (* A state machine defines a set of possible transition and state
  traces. Transition traces are discrete (i.e. of type DiscreteTrace), while
  state traces are continuous (i.e. of type ContinuousTrace).

  The machine starts in the initial state, and changes state as transitions
  occur in time, according to the graph of the machine. If transition tr
  occurs at time t, and the machine is in state (old tr) just before t, then
  the machine is in state (new tr) just after t. What state is the machine in
  at time t? We arbitrarily choose the old state.

  For every transition trace defined by the machine, there is a unique state
  trace corresponding to that transition trace. Thus, the op below returns a
  map from transition traces to state traces, as opposed to just a set of
  pairs (transition trace, state trace). *)

  import Traces

  op traces : [state,transition] StateMachine(state,transition) ->
              Map (DiscreteTrace transition, ContinuousTrace state)
  def [state,transition] traces mach = fn trTr -> Some
    (the(stTr)
      % initial state at the beginning of time:
      stTr zero = mach.init
      &&
      % if no transition between t (inclusive) and t1 (exclusive),
      % no state change:
      (fa (t:Time, t1:Time)
        t < t1 && empty? (trTr before t1 notBefore t) =>
        stTr t1 = stTr t)
      &&
      % if tr occurs at t and no other transition occurs before t1,
      % change state:
      (fa (t:Time, t1:Time, tr:transition)
        t < t1 && trTr t = Some tr && empty? (trTr before t1 after t) =>
        mach.old tr = stTr t && mach.new tr = stTr t1))

  % return only transition traces of machine:

  op transitionTraces : [state,transition]
     StateMachine(state,transition) -> Set (DiscreteTrace transition)
  def transitionTraces mach = domain (traces mach)

  % return state trace for given transition trace of machine:

  op stateTrace : [state,transition]
     {(mach,trTr) : StateMachine(state,transition) * DiscreteTrace transition |
      trTr in? transitionTraces mach} -> ContinuousTrace state
  def stateTrace(mach,trTr) = traces mach @ trTr

endspec
