(*
2005:09:02
AC
Notion of interation sequence as a finite sequence of input and output events,
possibly with time separation constraints among them. Interaction sequences
have semantics consisting of predicates over event traces. Interaction
sequences can be used to formalize use cases, and their semantics can be used
to prove that the requirements expressed by the use cases are satisfied by the
spec and/or implementation of a system.

ISSUE:
Some aspects of this spec (e.g. time separation constraints) are amenable to
generalization.

*)


InteractionSequence qualifying spec

  (* This spec formalizes a notion of interaction sequence as a sequence of
  input and output events (the in and out directions are with respect to some
  system of interest). An example is the interaction with a consumer device
  such as a CD player: input events include pushing the various buttons on the
  unit; output events include showing various information on the unit's
  display as well as playing music.

  The sequence of events may include time constraints on the separation
  between events in the sequence. These time constraints have the form of a
  minimum and/or a maximum time that separates events. Details are below.

  This spec attaches semantics to interaction sequences in the form of
  predicates over event traces. The predicate associated to an interaction
  sequence holds over an event trace iff the events in the trace satisfy the
  constraints of the interaction sequence. Details are below. *)

  import /Library/General/FiniteSequences, Traces

  (* This spec is parameterized over the events that comprise the interaction
  sequences (and the traces) and over a predicate that partitions events into
  input and output events. The subspec of this spec that consists of type
  Event and op input? can be instantiated via spec substitution. We could
  factor that subspec into a separate named spec that is imported by this
  spec, but we do not do that because it is very small and so it is not hard
  to write explicitly as "spec type Event op input? : Event -> Boolean
  endspec" when performing spec substitution. *)

  type Event

  op input? : Event -> Boolean

  (* Given events and the partitioning predicate input?, we can define the
  complementary predicate output? as well as subtypes for input and output
  events. *)

  type InputEvent = (Event | input?)

  op output? : Event -> Boolean
  def output? = ~~ input?

  type OutputEvent = (Event | output?)

  (* As mentioned earlier, an interaction sequence may include time
  constraints on the separation between events. A value of the following type
  expresses constraints on the separation between an event ev (to which the
  value if type EventSeparation is associated) and some previous event.

  The value {min = None, max = None} actually expresses no constraint.  If min
  has instead the form (Some (t, i)), it expresses the fact that event ev must
  be separated from the i-th previous event in the interaction sequence by at
  least t. If i is 1, the separation constraint is with respect to the event
  that immediately precedes event ev. Similarly, if max has the form (Some (t,
  i)), it expresses the fact that event ev must be separated from the i-th
  previous event by at most t. The i value of min need not be the same as the
  i value of max: in other words, the record consists of two independent time
  constraints between event ev and some preceding events.

  The kind of time constraints captured by type EventSeparation is not the
  most general possible. For instance, one could imagine multiple min and/or
  max constraints between ev and some preceding events (not just one min and
  one max). This spec is therefore amenable to generalization. *)

  type EventSeparation = {min : Option (Time * PosNat),
                          max : Option (Time * PosNat)}

  (* If an interaction sequence consists of say 10 events, no event separation
  can have say 20 as the value of i for min and/or max. More precisely, if
  event ev is the n-th event in the sequence, it must be the case that i < n,
  otherwise there would be no i-th previous event in the sequence. The
  following auxiliary predicate says whether an event separation constraint is
  valid with respect to a positive natural number n, where n is meant to be
  the total number of events that precede event ev in the interaction
  sequence. *)

  op validEventSeparation? : Nat -> EventSeparation -> Boolean
  def validEventSeparation? n evSep =
    % constraint on min:
    (case evSep.min of
       | Some (_, i) -> i <= n
       | None -> true)  % no constraint if no i
    &&
    % constraint on max:
    (case evSep.max of
       | Some (_, i) -> i <= n
       | None -> true)  % no constraint if no i

  (* Since the events that comprise an interaction sequence are sequentialized
  in time, it is convenient to introduce a type for finite sequences of time
  instants that come one after the other, in the order that they appear in the
  sequence. *)

  type TimeSeq =
    {tS : FSeq Time | fa(i:Nat) i < length tS - 1 => tS@i <= tS@(i+1)}

  (* The following auxiliary predicate holds iff the instant t (at which an
  event ev occurs) satisfies the event separation constraints expressed by
  evSep, with respect to the time instants tS (at which events that precede ev
  occur). *)

  op separatedFrom? : {(t,tS,evSep) : Time * TimeSeq * EventSeparation |
                       validEventSeparation? (length tS) evSep} -> Boolean
  def separatedFrom? (t,tS,evSep) =
    % t must not come earlier than any instant in tS (since the instants in tS
    % are ordered, it is sufficient to test t against the last instant in tS),
    % if any:
    (nonEmpty? tS => t >= last tS)
    &&
    % constraint on min separation:
    (case evSep.min of
       | Some (minSep, i) ->
         let ti:Time = tS @ (length tS - i) in  % ti = i-th previous instant
         t >= ti + minSep
       | None -> true)  % no constraint
    &&
    % constraint on max separation:
    (case evSep.max of
       | Some (maxSep, i) ->
         let ti:Time = tS @ (length tS - i) in  % ti = i-th previous instant
         t <= ti + maxSep
       | None -> true)  % no constraint

  (* The following is the "core" op that formalizes the semantics of an
  interaction sequence. In order to understand it, let us start by explaining
  the semantics of some simple interaction sequences and then moving to more
  complex ones, understanding the general pattern (which is captured by the
  following op).

  Consider a simple interaction sequence consisting of an input event followed
  by an output event. For example, the input event could be the pushing of a
  switch, and the output event could be the turning on of a lamp. The
  interaction sequence may also include separation constraints between the two
  events (expressed by a value of type EventSeparation). The informal meaning
  of this interaction sequence is that if the input event occurs at a time
  instant t1, then the output event must occur at a time instant t2 that
  satisfies the given separation constraints with t1. Formally, we can express
  this as a predicate over event traces. The predicate is true for an event
  trace evTr iff evTr satisfies the following condition: if the input event
  occurs at any instant t1 in evTr, then the output event occurs at some
  instant t2 in evTr that satisfies the separation constraints with t1. In
  this condition, t1 is universally quantified, while t2 is existentially
  quantified. Pseudo-formally:

    fa(t1) (t1, input event) in? evTr =>
           (ex(t2) (t2, output event) in? evTr &&
                   t2 satisfies separation constraints with t1)

  An event trace evTr either satisfies this condition or not. We regard this
  condition as the semantics of the interaction sequence. In other words, the
  semantics of an interaction sequence is a predicate over event traces that
  holds iff the event trace does not violate the interaction sequence. For
  example, an event trace with the input event but without any following
  output event does not satisfy the predicate.

  Now let us consider a slightly more complex interaction sequence, consisting
  of two input events followed by an output event. For instance, the first
  input event could be the lifting of a cover over a switch, the second event
  could be the pushing of the switch, and the output event the turning on of a
  lamp. After a little thought, it should be clear that the condition is now
  the following:

    fa(t1) (t1, first input event) in? evTr =>
           (fa(t2) (t2, second input event) in? evTr &&
                   t2 satisfies separation constraints with t1 =>
                   (ex(t3) (t3, output event) in? evTr &&
                           t3 satisfies separation constraints with t1 and t2))

  Note that the instants t1 and t2 at which both input events occur are
  universally quantified, while the instant t3 at which the output event
  occurs is existentially quantified.

  Let us now consider a symmatric variation of the previous interaction
  sequence, one with an input event followed by two output events. The input
  event could be again the pushing of a switch, the first output event could
  be the turning on of a lamp, and the second output event could be the
  turning off the lamp (e.g. via a timer). After a little thought, it should
  not be hard to realize that the condition is now the following:

    fa(t1) (t1, input event) in? evTr =>
           (ex(t2) (t2, first output event) in? evTr &&
                   t2 satisfies separation constraints with t1 &&
                   (ex(t3) (t3, second output event) in? evTr &&
                           t3 satisfies separation constraints with t1 and t2))

  At this point, the pattern should be clear. The instant of input/output
  events are universally/existentially quantified. The quantifiers have nested
  scopes, so that each instant is in the scope of the subformula of any
  subsequent event. Separation constraints are conjoined to the proposition
  that states the occurrence of an event in evTr. The logical connective
  between an input event and the subsequent events is implication ("if an
  input event occurs, then ..."), while the logical connective between an
  output event and the subsequence events is conjunction ("an output event
  occurs, and ...").

  The following op precisely formalizes this pattern. It takes as arguments a
  time sequence (in which previous events have occurred) and a sequence of
  events with a separation constraint associated to each event (a sequence of
  pairs); it returns a predicate over event traces, expressing the condition
  derived from the events (with separations) with respect to the time instants
  of the preceding events. This op is recursive: it processes the sequence of
  events from left to right. Note the subtype constraint that ensures that the
  separation constraints refer to existing time instants of previous
  events. *)

  op eventTraceConstraintAux :
     {(timesOfPreviousEvents,nextEventsWithSeparations) :
      TimeSeq * FSeq (EventSeparation * Event) |
      fa(i:Nat) i < length nextEventsWithSeparations =>
        validEventSeparation? (length timesOfPreviousEvents + i)
                              (nextEventsWithSeparations @ i).1} ->
     DiscreteTrace Event -> Boolean
  def eventTraceConstraintAux
      (timesOfPreviousEvents, nextEventsWithSeparations) evTr =
    % if no more events, we are done, return true (i.e. no constraint on evTr):
    if empty? nextEventsWithSeparations then true else
    % consider next event with its separation constraints:
    let (evSep, ev) = first nextEventsWithSeparations in
    % construct subformula for input event:
    if input? ev then
      (fa(t:Time)  % universal quantification
         separatedFrom? (t, timesOfPreviousEvents, evSep) &&  % separation
         (t, ev) in? evTr =>  % implication
         eventTraceConstraintAux  % recursively process following events
           (timesOfPreviousEvents <| t, rtail nextEventsWithSeparations) evTr)
    % construct subformula for output event:
    else (* output? ev *)
      (ex(t:Time)  % existential quantification
         separatedFrom? (t, timesOfPreviousEvents, evSep) &&  % separation
         (t, ev) in? evTr &&  % conjunction
         eventTraceConstraintAux  % recursively process following events
           (timesOfPreviousEvents <| t, rtail nextEventsWithSeparations) evTr)

  (* An interaction sequence starts with an input event (a stimulus from the
  outside world to the system under specification) and continues with one or
  more events, the last one of which must be an output event (if it were an
  input event, we would expect the interaction sequence to continue with some
  output event in response to the input event). There are separation
  constraints attached to all events except the first one. *)

  type InteractionSequence =
    {first : InputEvent,
     rest  : {rest : NonEmptyFSeq (EventSeparation * Event) |
              % last event is output event:
              output? (last rest).2 &&
              % all separation constraints refer to existing previous events:
              (fa(i:Nat) i < length rest =>
                 validEventSeparation? (i+1) (rest @ i).1)}}

  (* The following op attaches a semantics, consisting of a predicate over
  event traces, to an interaction sequence. It also takes a boolean condition
  over time instants as an additional argument, useful to restrict the
  predicate over event traces to start at a time instant that satisfies a
  certain conditions. In the above example of the switch and lamp, the
  condition could be that the lamp is off when the first input event
  occurs. *)

  op eventTraceConstraint :
     InteractionSequence -> (Time -> Boolean) -> DiscreteTrace Event -> Boolean
  def eventTraceConstraint intSeq cond evTr =
    fa(t:Time)  % universally quantified because intSeq.first is input event
      % t satisfies the given condition:
      cond t &&
      % first input event occurs at t:
      (t, intSeq.first) in? evTr =>
      % recursively process the events after the first:
      eventTraceConstraintAux (single t, intSeq.rest) evTr

endspec
