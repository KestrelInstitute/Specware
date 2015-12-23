(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
2005:09:26
AC
Notion of interation sequence as a finite sequence of input and output events,
possibly with time separation constraints among them. Interaction sequences
have semantics consisting of predicates over event traces. Interaction
sequences can be used to formalize use cases, and their semantics can be used
to prove that the requirements expressed by the use cases are satisfied by the
specification and/or implementation of a system.
*)



(* This spec formalizes a notion of interaction sequence as a sequence of
input and output events (the in and out directions are with respect to some
system of interest). An example is the interaction with a consumer device such
as a CD player: input events include pushing the various buttons on the unit;
output events include showing various information on the unit's display as
well as playing music.

The sequence of events may include time constraints on the separation between
events in the sequence. These time constraints have the form of a minimum
and/or a maximum time that separates events. Details are below.

We attache semantics to interaction sequences in the form of predicates over
event traces. The predicate associated to an interaction sequence holds over
an event trace iff the events in the trace satisfy the constraints of the
interaction sequence.

This spec is parameterized over the events that comprise the interaction
sequences (and the traces) and over a predicate that partitions events into
input and output events. In general, a parameterized spec consists of a
parameter spec and a body spec that includes the parameter spec. In this case,
spec param below is the parameter spec and spec body below is the body
spec. *)


param = InteractionSequence qualifying spec
  type Event
  op input? : Event -> Bool  % partitioning predicate
endspec


body = InteractionSequence qualifying spec

  import param,  % includes parameters
         Traces

  (* Given events and the partitioning predicate input?, we can define the
  complementary predicate output? as well as subtypes for input and output
  events. *)

  type InputEvent = (Event | input?)

  op output? : Event -> Bool
  def output? = ~~ input?

  type OutputEvent = (Event | output?)

  (* As mentioned earlier, an interaction sequence may include time
  constraints on the separation between events. A value of the following type
  expresses constraints on the separation between an event ev (to which the
  value if type EventSeparation is associated) and some previous event.

  The value {min = None, max = None} actually expresses no constraint. If min
  has instead the form (Some (t, i)), it expresses the fact that event ev must
  be separated from the i-th previous event in the interaction sequence by at
  least t. If i is 1, the separation constraint is with respect to the event
  that immediately precedes event ev. Similarly, if max has the form (Some (t,
  i)), it expresses the fact that event ev must be separated from the i-th
  previous event by at most t. The i value of min need not be the same as the
  i value of max: in other words, the record consists of two independent time
  constraints between event ev and some preceding events.

  The time separation cannot be null. A null time separation in min would
  effectively pose no constraint, because later events follow earlier
  events. A null time separation in max would pose an impossible constraint,
  because it would constrain the events to be simultaneous.

  The kind of time constraints captured by type EventSeparation is not the
  most general possible. For instance, one could imagine multiple min and/or
  max constraints between ev and some preceding events (not just one min and
  one max). This spec is therefore amenable to generalization. *)

  type EventSeparation = {min : Option ({t : Time | t ~= zero} * PosNat),
                          max : Option ({t : Time | t ~= zero} * PosNat)}

  (* The following ops construct commonly used kinds of event separations. *)

  op anySeparation : EventSeparation
  def anySeparation = {min = None, max = None}

  op minSeparationWith : {t : Time | t ~= zero} -> PosNat -> EventSeparation
  def minSeparationWith t i = {min = Some (t, i), max = None}

  op maxSeparationWith : {t : Time | t ~= zero} -> PosNat -> EventSeparation
  def maxSeparationWith t i = {min = None, max = Some (t, i)}

  op minSeparationWithPrevious : {t : Time | t ~= zero} -> EventSeparation
  def minSeparationWithPrevious t = minSeparationWith t 1

  op maxSeparationWithPrevious : {t : Time | t ~= zero} -> EventSeparation
  def maxSeparationWithPrevious t = maxSeparationWith t 1

  (* If an interaction sequence consists of say 10 events, no event separation
  can have say 20 as the value of i for min and/or max. More precisely, if
  event ev is the n-th event in the sequence, it must be the case that i < n,
  otherwise there would be no i-th previous event in the sequence. The
  following auxiliary predicate says whether an event separation constraint is
  valid with respect to a positive natural number n, where n is meant to be
  the total number of events that precede event ev in the interaction
  sequence. *)

  op validEventSeparation? : Nat -> EventSeparation -> Bool
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

  (* An interaction sequence starts with an input event (a stimulus from the
  outside world to the system under specification) and continues with one or
  more events, the last one of which must be an output event (if it were an
  input event, we would expect the interaction sequence to continue with some
  output event in response to the input event). There are separation
  constraints attached to all events except the first one. *)

  type InteractionSequence =
    {first : InputEvent,
     rest  : {rest : List1 (EventSeparation * Event) |
              % last event is output event:
              output? (last rest).2 &&
              % all separation constraints refer to existing previous events:
              (fa(i:Nat) i < length rest =>
                 validEventSeparation? (i+1) (rest @ i).1)}}

  (* Since the events that comprise an interaction sequence are sequentialized
  in time, it is convenient to introduce a type for finite sequences of
  ordered timed events, where a timed event is a pair consisting of a time
  instant and an event. The instants of the pairs that comprise the sequence
  come one after the other, in the order that they appear in the sequence. *)

  type EventSeq =
    {teS : List1 (Time * Event) |
     fa(i:Nat) i < length teS - 1 => (teS@i).1 < (teS@(i+1)).1}

  (* The following op returns the time of the last event in the sequence. *)

  op timeOfLastEvent : EventSeq -> Time
  def timeOfLastEvent evSeq = (last evSeq).1

  (* The following op returns the time of the last output event in the
  sequence. If there are no output events in the sequence, the op returns the
  time of the first (input) event in the sequence. *)

  op timeOfLastOutputEventOrFirstEvent : EventSeq -> Time
  def timeOfLastOutputEventOrFirstEvent evSeq =
    let outEvSeq = filter (fn te -> output? te.2) evSeq in
    if empty? outEvSeq then (head evSeq).1
    else (last outEvSeq).1

  (* The following auxiliary predicate holds iff the instant t (at which some
  event ev occurs) satisfies the event separation constraints expressed by
  evSep, with respect to the time instants of a given event sequence
  (consisting of the events that precede ev). *)

  op separatedFrom? : {(t,teS,evSep) : Time * EventSeq * EventSeparation |
                       validEventSeparation? (length teS) evSep} -> Bool
  def separatedFrom? (t,teS,evSep) =
    % t must not come earlier than any instant in tS (since the instants in teS
    % are ordered, it is sufficient to test t against the last instant in tS),
    % if any:
    (nonEmpty? teS => t >= (last teS).1)
    &&
    % constraint on min separation:
    (case evSep.min of
       | Some (minSep, i) ->
         let ti:Time = (teS @ (length teS - i)).1 in
           % ti = i-th previous instant
         t >= ti + minSep
       | None -> true)  % no constraint
    &&
    % constraint on max separation:
    (case evSep.max of
       | Some (maxSep, i) ->
         let ti:Time = (teS @ (length teS - i)).1 in
           % ti = i-th previous instant
         t <= ti + maxSep
       | None -> true)  % no constraint

  (* The following predicate says that, in an event trace, no input events
  take place, after a given time t, until an output event occurs. This
  predicate is used, for example, to express the fact that after an input
  event no further input events are supplied to the system, waiting for an
  output event to occur. *)

  op noInputsUntilOutput? : DiscreteTrace Event -> Time -> Bool
  def noInputsUntilOutput? evTr t =
    % for every instant t1 after t:
    (fa(t1:Time) t1 > t &&
    % if no output events take place between t and t1:
        empty? (evTr suchThat output? after t before t1) =>
    % then no input events take place between t and t1:
        empty? (evTr suchThat  input? after t before t1))

  (* The following predicate says that, in an event trace, the input event ev
  occurs at time t1 after t and that no other input event occurs between t and
  t1. This predicate is used to express the fact that only the input events
  explicitly present in an interaction sequence occur, and no others. *)

  op onlyInputAtAfter? :
     DiscreteTrace Event -> InputEvent -> Time -> Time -> Bool
  def onlyInputAtAfter? evTr ev t1 t =
    t1 > t &&
    evTr suchThat input? after t notAfter t1 = single t1 ev

  (* The following predicate says that, in an event trace, the output event ev
  occurs at time t1 after t and that no other output event occurs between t
  and t1. This predicate is used to express the fact that only the output
  events explicitly present in an interaction sequence occur, and no
  others. This is just like the previous predicate, except that it deals with
  output events rather than input events. *)

  op onlyOutputAtAfter? :
     DiscreteTrace Event -> OutputEvent -> Time -> Time -> Bool
  def onlyOutputAtAfter? evTr ev t1 t =
    t1 > t &&
    evTr suchThat output? after t notAfter t1 = single t1 ev

  (* The following ops formalize the semantics of an interaction sequence. In
  order to understand them, let us start by explaining the semantics of some
  simple interaction sequences and then moving to more complex ones,
  understanding the general pattern (which is captured by the following op).

  Consider a simple interaction sequence consisting of an input event followed
  by an output event. For example, the input event could be the pushing of the
  PLAY button on a CD player, and the output event could be the first track of
  a CD that starts playing. The interaction sequence may also include
  separation constraints between the two events (expressed by a value of type
  EventSeparation), e.g. the maximum time that takes for the player to get the
  disc spinning and the laser positioned at the beginning of the first track
  (this maximum time should be about less than a second).

  The informal meaning of this interaction sequence is that if the input event
  occurs at a time instant t1, then the output event must occur at a time
  instant t2 that satisfies the given separation constraints with t1.

  Formally, we can express this as a predicate over event traces. The
  predicate is true for an event trace evTr iff evTr satisfies the following
  condition: if the input event occurs at any instant t1 in evTr, then the
  output event occurs at some instant t2 in evTr that satisfies the separation
  constraints with t1. The predicate rules out event traces where the input
  event occurs at t1 but no output event occurs at any t2 that satisfies the
  separation constraints with t1 (including the case that the output event
  does not occur at all). In the CD player example, it rules out the
  possibility of the CD never playing or playing after, say, 1 hour.

  We may start writing the predicate in this form:

    fn evTr ->
    (fa(t1) (t1, input event) in? evTr =>
            (ex(t2) t2 satisfies separation constraints with t1 &&
                    (t2, output event) in? evTr))

  Note that t1 is universally quantified, while t2 is existentially
  quantified. This reflects the words "any" and "some" used in the sentence
  "if the input event occurs at any instant t1 in evTr, then the output event
  occurs at some instant t2 in evTr that satisfies the separation constraints
  with t1" (this sentence was already written above).

  However, the predicate is not quite right. One problem is that there are no
  constraints on t1. If at time t1 there is no CD inside the player or if a CD
  is already playing, pushing PLAY has no effect; in particular, there will be
  no t2, "close" to t1 (i.e. satisfying the max separation constraint), at
  which the first track starts playing. For the constraints of this
  interaction to apply, it must be the case that at t1 there is a CD inside
  the player and that the player is not already playing a track. The predicate
  as written above is too strong and cannot be satisfied. We weaken it by
  adding conditions on t1:

    fn evTr ->
    (fa(t1) t1 satisfies suitable conditions &&
            (t1, input event) in? evTr =>
            (ex(t2) t2 satisfies separation constraints with t1 &&
                    (t2, output event) in? evTr))

  There is still another problem. If, immediately after pushing PLAY, the user
  pushes the STOP button, the CD player will not have enough time to spin the
  disc and start playing. So, there will be no t2 as required by the
  predicate. Again, the predicate is too strong. We must add the fact that,
  after the input event at t1, we do not provide any additional inputs to the
  system, but we wait for an output event to occur. We use op
  noInputsUntilOutput? defined earlier:

    fn evTr ->
    (fa(t1) t1 satisfies suitable conditions &&
            (t1, input event) in? evTr &&
            noInputsUntilOutput? evTr t1 =>
            (ex(t2) t2 satisfies separation constraints with t1 &&
                    (t2, output event) in? evTr))

  Now the predicate is satisfiable and adequate. However, it can be improved.
  As it stands, it does not prevent additional output events to occur, say,
  before t2. For example, it could allow the CD player to briefly flash some
  random digits on the display before starting playing the first track. We can
  prohibit this behavior by slightly strengthening our predicate, by saying
  that in fact no output event must occur between t1 and t2. We do that by
  means of the predicate onlyOutputAtAfter? defined earlier:

    fn evTr ->
    (fa(t1) t1 satisfies suitable conditions &&
            (t1, input event) in? evTr &&
            noInputsUntilOutput? evTr t1 =>
            (ex(t2) t2 satisfies separation constraints with t1 &&
                    onlyOutputAtAfter? (evTr, output event, t2, t1)))

  Now the predicate for this simple interaction sequence "covers" the whole
  time interval from t1 (when the first event of the sequence occurs) and t2
  (when the last event of the sequence occurs): the input event at t1 is the
  only input event in that interval, and the output event is the only output
  event in that interval.

  An event trace evTr either satisfies the predicate or not. We regard the
  predicate as the semantics of the interaction sequence. In other words, the
  semantics of an interaction sequence is a predicate over event traces that
  holds iff the event trace does not violate the constraints expressed by the
  interaction sequence. For example, an event trace with the input event but
  without any following output event does not satisfy the predicate.

  The predicate does not cover time instants outside of the interval between
  t1 and t2. In particular, the predicate does not prevent the CD player from
  suddenly stopping playback of the first track a few seconds after t2. In
  order to prevent this, one could use a longer interaction sequence, which
  leads us to our second explanatory example.

  Let us consider a slightly more complex interaction sequence, one with one
  input event followed by two output events. For the CD player example, the
  input event could again be the pushing of the PLAY button, the first output
  event could again be the first track starting playback, and the second
  output event could be the second track starting playback (assuming that the
  CD has at least two tracks, which should be part of the conditions on t1,
  i.e. that there is a CD inserted and that it has at least two tracks;
  obviously, the interaction sequence can be extended to a full playback of
  all the CD tracks). The separation constraint between the two output events
  are determined by the length of the first track: the maximum and minimum
  separations should be the track length plus or minus a small tolerance.

  The informal meaning of this interaction sequence is: if the input event
  occurs at any time t1 (satisfying the needed conditions), then the first
  output event occurs at some time t2 that satisfies the separation
  constraints with t1 and the second output event occurs at some t3 that
  satisfies the separation constraints with t2 and t1 (in the CD player
  example, only t2, but in general there could be constraints with respect to
  t1 too). Again, we must take care to disallow any event other than these
  three, in the time interval from t1 to t3. This leads to:

  fn evTr ->
  (fa(t1) t1 satisfies suitable conditions &&
          (t1, input event) in? evTr &&
          noInputsUntilOutput? evTr t1 =>
          (ex(t2) t2 satisfies separation constraints with t1 &&
                  onlyOutputAtAfter? (evTr, first output event, t2, t1) &&
                  (noInputsUntilOutput? evTr t2 =>
                   (ex(t3) t3 satisfies separation constraints with t1 and t2 &&
                           onlyOutputAtAfter?
                             (evTr, second output event, t3, t2)))))

  We use predicate noInputUntilOutput? to disallow any input events other than
  the one at t1. We use predicate onlyOutputAtAfter? to disallow any output
  events other than the ones at t2 and t3.

  Let us slightly rephrase the above predicate as follows:

  fn evTr ->
  (fa(t1) t1 satisfies suitable conditions &&
          (t1, input event) in? evTr =>
          (noInputsUntilOutput? evTr t1 =>
           (ex(t2) t2 satisfies separation constraints with t1 &&
                   onlyOutputAtAfter? (evTr, first output event, t2, t1) &&
                   (noInputsUntilOutput? evTr t2 =>
                    (ex(t3) t3 satisfies separation constraints with t1 and t2 &&
                            onlyOutputAtAfter?
                              (evTr, second output event, t3, t2))))))

  The only change is that we have replaced && with => in the third line,
  adding suitable parentheses. The predicate is equivalent, because (P && Q =>
  R) is equivalent to (P => (Q => R)). The reason for this re-phrasing is to
  make the pattern followed by the predicate more evident:

  fn evTr ->
  ***** input event:
  (fa(t1) t1 satisfies suitable conditions &&
          (t1, input event) in? evTr =>
  ***** first output event:
          (noInputsUntilOutput? evTr t1 =>
           (ex(t2) t2 satisfies separation constraints with t1 &&
                   onlyOutputAtAfter? (evTr, first output event, t2, t1) &&
  ***** second output event:
                   (noInputsUntilOutput? evTr t2 =>
                    (ex(t3) t3 satisfies separation constraints with t1 and t2 &&
                            onlyOutputAtAfter?
                              (evTr, second output event, t3, t2))))))

  Note that the parts of the predicate that deal with the two output events
  are very similar. Each says that if there is no input event between the time
  of the previous (input or output) event (i.e. t1 or t2) and the time of the
  output event in question (t2 or t3), then the output event in question is
  the only one in that interval.

  Let us now consider a symmetric variation of this interation sequence, one
  with two input events followed by one output event. In the CD player
  example, the first input event could be the insertion of a CD into the
  player, the second input event could be the pushing of the PLAY button, and
  the output event could be the first track starting playback. There could be
  a minimum separation constraint between the first input event and the second
  output event, because typically when a CD is inserted into a player the
  player reads and memorizes the CD's table of contents in order to
  efficiently access the different tracks. So, we need to give the player
  enough time for that, before pushing PLAY and expecting the first track to
  play. On the other hand, we could put no constraint on the maximum
  separation between the two input events: we can wait as much as we want
  before starting playback.

  The informal meaning of this interaction sequence is: if the first input
  event occurs at any time t1 (satisfying the needed conditions, e.g. that the
  CD player is empty) and the second input event occurs at any time t2
  satisfying the separation constraints with t1, then the output event occurs
  at some time t3 that satisfies the separation constraints with t1 and t2.
  Using the fact that (P && Q => R) is equivalent to (P => (Q => R)), we
  formalize the predicate like this:

  fn evTr ->
  ***** first input event:
  (fa(t1) t1 satisfies suitable conditions &&
          (t1, firstinput event) in? evTr =>
  ***** second input event:
          (fa(t2) t2 satisfies separation constraints with t1 &&
                  onlyInputAtAfter? (evTr, second input event, t2, t1) =>
  ***** output event:
                  (noInputsUntilOutput? evTr t2 =>
                   (ex(t3) t3 satisfies separation constraints with t1 and t2 &&
                           onlyOutputAtAfter?
                             (evTr, second output event, t3, t1)))))

  We use predicate onlyInputAtAfter? to disallow input events between t1 and
  t2. The portion of the predicate that deals with the output event is almost
  the same as in the predicate for the previous interaction sequence (the one
  with one input event and two output events), except that t1 appears as the
  last argument of onlyOutputAtAfter?, instead of t2. The reason is that we
  need to disallow output events not only between t2 and t3, but also between
  t1 and t2.

  One could be tempted to use t2 instead, and to move the requirement of no
  output events between t1 and t2 "earlier" in the predicate. We could define
  a predicate noOutputUntilInputs? (dual to noInputsUntilOutputs?) and attempt
  to rewrite the above predicate as follows:

  fn evTr ->
  ***** first input event:
  (fa(t1) t1 satisfies suitable conditions &&
          (t1, firstinput event) in? evTr =>
  ***** second input event:
          noOutputsUntilInput? evTr t1 &&   <--- added
          (fa(t2) t2 satisfies separation constraints with t1 &&
                  onlyInputAtAfter? (evTr, second input event, t2, t1) =>
  ***** output event:
                  (noInputsUntilOutput? evTr t2 =>
                   (ex(t3) t3 satisfies separation constraints with t1 and t2 &&
                           onlyOutputAtAfter?
                             (evTr, second output event, t3, t2)))))   <-- was t1

  However, in general, this is too strong. It starts with:

  fn evTr ->
  (fa(t1) t1 satisfies suitable conditions &&
          (t1, firstinput event) in? evTr =>
          noOutputsUntilInput? evTr t1 &&
          ...

  Because of the conjunction in the consequent of the implication, no matter
  what other input events may occur (in the "..." part), it must be always the
  case that, after we insert a CD into the player, the player waits forever
  for a further input from the user. However, the CD player might have a
  power-saving feature that turns the player off after, say, 1 minute of
  inactivity (i.e. no track playing and no user inputs). This automatic
  turning off, and/or a short message on the display announcing that the
  player is turning itself off, is an output event, which would be prohibited
  by the above attempt to rewrite the predicate. As an aside, note that this
  power-saving feature would make it necessary, in the interaction sequence
  under consideration (i.e. insert CD, push PLAY, first track plays), to add a
  maximum separation constraint between the two input events, equal to the
  timeout for the power-saving feature (a few paragraphs above, we had instead
  hypothesized that the user could wait as much as desired to push PLAY,
  effectively prohibiting the power-saving feature).

  The three simple interaction sequences analyzed above suffice to understand
  the general patterns needed to express the predicates associated to
  arbitrary interaction sequences.

  First, the predicate for an interaction sequence always starts with a
  universally quantified implication, whose antecedent constrains the
  universally quantified time instant to satisfy suitable conditions for the
  start of the interaction sequence and constrains the opening input event of
  the sequence to occur at that time instant. The consequent of the
  implication is derived from the rest of the interaction sequence. This is
  captured by op eventTraceConstraint below. It takes as arguments an
  interaction sequence, a condition that the starting time of the sequence
  must satisfy (in the form of a predicate over time), and returns a predicate
  over event traces. The returned predicate follows exactly the pattern just
  described. The consequent of the implication is the result of op
  eventTraceConstraintAux, which associates "subpredicates" of the predicate
  based on the events of the interaction sequence that come after the first.

  The subpredicates for the events other than the first are nested in the
  order that the events occur in the sequence. Thus, op
  eventTraceConstraintAux is recursive.

  The subpredicate for an input event (other than the first) in an interaction
  sequence is a universally quantified implication. The antecedent constrains
  the universally quantified time to satisfy separation constraints with the
  time instants of the previous events and the input event to be the only
  input event occurring between the time of the previous event and the
  universally quantified time. The consequent is derived from the successive
  events of the interaction sequence.

  The subpredicate for an output event in an interaction sequence is an
  (unquantified) implication. The antecedent says that no input events occur
  after the time of the previous event until the output event occurs (i.e. we
  "wait" for the output event). The consequent is an existentially quantified
  conjunction of three conjuncts. The first conjunct constrains the
  existentially quantified time to satisfy separation constraints with the
  time instants of the previous events. The second conjunct constrains the
  output event to be the only output event since the last output event. If
  this is the first output event of the interaction sequence, then the
  conjunct constrains the output event to be the only output event since the
  first event of the interaction sequence (which is always an input event).
  The third conjunct is derived from the successive events of the interaction
  sequence. *)

  op eventTraceConstraintAux :
     {(previousEvents,nextEventsWithSeparations) :
      EventSeq * List (EventSeparation * Event) |
      fa(i:Nat) i < length nextEventsWithSeparations =>
        validEventSeparation? (length previousEvents + i)
                              (nextEventsWithSeparations @ i).1} ->
     DiscreteTrace Event -> Bool
  def eventTraceConstraintAux (previousEvents, nextEventsWithSeparations) evTr =
    % if no more events, we are done, return true (i.e. no constraint on evTr):
    if empty? nextEventsWithSeparations then true else
    % consider next event with its separation constraints:
    let (evSep, ev) = head nextEventsWithSeparations in
    % construct subformula for input event:
    if input? ev then
      (fa(t:Time)  % universal quantification
         separatedFrom? (t, previousEvents, evSep) &&  % separation
         onlyInputAtAfter?  % input event occurrence
           evTr ev t (timeOfLastEvent previousEvents)
         =>  % implication
         eventTraceConstraintAux  % recursively process following events
           (previousEvents <| (t, ev), tail nextEventsWithSeparations) evTr)
    % construct subformula for output event:
    else (* output? ev *)
      (noInputsUntilOutput?
         evTr (timeOfLastEvent previousEvents)
       =>  % implication
       (ex(t:Time)  % existential quantification
          separatedFrom? (t, previousEvents, evSep)  % separation
          &&  % conjunction
          onlyOutputAtAfter?  % output event occurrence
            evTr ev t (timeOfLastOutputEventOrFirstEvent previousEvents)
          &&  % conjunction
          eventTraceConstraintAux  % recursively process following events
            (previousEvents <| (t, ev), tail nextEventsWithSeparations) evTr))

  op eventTraceConstraint :
     InteractionSequence -> (Time -> Bool) -> DiscreteTrace Event -> Bool
  def eventTraceConstraint intSeq cond evTr =
    fa(t:Time)  % universal quantification
      % t satisfies the given condition:
      cond t &&
      % first input event occurs at t:
      evTr t =Some intSeq.first =>  % implication
      % recursively process the events after the first:
      eventTraceConstraintAux (single (t, intSeq.first), intSeq.rest) evTr

  (* The notion of interaction sequence formalized in this spec allows the
  user to state impossible interaction sequences, i.e. sequences that are not
  satisfied by any trace of events. An example of impossible sequence is one
  with three contiguous events e1, e2, and e3 (in that order) and with a
  maximum separation between e3 and e1 that is smaller than the minimum
  separation between e2 and e1. Op eventTraceConstraint associates to such an
  impossible sequence the always-false predicate over event traces. Thus, the
  user must exercise some care in defining interaction sequences. In the
  future, the type of interaction sequence defined in this spec could be
  re-defined to disallow impossible sequences. *)

endspec
