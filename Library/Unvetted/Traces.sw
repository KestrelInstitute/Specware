(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
2005:06:24
AC

This is a spec for traces of "things" in time.

The spec could be amenable to generalizations, some of which are indicated by
comments in the spec.
*)


Trace qualifying spec

  (* We model time densely using (non-negative) rational numbers. Alternatives
  are modeling time discretely using integer numbers or continuously using
  real numbers. Eventually, this spec should be parameterized over a suitable
  notion of time, which can be instantiated to be integers, rationals, reals,
  or others (e.g. records consisting of a date and a time). *)

  import Rational

  type Time = NonNegativeRational

  (* Normally, a trace of something (e.g. events) is a (potentially infinite)
  sequence of those things, which can be modeled by a function from Nat to the
  type of those things. Here, since we want to associate time to everything in
  the trace, we use a map from time instants to the type of the things in the
  trace; the linear order of time instants automatically defines the
  sequentialization of the elements of the trace. These traces of things in
  time are captured by type DiscreteTrace below.

  We require a trace to contain a finite number of elements in every time
  interval. Eventually this requirement should be factored out, defining two
  types of discrete traces: one with a finite number of elements in every time
  interval, and one with a potentially infinite number. *)

  import /Library/General/Map

  type DiscreteTrace a =
    {tr : Map (Time, a) | fa(interval:Range) finite? (tr restrictDomain interval)}

  % filtering operations over discrete traces:

  op before infixl 25 : [a] DiscreteTrace a * Time -> DiscreteTrace a
  def before (tr,t) = tr restrictDomain (fn t1 -> t1 < t)

  op after infixl 25 : [a] DiscreteTrace a * Time -> DiscreteTrace a
  def after (tr,t) = tr restrictDomain (fn t1 -> t1 > t)

  op notAfter infixl 25 : [a] DiscreteTrace a * Time -> DiscreteTrace a
  def notAfter (tr,t) = tr restrictDomain (fn t1 -> t1 <= t)

  op notBefore infixl 25 : [a] DiscreteTrace a * Time -> DiscreteTrace a
  def notBefore (tr,t) = tr restrictDomain (fn t1 -> t1 >= t)

  op suchThat infixl 25 : [a] DiscreteTrace a * (a -> Bool) -> DiscreteTrace a
  def suchThat (tr,p) = tr restrictRange p

  % return first element of trace, if trace is not empty:

  op first : [a] DiscreteTrace a -> Option (Time * a)
  def first tr =
    if nonEmpty? tr
    then let t = min (domain tr) in Some (t, tr @ t)
    else None  % op totalized via Option

  % return last element of trace, if trace is finite:

  op last : [a] DiscreteTrace a -> Option (Time * a)
  def last tr =
    if finite? tr
    then let t = max (domain tr) in Some (t, tr @ t)
    else None  % op totalized via Option

  (* Since time is modeled densely with rational numbers, we introduce a
  notion of continuous traces as functions from (all) time instants to some
  type. Perhaps "DenseTrace" could be a better name, while "ContinuousTrace"
  could be used when modeling time continuously with real numbers. *)

  type ContinuousTrace a = Time -> a

  % check whether trace is constant in set of times (usually an interval):

  op constantIn infixl 20 : [a] ContinuousTrace a * Set Time -> Bool
  def constantIn (tr,times) = (ex(x) (fa(t) t in? times => tr t = x))

  % if trace constant in set of times, return that constant value:

  op constantValue : [a] ContinuousTrace a -> Set Time -> Option a
  def constantValue tr times =
    if tr constantIn times then
      Some (the(x) (ex(t) t in? times && tr t = x))
    else None  % op totalized via Option

  (* We introduce a notion of traces of things that have extents in time. Each
  thing starts at a time instant and ends at a time instant, i.e. has a closed
  range of times associated to it. A trace is a set of such "segments" of
  things in time. Note that segments may overlap in time. *)

  type Segment a = a * ClosedRange

  op extent : [a] Segment a -> ClosedRange
  def extent = project 2

  type NonZeroSegment a =
    {seg : Segment a | length (extent seg) > zero}

  type SegmentTrace a = Set (Segment a)

  % filtering operations over segment traces:

  op endedBefore infixl 25 : [a] SegmentTrace a * Time -> SegmentTrace a
  def endedBefore (tr,t) = tr /\ (fn seg -> sup (extent seg) < t)

  op endedNotAfter infixl 25 : [a] SegmentTrace a * Time -> SegmentTrace a
  def endedNotAfter (tr,t) = tr /\ (fn seg -> sup (extent seg) <= t)

  op startedAfter infixl 25 : [a] SegmentTrace a * Time -> SegmentTrace a
  def startedAfter (tr,t) = tr /\ (fn seg -> inf (extent seg) > t)

  op startedNotBefore infixl 25 : [a] SegmentTrace a * Time -> SegmentTrace a
  def startedNotBefore (tr,t) = tr /\ (fn seg -> inf (extent seg) >= t)

  op nonOverlapping? : [a] SegmentTrace a -> Bool
  def nonOverlapping? tr =
    (fa(seg1,seg2) seg1 in? tr && seg2 in? tr && seg1 ~= seg2 =>
                   extent seg1 /\ extent seg2 = empty)

  % traces of non-overlapping segments (segments are sequential and separated):

  type NonOverlappingSegmentTrace a = (SegmentTrace a | nonOverlapping?)

  % return first segment of trace, if trace is not empty:

  op firstSegment : [a] NonOverlappingSegmentTrace a -> Option (Segment a)
  def firstSegment tr =
    if nonEmpty? tr then
      Some (the(seg) seg in? tr &&
                     (fa(seg1) seg1 in? tr && seg1 ~= seg =>
                               (extent seg) allLess (extent seg1)))
    else None  % op totalized via Option

  % return last segment of trace, if trace is finite:

  op lastSegment : [a] NonOverlappingSegmentTrace a -> Option (Segment a)
  def lastSegment tr =
    if finite? tr then
      Some (the(seg) seg in? tr &&
                     (fa(seg1) seg1 in? tr && seg1 ~= seg =>
                               (extent seg) allGreater (extent seg1)))
    else None  % op totalized via Option

  (* Given a trace of non-overlapping segments, at any time instant there is
  either no segment or exactly one segment. Thus, we can build a continuous
  trace of the segment at every time instant, using Option for the instants
  with no segment. *)

  op toContinuous : [a]
     NonOverlappingSegmentTrace a -> ContinuousTrace (Option a)
  def toContinuous tr t =
    if ~(ex(seg) seg in? tr && t in? extent seg) then None
    else let seg = the(seg) seg in? tr && t in? extent seg in Some seg.1

  (* The notion of discrete traces and segment traces could be unified by
  generalizing the elements of discrete traces to have possibly non-zero time
  extents, so that discrete traces would become what now are segment
  traces. We could then define a subtype of discrete traces such that all
  elements have zero extents, i.e. they are instantaneous, obtaining what now
  are discrete traces. *)

endspec
