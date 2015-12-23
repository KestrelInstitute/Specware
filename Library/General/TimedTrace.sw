(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

TimedTrace qualifying spec

import Real, Sequence

(* In order to describe traces of things (e.g. events) that happen in time in
the physical world, we model time instants as non-negative real numbers (as is
customary in physics). Thus, we consider traces along the timeline that consists
of the non-negative real semi-axis. The origin of the timeline (i.e. time
instant 0) marks the beginning of our observations of traces; we do not observe
anything before the origin. This is adequate to describe computing systems which
are always started at some point in time, as opposed to having been running
forever in the past.

Note that the following type, besides capturing time instants, also captures
time durations. For example, given t:Time that represents an instant and d:Time
that represents a duration, (t+d):Time is another instant. In the future, we may
generalize the notion of time used here to include richer forms of denoting time
instants and durations (e.g. records representing dates and times of day). We
may also generalize the notion to include not only the future starting from an
origin time but also the past (e.g. the whole real axis). *)

type Time = NonNegReal

(* Normally, a trace of things is a (potentially infinite) sequence of those
things. Here, since we want to associate time to the elements of the trace, we
use a map from time instants to the type of the elements in the trace (which is
left open, using polymorphism); the linear order of time instants determined the
sequentialization of the elements of the trace. *)

type Trace a = Map (Time, a)

% some filtering operations over traces:

op [a] before (tr:Trace a, t:Time) infixl 25 : Trace a =
  tr restrictDomain (fn t':Time -> t' < t)  % keep elements before t

op [a] after (tr:Trace a, t:Time) infixl 25 : Trace a =
  tr restrictDomain (fn t':Time -> t' > t)  % keep elements after t

op [a] notAfter (tr:Trace a, t:Time) infixl 25 : Trace a =
  tr restrictDomain (fn t':Time -> t' <= t)  % keep elements not after t

op [a] notBefore (tr:Trace a, t:Time) infixl 25 : Trace a =
  tr restrictDomain (fn t':Time -> t' >= t)  % keep elements not before t

(* We say that a trace is finitely dense when there is a finite number of
elements in every finite time interval (recall that type Real.Range captures a
finite range of real numbers). *)

op [a] finitelyDense? (tr:Trace a) : Bool =
  fa(interval:Real.Range) interval <= nonNegative? =>
    finite? (tr restrictDomain interval)

type TraceFD a = (Trace a | finitelyDense?)

(* The sequentialization of the elements of a finitely dense trace is explicated
by the following ops, which return the sequence of the elements and/or time
instants that comprise the trace. This is not always possible for a trace that
is not finitely dense: for instance, if we could organize the elements of a
trace whose domain consists of all the real numbers into a sequence, it would
mean that the real numbers are countable, which is not the case. *)

op [a] seq (tr:TraceFD a) : Seq (Time * a) =
  % the resulting sequence s is characterized as follows:
  the (s: Seq (Time * a))
  % for each i:
  fa(i:Nat)
  % if i exceeds the number of elements in the trace, s has no element at i:
    (if finite? tr && size (domain tr) <= i then s @@ i = None
  % otherwise, s has an element at i, obtained by removing the first i
  % elements from the trace and then taking the first remaining element:
     else s @@ i ~= None &&
          (let t:Time = minIn (domain (tr -- toSet (map (project 1) (prefix (s, i))))) in
          s @ i = (t, tr @ t)))
          (* Why writing "s @@ i ~= None && ... s @ i = ..." as opposed to just
          "s @@ i = Some ..."? Because the condition "s @@ i ~= None" is needed
          for "prefix (s, i)" to be well-defined, which is in turn needed to
          define the exact value of element i of s. *)

op [a] timeSeq (tr:TraceFD a) : Seq Time = map (project 1) (seq tr)

op [a] elemSeq (tr:TraceFD a) : Seq a    = map (project 2) (seq tr)

endspec
