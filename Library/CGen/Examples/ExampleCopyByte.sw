(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* In this example,
we want to derive from requirements a C function that copies
a byte (unsigned char) from its 1st argument
to the object pointed to by its 2nd argument.
The derived C function should be

  void copy(unsigned char src, unsigned char *dst) {
    *dst = src;
  }

This is a very simple example, but we want to work out in detail
how that C code can be derived from a higher-level requirement specification
with proofs. *)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(* We start with a requirement specification. *)

Spec = spec

import CUtilities

(* In order to have a clear relationship
between the generated C function and its requirement specification,
we express the requirement specification on the C function
as constraints on a shallow embedding of the C function,
which is a Specware function with the signature described in spec CModel.

For this example, the Specware function has the signature

  copy (src: UcharValue) (dst: (PointerValue | toType? uchar)): Monad ()

The only kind of requirements that the shallow embedding permits us to express
concern the pre/post-condition behavior of the function
(a deep embedding is needed to express additional kinds of constraints,
as in pop-refinement).

The C compiler enforces the pre-conditions
expressed by the types of the arguments.
Additional pre-conditions are captured by the following predicate,
defined on the same arguments of the function and on the state:
- dst points to an unsigned char object in the state;
- the state is well-formed.
Note that a C function that receives a pointer argument
can check to see if it is null or not,
but cannot check if a non-null pointer points to an unsigned char object---
the C function must trust the caller on this.
For this example, we could use a weaker pre-condition
that allows a null pointer (which the function would have to check for),
but we keep the example simpler with this stronger pre-condition.
Note also that a C function cannot check the well-formedness of the state. *)

op pre? (src: UcharValue)
        (dst: (PointerValue | toType? uchar))
        (state: State): Bool =
  wfState? state &&
  pointsToObject? state dst

(* The post-condition is that
the state after executing the function
is like the state before executing the function,
with the only difference that the object designated by dst
contains the value src.
This is captured by the following predicate,
defined on
the arguments of the function, the before-state, and the after-state. *)

op post? (src: UcharValue)
         (dst: (PointerValue | toType? uchar))
         (state: State) (state': State): Bool =
  writePointed state dst src = Some state'

(* We can capture the requirements on our target C function
as a predicate over Specware functions with the type of the target C function.
The requirements are that
if the function is run in a state with arguments
that satisfy the pre-condition,
then the function must terminate without error
and the new state must satisfy the post-condition
(with the initial state and with the arguments).

This form of specification is quite in the spirit of pop-refinement,
even though we are using a shallow embedding and not a deep embedding.
In this specification, the target "programs" are
Specware functions that represent shallow embeddings of C functions.
This specification can be pop-refined
by constructing a monotonically decreasing sequence of predicates
over functions of this type,
ending with a predicate that characterizes a unique function, i.e.

  op spec?_end
    (copy: UcharValue -> (PointerValue | toType? uchar) -> Monad ()): Bool =
    copy = (fn src: UcharValue ->
            fn dst: (PointerValue | toType? uchar) ->
            <shallowly-embedded-function-body>)

using exclusively the shallowly embedded expressions and statements,
from which program text can be readily extracted. *)

op spec?
  (copy: UcharValue -> (PointerValue | toType? uchar) -> Monad ()): Bool =
  fa (src: UcharValue, dst: (PointerValue | toType? uchar), state: State)
    pre? src dst state =>
    (ex (state':State)
      copy src dst state = Some (state', ()) &&
      post? src dst state state')

(* Another form of specification, which follows Specware's classical style,
is to declare an uninterpreted function
along with an axiom that expresses requirements on the function.
This specification can be refined
by constructing a sequence of Specware specifications and morphisms
ending with a specification that defines the function, i.e.

  spec
    ...
    op copy (src: UcharValue) (dst: (PointerValue | toType? uchar)): Monad () =
      <shallowly-embedded-function-body>
  endspec

using exclusively the shallowly embedded expressions and statements
(the same as in the pop-refinement approach described above),
from which program text can be readily extracted. *)

op copy: UcharValue -> (PointerValue | toType? uchar) -> Monad ()

axiom spec?copy is
  spec? copy

endspec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(* We want to stepwise refine the requirement specification
using transformations. *)

Step0 = Spec

Step1 = transform Step0 by {
at spec?
  {unfold post?}
}
(* RESULT:
spec  
import Step0
refine def spec? (copy: UcharValue -> (PointerValue | toType? uchar) -> Monad(())): Bool
  = fa(src: UcharValue, dst: (PointerValue | toType? uchar), state: State) 
     pre? src dst state 
      => (ex(state': State) 
           copy src dst state = Some(state', ()) && writePointed state dst src = Some state')
end-spec
*)

% IN PROGRESS...

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(* Here we manually explore how an automated derivation could be performed. *)

Explore = spec

import Spec

op refined_spec?
  (copy: UcharValue -> (PointerValue | toType? uchar) -> Monad ()): Bool =
( % original definition of spec?:
  fa (src: UcharValue, dst: (PointerValue | toType? uchar), state: State)
    pre? src dst state =>
    (ex (state':State)
      copy src dst state = Some (state', ()) &&
      post? src dst state state')
; % unfold post?:
  fa (src: UcharValue, dst: (PointerValue | toType? uchar), state: State)
    pre? src dst state =>
    (ex (state':State)
      copy src dst state = Some (state', ()) &&
      writePointed state dst src = Some state')
; % lr optionEqSome (not working in transformation shell):
  fa (src: UcharValue, dst: (PointerValue | toType? uchar), state: State)
    pre? src dst state =>
    (ex (state':State)
      copy src dst state = Some (state', ()) &&
      writePointed state dst src ~= None &&
      state' = unwrap (writePointed state dst src))
; % commute && (OK in this case):
  fa (src: UcharValue, dst: (PointerValue | toType? uchar), state: State)
    pre? src dst state =>
    (ex (state':State)
      writePointed state dst src ~= None &&
      state' = unwrap (writePointed state dst src) &&
      copy src dst state = Some (state', ()))
; % unfold pre?:
  fa (src: UcharValue, dst: (PointerValue | toType? uchar), state: State)
    wfState? state &&
    pointsToObject? state dst =>
    (ex (state':State)
      writePointed state dst src ~= None &&
      state' = unwrap (writePointed state dst src) &&
      copy src dst state = Some (state', ()))
; % use theorem writePointedObject:
  fa (src: UcharValue, dst: (PointerValue | toType? uchar), state: State)
    wfState? state &&
    pointsToObject? state dst =>
    (ex (state':State)
      state' = unwrap (writePointed state dst src) &&
      copy src dst state = Some (state', ()))
; % logic:
  fa (src: UcharValue, dst: (PointerValue | toType? uchar), state: State)
    wfState? state &&
    pointsToObject? state dst =>
    copy src dst state = Some (unwrap (writePointed state dst src), ())
; % rl writePointedM_writePointed:
  fa (src: UcharValue, dst: (PointerValue | toType? uchar), state: State)
    wfState? state &&
    pointsToObject? state dst =>
    copy src dst state = writePointedM dst src state
; % lr writePointedE_valueExpr:
  fa (src: UcharValue, dst: (PointerValue | toType? uchar), state: State)
    wfState? state &&
    pointsToObject? state dst =>
    copy src dst state = writePointedE (valueExpr dst) (valueExpr src) state
) % IN PROGRESS...

endspec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(* Our goal is to conclude the derivation
with the following characterization of the copy function. *)

Goal = spec

import Spec

op goal?
  (copy: UcharValue -> (PointerValue | toType? uchar) -> Monad ()): Bool =
  copy = (fn src: UcharValue ->
          fn dst: (PointerValue | toType? uchar) ->
          {INIT ["src", "dst"] [src, dst];
           (STAR (variable "dst")) ASG (variable "src");
           RETURNv})

endspec
