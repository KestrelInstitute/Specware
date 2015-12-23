(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* This file contains some example Specware derivations of C programs
from specifications via stepwise refinement,
using the model of C features in spec CModel.

In general, a C function with N >= 0 arguments and non-void return type
is specified by a Specware op of the form

  op f (state:State, arg1:Value, ..., argN:Value | ...): State * (Value | ...)

and a C function with N >= 0 arguments and void return type
is specified by a Specware op of the form

  op f (state:State, arg1:Value, ..., argN:Value | ...): State

where in both cases the state is threaded through the op
and the subtype conditions are used to define the C types of the arguments
(and of the result, if any).
See examples below for details. *)

Utilities = spec

import CModel

(* This spec does not contain an example.
It defines utility concepts used in the examples in the specs below. *)

(* A buffer is often passed to a C function in the form of two arguments:
(1) a pointer to the first element of the buffer;
(2) the length, i.e. the number of elements, of the buffer.
The pointer normally points to
some element (not necessarily the first) of some array,
i.e. the buffer is part of an array;
the length should not exceed the number of remaining elements in the array.
As a special case, the pointer could point to
an object that is not an element of an array,
but in that case the length should not exceed 1;
pointer arithmetic with this object works in the same way
as with an array of length 1 [ISO 6.5.6/7].
As an even more special case,
the length could be 0 and in that case the pointer is irrelevant.
The following ops formalize reading from and writing to a buffer
identified by pointer and length values. *)

(* The length is normally passed as an integer value,
but in the case of an output buffer
(i.e. a buffer intended for writing by the function)
the length could be passed as a pointer to an integer object,
which initially contains the maximum length of the output buffer
and which the function sets to the actual length prior to returning.
The following op reads the length of a buffer
from an integer value or from a pointer value.
The length must be non-negative. *)

op readBufferLength (state:State) (len:Value): Option Nat =
  if integerValue? len
  then let n = mathIntOfValue len in
       if n >= 0 then Some n else None
  else case len of
       | nnpointer (_, object obj) ->
         (case readObject state obj of
         | Some val ->
           if integerValue? val
           then let n = mathIntOfValue val in
                if n >= 0 then Some n else None
           else None
         | None -> None)
       | _ -> None

(* The following op reads the values in a buffer from (part of) an array.
The ptr value must be a pointer whose object designator is a subscript;
readObject is applied not to the object designator
(which would just yield the array element),
but to the designator of the enclosing array object,
from which a portion of the element values is extracted and returned. *)

op readBufferFromArray
  (state:State) (ptr:Value) (len:Value): Option (List Value) =
  case (ptr, readBufferLength state len) of
  | (nnpointer (ty, object (subscript (obj, i))), Some n) ->
    (case readObject state obj of
    | Some (array (ty', vals)) ->
      if ty' = ty && i + n <= length vals
      then Some (subFromLong (vals, i, n))
      else None
    | _ -> None)
  | _ -> None

(* The following op reads the value of a 1-length buffer
from an object that is not an array element.
In our current model of values,
the only values in the state that are not array elements
are objects whose designators are outside IDs without subscripts.
The returned list of value has always length 1. *)

op readBufferFromNonArray
  (state:State) (ptr:Value) (len:Value): Option (List Value) =
  case (ptr, readBufferLength state len) of
  | (nnpointer (ty, object (outside id)), Some n) ->
    (case state.outside id of
    | Some val ->
      if typeOfValue val = ty && n = 1
      then Some [val]
      else None
    | None -> None)
  | _ -> None

(* The following op reads the values in a buffer that is
(part of) an array,
a 1-length buffer consisting of a non-array-element object,
or a 0-length buffer. *)

op readBuffer (state:State) (ptr:Value) (len:Value): Option (List Value) =
  % array:
  case readBufferFromArray state ptr len of
  | Some vals -> Some vals
  | None ->
    % 1-length buffer of non-array-element value:
    (case readBufferFromNonArray state ptr len of
    | Some vals -> Some vals
    | None ->
      % 0-length buffer:
      (case readBufferLength state len of
      | Some 0 -> Some []  % regardless of ptr
      | _ -> None))

(* The following op writes values to a buffer from (part of) an array.
The ptr value must be a pointer whose object designator is a subscript;
readObject and writeObject are applied not to the object designator
(which would just operate on the array element),
but to the designator of the enclosing array object,
into which a portion of the element values are written.
There must be enough room for the values in the buffer. *)

op writeBufferToArray
  (state:State) (ptr:Value) (len:Value) (vals:List Value): Option State =
  case (ptr, readBufferLength state len) of
  | (nnpointer (ty, object (subscript (obj, i))), Some n) ->
    (case readObject state obj of
    | Some (array (ty', oldVals)) ->
      if ty' = ty && i + n <= length oldVals && length vals <= n
      then let newVals = prefix (oldVals, i) ++
                         vals ++
                         removePrefix (oldVals, i + length vals)
           in writeObject state obj (array (ty, newVals))
      else None
    | _ -> None)
  | _ -> None

(* The following op writes values to a 1-length buffer
from an object that is not an array element.
In our current model of values,
the only values in the state that are not array elements
are objects whose designators are outside IDs without subscripts. *)

op writeBufferToNonArray
  (state:State) (ptr:Value) (len:Value) (vals:List Value): Option State =
  case (ptr, readBufferLength state len) of
  | (nnpointer (ty, object (outside id)), Some n) ->
    (case state.outside id of
    | Some oldVal ->
      if typeOfValue oldVal = ty && n = 1
      then case vals of
           | [] -> Some state  % no new values, no change
           | [newVal] ->
             Some (state << {outside = update state.outside id newVal})
           | _ -> None  % not enough room for 2 or mote values
      else None
    | None -> None)
  | _ -> None

(* The following op writes values in a buffer that is
(part of) an array,
a 1-length buffer consisting of a non-array-element object,
or a 0-length buffer.
There must be enough room for the values in the buffer. *)

op writeBuffer
  (state:State) (ptr:Value) (len:Value) (vals:List Value): Option State =
  % array:
  case writeBufferToArray state ptr len vals of
  | Some state' -> Some state'
  | None ->
    % 1-length buffer of non-array-element value:
    (case writeBufferToNonArray state ptr len vals of
    | Some state' -> Some state'
    | None ->
      % 0-length buffer:
      (case readBufferLength state len of
      | Some 0 -> if length vals = 0 then Some state else None
      | _ -> None))

(* In order to express (non-)overlap of buffers
it is useful to define an op that returns
the set of all object designators of the elements of a buffer.
As in the ops that define buffer reads and writes
the buffer could be part of an array
or could be an object that is not an element of an array. *)

op objectDesignatorsOfBufferInArray
  (state:State) (ptr:Value) (len:Value): FiniteSet ObjectDesignator =
  case (ptr, readBufferLength state len) of
  | (nnpointer (ty, object (subscript (obj, i))), Some n) ->
    (case readObject state obj of
    | Some (array (ty', vals)) ->
      if ty' = ty && i + n <= length vals
      then (fn obj' ->
             (ex (j:Nat) i <= j && j < i + n && obj' = subscript (obj, j)))
      else empty
    | _ -> empty)
  | _ -> empty

op objectDesignatorsOfBufferInNonArray
  (state:State) (ptr:Value) (len:Value): FiniteSet ObjectDesignator =
  case (ptr, readBufferLength state len) of
  | (nnpointer (ty, object (outside id)), Some n) ->
    (case state.outside id of
    | Some val ->
      if typeOfValue val = ty && n = 1
      then single (outside id)
      else empty
    | None -> empty)
  | _ -> empty

op objecDesignatorsOfBuffer
  (state:State) (ptr:Value) (len:Value): FiniteSet ObjectDesignator =
  % at most one of the following returns a non-empty set:
  objectDesignatorsOfBufferInArray state ptr len \/
  objectDesignatorsOfBufferInNonArray state ptr len

(* Two buffers overlap iff they have some object designator in common. *)

op buffersOverlap?
  (state:State) (ptr1:Value) (len1:Value) (ptr2:Value) (len2:Value): Bool =
  objecDesignatorsOfBuffer state ptr1 len1 /\
  objecDesignatorsOfBuffer state ptr2 len2 ~= empty

endspec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

CopyByte = spec

import Utilities

(* We specify a C function that copies a byte (unsigned char)
from its 1st argument to the object pointed to by its 2nd argument. *)

op copyByte
  (state:State, src:Value, dst:Value |
    % state and arguments are well-formed:
    wfState? state &&
    wfValue? state src &&
    wfValue? state dst &&
    % C types of arguments:
    typeOfValue src = uchar &&
    typeOfValue dst = pointer uchar)
  : (State | wfState?) =
  % the new state is the result of
  % storing the 1st argument into the 2nd argument:
  let nnpointer (_, object obj) = dst in
  unwrap (writeObject state obj src)

(* We would like to refine this specification to a C function of this form:

  void copyByte(unsigned char src, unsigned char *dst) {
      *dst = src;
  }
*)

endspec

% CopyByteCode =
%   CopyByte
%     {genC
%      ((copyByte), (copyByte), (State), State, None, None, "CopyByte", true)}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

SwapBytes = spec

import Utilities

(* We specify a C function that swaps two bytes (unsigned chars)
whose pointers are passed as arguments. *)

op swapBytes
   (state:State, x:Value, y:Value |
     % state and values are well-formed:
     wfState? state &&
     wfValue? state x &&
     wfValue? state y &&
     % C types of arguments:
     typeOfValue x = pointer uchar &&
     typeOfValue y = pointer uchar)
  : (State | wfState?) =
  % the new state is the result of swapping the two values:
  let nnpointer (_, object objx) = x in
  let nnpointer (_, object objy) = y in
  let Some valx = readObject state objx in
  let Some valy = readObject state objy in
  let Some state' = writeObject state objx valy in
  unwrap (writeObject state' objy valx)

endspec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

CopyBytes = spec

import Utilities

(* We specify a C function that copies a byte array to another byte array.
The 1st argument is a pointer to (the first element of) the input array.
The 2nd argument is the length of the input array.
The 3rd argument is a pointer to (the first element of) the output array.
The 4th argument is a pointer to the maximum length of the output array,
which the function updates to the actual length of the output
(in this case equal to the 2nd argument) when the function returns.
If the output array has insufficient room,
this function just sets the output length to 0. *)

op copyBytes
  (state:State, src:Value, srcL:Value, dst:Value, dstL:Value |
    % state and arguments are well-formed:
    wfState? state &&
    wfValue? state src &&
    wfValue? state srcL &&
    wfValue? state dst &&
    wfValue? state dstL &&
    % C types of arguments:
    typeOfValue src = pointer uchar &&
    typeOfValue srcL = uint &&
    typeOfValue dst = pointer uchar &&
    typeOfValue dstL = pointer uint &&
    % 1st and 2nd arguments identify a buffer:
    readBuffer state src srcL ~= None &&
    % 3rd and 4th arguments identify a buffer:
    readBuffer state dst dstL ~= None &&
    % the two buffers do not overlap:
    ~ (buffersOverlap? state src srcL dst dstL))
  : (State | wfState?) =
  let vals = unwrap (readBuffer state src srcL) in
  let n = unwrap (readBufferLength state dstL) in
  let nnpointer (_, object obj) = dstL in
  if n < length vals  % not enough room in output buffer
  then unwrap (writeObject state obj (valueOfMathInt (0, uint)))
  else let Some state' = writeBuffer state dst dstL vals in
       unwrap (writeObject state' obj (valueOfMathInt (length vals, uint)))

(* We would like to refine this specification to a C function of this form:

  void copyBytes(unsigned char *src, unsigned int srcL,
                 unsigned char *dst, unsigned int *dstL) {
    if ( *dstL < srcL ) {
        *dstL = 0;
    } else {
        for (unsigned int i = 0; i < srcL; i++) dst[i] = src[i];
        *dstL = srcL;
    }
  }
*)

endspec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ReverseBytes = spec

import Utilities

(* We specify a C function that reverses a byte buffer in place.
The 1st argument is a pointer to (the first element of) the buffer.
The 2nd argument is the length of the buffer.
Note that op reverse expresses the abstract computation to be performed,
while op reverseBytes links that to the C target function. *)

op reverseBytes
  (state:State, buf:Value, bufL:Value |
    % state and arguments are well-formed:
    wfState? state &&
    wfValue? state buf &&
    wfValue? state bufL &&
    % C types of arguments:
    typeOfValue buf = pointer uchar &&
    typeOfValue bufL = uint &&
    % arguments identify a buffer:
    readBuffer state buf bufL ~= None)
  : (State | wfState?) =
  let oldVals = unwrap (readBuffer state buf bufL) in
  let newVals = reverse oldVals in
  unwrap (writeBuffer state buf bufL newVals)

(* We would like to refine this specification to a C function of this form:

  void reverseBytes(unsigned char *buf, unsigned int bufL) {
      for (unsigned int i = 0; i < bufL / 2; i++) {
          unsigned char tmp = buf[i];
          buf[bufL - i - 1] = buf[i];
          buf[i] = tmp;
      }
  }
*)

endspec
