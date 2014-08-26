(* This file contains a model of C features in the logic of Specware.
This model is used to specify requirements (in Specware) on C programs,
for the puropse of deriving programs from specification via stepwise refinement.
This model only contains the features needed for the current developments.
More features will be added as needed.

This model and its use in specification and refinement
are in the spirit of pop-refinement,
in the sense that features of the target language (C)
are formalized in the logic of Specware,
and requirements are specified in terms of such formalization.
However, in this model the C features are embedded more shallowly,
and a specification in terms of this model may use
a collection of Specware functions to describe (requirements on) target programs
instead of a predicate over (some representation of) target programs.

This C model, like the deep and shallow embeddings,
is based on the C11 standard,
i.e. ISO/IEC 9899, "Information technology - Programming languages - C",
Second edition (2011-12-15).
In the comments in this spec, we reference the ISO standard as '[ISO]',
possibly including (dotted) (sub)section numbers (e.g. '[ISO 6.5.9]')
and paragraph numbers separated by '/' (e.g. '[ISO 6.5.9/2]').
We use ',' to indicate multiple sub-references (e.g. '[ISO 6.5.4/3, 5.2.1]')
and we use '-' to indicate ranges of contiguous sub-references
(e.g. '[ISO 6.5.4-6.5.6]' is the same as '[ISO 6.5.4, 6.5.5, 6.5.6]'). *)

spec

import /Library/General/OptionExt
import /Library/General/Map

(* We define integer values similarly to the C deep and shallow embeddings,
parameterized over the size of bytes, shorts, ints, longs, and long longs. *)

type Uchar % = ...

type Schar % = ...

type Char % = ...

type Ushort % = ...

type Sshort % = ...

type Uint % = ...

type Sint % = ...

type Ulong % = ...

type Slong % = ...

type Ullong % = ...

type Sllong % = ...

(* We define object designators similarly to the C deep embedding, but:
- For now we do not consider structures.
- We only consider outside storage,
  i.e. objects from code that is outside the target program. *)

type OutsideID = | outsideID Nat  % opaque IDs, isomorphic to natural numbers

type ObjectDesignator =
  | outside OutsideID
  | subscript ObjectDesignator * Nat

(* As in the C deep embedding,
it is convenient to model values as carrying their own types.
Thus the following (Specware) type of (C) types is introduced,
which is a slightly simplified version of the one in the C deep embedding
(in this model we do not consider structures and the void type for now). *)

type Type =
  | uchar
  | schar
  | char
  | ushort
  | sshort
  | uint
  | sint
  | ulong
  | slong
  | ullong
  | sllong
  | pointer Type
  | array Type * PosNat

(* Values are defined similarly to the C deep embedding. *)

type Value =
  | uchar Uchar
  | schar Schar
  | char Char
  | ushort Ushort
  | sshort Sshort
  | uint Uint
  | sint Sint
  | ulong Ulong
  | slong Slong
  | ullong Ullong
  | sllong Sllong
  | pointer Type * ObjectDesignator
  | array Type * List1 Value
  | nullpointer Type

op typeOfValue (val:Value): Type =
  case val of
  | uchar _ -> uchar
  | schar _ -> schar
  | char _ -> char
  | ushort _ -> ushort
  | sshort _ -> sshort
  | uint _ -> uint
  | sint _ -> sint
  | ulong _ -> ulong
  | slong _ -> slong
  | ullong _ -> ullong
  | sllong _ -> sllong
  | pointer (ty, _) -> ty
  | array (ty, vals) -> array (ty, length vals)
  | nullpointer ty -> ty

op integerValue? (val:Value): Bool =
  embed? uchar val ||
  embed? schar val ||
  embed? char val ||
  embed? ushort val ||
  embed? sshort val ||
  embed? uint val ||
  embed? sint val ||
  embed? ulong val ||
  embed? slong val ||
  embed? ullong val ||
  embed? sllong val

op mathIntOfValue (val:Value | integerValue? val): Int % = ...
  % same definition as C deep embedding

op valueOfMathInt (i:Int, ty:Type): Value % = ...
  % same definition as C deep embedding (needs subtype)

(* For now we model the state as just consisting of outside storage.
This is the state as seen from outside our target program.
Internal state of the target program
is not explicitly represented in the following type. *)

type State = FiniteMap (OutsideID, Value)

(* The following ops are defined similarly to the C deep embedding.
Op readObject implicitly defines valid object designators,
i.e. the ones that designate objects in the state.
Constructor None models an error.
Op writeObject requires the new value to have the same type as the old value. *)

op readObject (state:State) (obj:ObjectDesignator): Option Value =
  case obj of
  | outside id -> state id
  | subscript (obj0, i) ->
    (case readObject state obj0 of
    | Some (array (_, vals)) -> vals @@ i
    | _ -> None)

op designatesObject? (state:State) (obj:ObjectDesignator): Bool =
  readObject state obj ~= None

op writeObject
  (state:State) (obj:ObjectDesignator) (newVal:Value): Option State =
  case obj of
  | outside id ->
    (case state id of
    | Some oldVal ->
      if typeOfValue newVal = typeOfValue oldVal
      then Some (update state id newVal)
      else None
    | None -> None)
  | subscript (obj0, i) ->
    (case readObject state obj0 of
    | Some (array (ty, oldVals)) ->
      if typeOfValue newVal = ty && i < length oldVals
      then let newVals = update (oldVals, i, newVal) in
           writeObject state obj0 (array (ty, newVals))
      else None
    | _ -> None)

(* A value is well-formed (in a state) iff:
- every array is not empty;
- every array element has the correct type;
- every pointer designates an object in the state of the correct type. *)

op wfValue? (state:State) (val:Value): Bool =
  case val of
  | array (ty, vals) ->
    (fa (i:Nat) i < length vals =>
      (let val = vals @ i in
       typeOfValue val = ty &&  % array element has correct type
       wfValue? state val))  % array element is recursively well-formed
  | pointer (ty, obj) ->
    (case readObject state obj of
    | Some val -> typeOfValue val = ty  % designates object of correct type
    | None -> false)
  | _ -> true  % null pointer and integer values always well-formed

(* A state is well-formed iff all its values are well-formed (in the state). *)

op wfState? (state:State): Bool =
  fa (val:Value) val in? range state => wfValue? state val

(* This model will be extended as needed. *)

endspec
