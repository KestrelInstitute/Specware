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

(* Pointers in our C model include object designators,
which have well-defined semantics in [ISO] and which can be dereferenced.
Pointer arithmetic may yield well-defined pointers that also include
one past the last element of an array object
or one past an object that is not an element of an array object [ISO 6.5.6/8].
Such pointers cannot be dereferenced [ISO 6.5.6/8],
but have well-defined arithmetic [ISO 6.5.6/8-9].
Thus we define a pointer as
either an object designator or something that points one past another object.
This notion is not present in the C deep or shallow embeddings. *)

type Pointer =
  | object ObjectDesignator
  | past1 ObjectDesignator

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

op integerType? (ty:Type): Bool % = ...
  % same definition as C deep embedding

(* Values are defined similarly to the C deep embedding.
Note that arrays are never empty [ISO 6.2.5/20]. *)

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
  | pointer Type * Pointer
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
  integerType? (typeOfValue val)

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
- every array element has the correct type;
- every pointer that is an object designator
  designates an object in the state of the correct type;
- every one-past pointer has an object designator that
  either designates a top-level non-array
  or designates an array
  (i.e. it does not designate an element of an array that is not an array). *)

op wfValue? (state:State) (val:Value): Bool =
  case val of
  | array (ty, vals) ->
    (fa (i:Nat) i < length vals =>
      (let val = vals @ i in
       typeOfValue val = ty &&  % array element has correct type
       wfValue? state val))  % array element is recursively well-formed
  | pointer (ty, object obj) ->
    (case readObject state obj of
    | Some val -> typeOfValue val = ty  % designates object of correct type
    | None -> false)
  | pointer (ty, past1 obj) ->
    (case readObject state obj of
    | Some val ->  % obj designates an object in the state
      embed? outside obj ||  % top-level object (array or not)
      embed? array val  % or array (top-level or element of an outer array
    | None -> false)
  | _ -> true  % null pointer and integer values always well-formed

(* A state is well-formed iff all its values are well-formed (in the state). *)

op wfState? (state:State): Bool =
  fa (val:Value) val in? range state => wfValue? state val

(* We introduce a state-error monad for C, with error modeled by None.
Op monadBind enables the use of monadic syntax in Specware. *)

type C a = State -> Option (State * a)

op [a,b] monadBind (comp1: C a, comp2: a -> C b): C b =
  fn state:State ->
    case comp1 state of
    | Some (state', x) -> comp2 x state'
    | None -> None

(* Lift constants and functions to C monad. *)

op [a] conC (x:a): C a =  % monad return
  fn state:State -> Some (state, x)

op [a,b] funC (f: a -> b): a -> C b =
  fn x:a -> fn state:State -> Some (state, f x)

(* Move state out of and into the C monad. *)

op outC: C State =
  fn state:State -> Some (state, state)

op inC (state:State): C () =
  fn state':State -> Some (state, ())

(* Monadic versions of readObject and writeObject. *)

op readObjectC (obj:ObjectDesignator): C Value =
  fn state:State ->
    case readObject state obj of
    | Some val -> Some (state, val)
    | None -> None

op writeObjectC (obj:ObjectDesignator) (newVal:Value): C () =
  fn state:State ->
    case writeObject state obj newVal of
    | Some state' -> Some (state', ())
    | None -> None

(* We define a shallow embedding of (some) C expressions [ISO 6.5].
We consider side-effect-free expressions for now,
modeling assignments as non-expressions (e.g. as statements).
Thus, in our model an expression yields a value or an object designator
[ISO 6.5/1]. *)

(* An expression that yields a value (and not an object designator)
is sometimes called 'rvalue'---see footnote 64 in [ISO 6.3.2.1/1].
Thus, the semantics of an rvalue is a function from states to values
(using Option to model errors).
This is the definition of
the type of semantic rvalues in the shallow embedding. *)

type Rvalue = State -> Option Value

(* An lvalue is an expression
that (in our model) yields an object designator [ISO 6.3.2.1/1].
An object designator provides
the capability to read from and write to the object.
Thus, the semantics of an lvalue can be defined as a pair of functions:
- a "getter" that maps a state to the value of the designated object
  (using Option to model errors);
- a "setter" that maps a state and a value to a new state
  where the value of the designated object has been updated
  (using Option to model errors).
This is the definition of
the type of semantics lvalues in the shallow embedding. *)

type Lvalue =
  {get: State -> Option Value,
   set: State -> Value -> Option State}

% IN PROGRESS...

endspec
