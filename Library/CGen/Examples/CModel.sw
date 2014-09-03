(* This file contains a model of C features in the logic of Specware.
This model is used to specify requirements (in Specware) on C programs,
for the purpose of deriving programs from specification via stepwise refinement.
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
This notion is not present in the C deep and shallow embeddings. *)

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
  % same definition as C deep embedding---needs subtype

(* For now we model the state as just consisting of outside storage.
This is the state as seen from outside our target program.
The internal state of the target program
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
Thus, in our model an expression yields as result
either a value or an object designator [ISO 6.5/1].
In the shallow embedding,
a semantic expression is a function from states to expression results,
with errors modeled by None. *)

type ExpressionResult =
  | object ObjectDesignator
  | value Value

type Expression = State -> Option ExpressionResult

(* For most operators, a non-array object designator yielded by a sub-expression
is converted to the value stored in the designated object [ISO 6.3.2.1/2].
The following op performs this conversion
if the expression yields a non-array object designator,
otherwise it leaves the expression result unchanged;
so this op can be always safely applied
to sub-expressions of operands that require this conversion. *)

op convertLvalue (e:Expression): Expression =
  fn state:State ->
    case e state of
    | Some (object obj) ->
      (case readObject state obj of
      | Some val ->
        if embed? array val
        then e state % no conversion for arrays
        else Some (value val) % convert
      | None -> None) % error, no object designated
    | Some (value _) -> e state % no conversion if already a value
    | Nonve -> None % propagate error

(* For most operators, an array sub-expression
is converted to a pointer to the first element of the array [ISO 6.3.2.1/3].
The following op performs this conversion
if the expression yields an object designator to an array,
otherwise it leaves the expression result unchanged;
so this op can be always safely applied
to sub-expressions of operands that require this conversion.
Note that, when constructing well-formed C expressions,
the following op is never applied to an expression that yields an array value
(vs. an array object designator);
this claim should be proved formally. *)

op convertArray (e:Expression): Expression =
  fn state:State ->
    case e state of
    | Some (object obj) ->
      (case readObject state obj of
      | Some val ->
        (case typeOfValue val of
        | array (ty, _) ->
          Some (value (pointer (ty, (object (subscript (obj, 0)))))) % convert
        | _ -> e state) % no conversion for non-arrays
      | None -> None) % error, no object is designated
    | Some (value _) -> e state % this case should never occur
    | None -> None % propagate error

(* We define integer constants similarly to the C deep embedding.
An integer constant denotes a valid integer value if it fits in an integer type,
otherwise None is used to model an error. *)

type IntegerConstant % = ...

op valueOfIntegerConstant
  (c:IntegerConstant): Option (Value | integerValue?) % = ...
  % same definition as C deep embedding

(* A constant expression [ISO 6.5.1/3] yields a value,
which is independent from the state. *)

op constant (c:IntegerConstant): Expression =
  fn state:State ->
    case valueOfIntegerConstant c of
    | Some val -> Some (value val)
    | None -> None

(* Automatic [ISO 6.2.4/5] variables in the shallow embedding
may be represented by
(let-bound or monad-bound) Specware variables of type Value.
The following op lifts a value to an expression,
so it can be applied to any value,
but it is meant to be applied to Specware variables of type Value,
which motivates the name of the op.
The expression does not depend on the state because, as remarked earlier,
type State captures the state outside the target program,
while automatic variables are inside the target program.
The expression never yields an error
because the variable is always in scope by construction.
See [ISO 6.5.1/2]. *)

op variable (var:Value): Expression =
  fn state:State -> Some (value var)

(* The address operator &
must be applied to an expression that designates an object [ISO 6.5.3.2/1]
(our model does not have function designators for now),
and the object designator is turned into a pointer value [ISO 6.5.3.2/3].
No lvalue or array conversions are applied to the sub-expression
[ISO 6.3.2.1/2-3]. *)

op amp(*ersand*) (e:Expression): Expression =
  fn state:State ->
    case e state of
    | Some (object obj) ->
      (case readObject state obj of
      | Some val ->
        let ty = typeOfValue val in
        Some (value (pointer (ty, object obj)))
      | None -> None)
    | _ -> None

(* The indirection operator *
must be applied to a pointer value [ISO 6.5.3.2/2],
which is turned into an object designator [ISO 6.5.3.2/4],
provided that the pointer points to an object. *)

op star (e:Expression): Expression =
  fn state:State ->
    case (convertArray (convertLvalue e)) state of
    | Some (value (pointer (_, object obj))) -> Some (object obj)
    | _ -> None

% IN PROGRESS...

endspec
