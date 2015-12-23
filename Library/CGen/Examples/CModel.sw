(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

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

import LibExt

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
- We only consider designators to objects in outside storage,
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
Thus we define a non-null pointer as
either an object designator or something that points one past another object.
The notion of pointer one past an object
is not present in the C deep and shallow embeddings. *)

type NNPointer =
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

op scalarType? (ty:Type): Bool % = ...
  % same definition as C deep embedding

type ScalarType = (Type | scalarType?)

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
  | nnpointer Type * NNPointer
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
  | nnpointer (ty, _) -> ty
  | array (ty, vals) -> array (ty, length vals)
  | nullpointer ty -> ty

op integerValue? (val:Value): Bool =
  integerType? (typeOfValue val)

type IntegerValue = (Value | integerValue?)

op mathIntOfValue (val:IntegerValue): Int % = ...
  % same definition as C deep embedding

op valueOfMathInt (i:Int, ty:Type): Value % = ...
  % same definition as C deep embedding---needs subtype

op int0: IntegerValue = valueOfMathInt (0, sint)

op int1: IntegerValue = valueOfMathInt (1, sint)

op scalarValue? (val:Value): Bool =
  scalarType? (typeOfValue val)

type ScalarValue = (Value | scalarValue?)

op zeroScalar? (val:ScalarValue): Bool % = ...
  % similar definition as C deep embedding

(* Subtypes of values corresponding to the scalar C types in our model.
These are used as argument and return types of Specware ops
that represent C functions.
The predicate toType? defined below can be used
to form further subtypes of pointers to specific types,
e.g. (PointerValue | toType? uchar). *)

type UcharValue = (Value | embed? uchar)

type ScharValue = (Value | embed? schar)

type CharValue = (Value | embed? char)

type UshortValue = (Value | embed? ushort)

type SshortValue = (Value | embed? sshort)

type UintValue = (Value | embed? uint)

type SintValue = (Value | embed? sint)

type UlongValue = (Value | embed? ulong)

type SlongValue = (Value | embed? slong)

type UllongValue = (Value | embed? ullong)

type SllongValue = (Value | embed? sllong)

op pointerValue? (val:Value): Bool =
  embed? nnpointer val || embed? nullpointer val

type PointerValue = (Value | pointerValue?)

op toType? (ty:Type) (val:PointerValue): Bool =
  let pointer ty' = typeOfValue val in ty' = ty

(* We model automatic storage [ISO 6.2.4/5] as
a list of finite maps from identifiers to values.
The list corresponds to the call stack,
with the bottom at the left end the top at the rigth end.
Each element of the list is the block of the corresponding function;
for now we do not model nested blocks, so there is one block per function. *)

type Identifier = String % | ...
  % same definition as C deep embedding (subtype of String)

type AutomaticStorage = List (FiniteMap (Identifier, Value))

(* We model outside storage (i.e. storage form code outside the target program)
as a finite map from outside IDs to values. *)

type OutsideStorage = FiniteMap (OutsideID, Value)

(* For now we model the state as just consisting of
automatic and outside storage. *)

type State =
 {automatic: AutomaticStorage,
  outside: OutsideStorage}

(* The following ops are defined similarly to the C deep embedding.
Op readObject implicitly defines valid object designators,
i.e. the ones that designate objects in the state.
Errors are modeled by None.
Op writeObject requires the new value to have the same type as the old value. *)

op readObject (state:State) (obj:ObjectDesignator): Option Value =
  case obj of
  | outside id -> state.outside id
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
    (case state.outside id of
    | Some oldVal ->
      if typeOfValue newVal = typeOfValue oldVal
      then Some (state << {outside = update state.outside id newVal})
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
  | nnpointer (ty, object obj) ->
    (case readObject state obj of
    | Some val -> typeOfValue val = ty  % designates object of correct type
    | None -> false)
  | nnpointer (ty, past1 obj) ->
    (case readObject state obj of
    | Some val ->  % obj designates an object in the state
      embed? outside obj ||  % top-level object (array or not)
      embed? array val  % or array (top-level or element of an outer array)
    | None -> false)
  | _ -> true  % null pointer and integer values always well-formed

(* A state is well-formed iff
all its values are well-formed (in the state)
and (for now) automatic storage includes no arrays. *)

op wfState? (state:State): Bool =
  % outside storage:
  (fa (val:Value) val in? range state.outside => wfValue? state val) &&
  % automatic storage:
  (fa (i:Nat, val:Value)
    i < length state.automatic && val in? range (state.automatic @ i) =>
    wfValue? state val && ~ (embed? array val))

(* We define integer constants similarly to the C deep embedding.
An integer constant denotes a valid integer value if it fits in an integer type,
otherwise None is used to model an error. *)

type IntegerConstant % = ...

op valueOfIntegerConstant (c:IntegerConstant): Option IntegerValue % = ...
  % same definition as C deep embedding

op integerConstant1: IntegerConstant % = ...

(* We define the unary arithmetic operators + - ~ ! on values
as in the deep and shallow embeddings,
with None modeling
an error due to the application of a value of the wrong type
or results not prescribed by [ISO]. *)

op PLUS_v (val:Value): Option Value % = ...

op MINUS_v (val:Value): Option Value % = ...

op NOT_v (val:Value): Option Value % = ...

op NEG_v (val:Value): Option Value % = ...

(* We define
the multiplicative operators * / % on values,
the bitwise shift operators << >> on values,
the relational operators < > <= >= on values,
the equality operators == != on values,
and the bitwise AND/OR operators & ^ | on values
as in the deep and shallow embeddings. *)

op MUL_v (val1:Value) (val2:Value): Option Value % = ...

op DIV_v (val1:Value) (val2:Value): Option Value % = ...

op REM_v (val1:Value) (val2:Value): Option Value % = ...

op SHL_v (val1:Value) (val2:Value): Option Value % = ...

op SHR_v (val1:Value) (val2:Value): Option Value % = ...

op LT_v (val1:Value) (val2:Value): Option Value % = ...

op GT_v (val1:Value) (val2:Value): Option Value % = ...

op LE_v (val1:Value) (val2:Value): Option Value % = ...

op GE_v (val1:Value) (val2:Value): Option Value % = ...

op EQ_v (val1:Value) (val2:Value): Option Value % = ...

op NE_v (val1:Value) (val2:Value): Option Value % = ...

op AND_v (val1:Value) (val2:Value): Option Value % = ...

op XOR_v (val1:Value) (val2:Value): Option Value % = ...

op IOR_v (val1:Value) (val2:Value): Option Value % = ...

(* We define addition and subtraction on integer values
as in the deep and shallow embeddings,
with None modeling results not prescribed by [ISO]. *)

op ADD_i (val1:IntegerValue) (val2:IntegerValue): Option IntegerValue % = ...

op SUB_i (val1:IntegerValue) (val2:IntegerValue): Option IntegerValue % = ...

(* Adding an integer value to a pointer value
yields a well-defined result under certain conditions [ISO 6.5.6/8,7].
The model of pointer arithmetic below
is not present in the deep or shallow embeddings.
We start with an op that adds a mathematical integer to a non-null pointer.
If ptr designates a top-level non-array object, i must be
either 0 (in which case the pointer is unchanged)
or 1 (in which case the pointer one past the object is returned).
The case of ptr designating a top-level array object
should not occur due to array conversion [ISO 6.3.2.1/3]
(this claim should be proved formally);
the following op treats a top-level array object
the same as a top-level non-array object. *)

op add_int_to_pointer
  (state:State) (i:Int) (ptr:NNPointer): Option NNPointer =
  case ptr of
  % pointer designates object:
  | object obj ->
    (case obj of
    % top-level object:
    | outside id ->
      if i = 0 then Some ptr % no change
      else if i = 1 then Some (past1 obj) % go past object
      else None
    % element of array at index j:
    | subscript (obj0, j) ->
      % get array for length:
      (case readObject state obj0 of
      | Some (array (_, vals)) ->
        let l = length vals in
        % adding i to j stays within the array:
        if 0 <= j + i && j + i < l
        then Some (object (subscript (obj0, j + i)))
        % adding i to j goes one past the array (in this case i > 0):
        else if j + i = l
        then Some (past1 obj0)
        % adding i to j goes outside the array:
        else None
      | _ -> None))
  % pointer is one-past some object:
  | past1 obj ->
    % get the object:
    (case readObject state obj of
    % if the object is an array, get its length:
    | Some (array (_, vals)) ->
      let l = length vals in
      % no change if i = 0:
      if i = 0 then Some ptr
      % adding i to l goes inside the array (in this case i < 0):
      else if 0 <= l + i && l + i < l
      then Some (object (subscript (obj, l + i)))
      % adding i to l stays outside the array:
      else None
    % if the object is not an array, treat as a one-element array:
    | Some val ->
      % no change if i = 0:
      if i = 0 then Some ptr
      % point to object if i = -1:
      else if i = -1 then Some (object obj)
      % every other i is not a valid pointer:
      else None)

(* Addition and subtraction on values.
For now we only allow an integer to be subtracted from a pointer,
but not subtraction between two pointers. *)

op ADD_v (state:State) (val1:Value) (val2:Value): Option Value =
  if integerValue? val1 then
    if integerValue? val2 then
      ADD_i val1 val2
    else
      case val2 of
      | nnpointer (ty, ptr) ->
        (case add_int_to_pointer state (mathIntOfValue val1) ptr of
        | Some ptr' -> Some (nnpointer (ty, ptr'))
        | None -> None)
      | _ -> None
  else % ~ (integerValue? val1)
    case val1 of
    | nnpointer (ty, ptr) ->
      if integerValue? val2 then
        case add_int_to_pointer state (mathIntOfValue val2) ptr of
        | Some ptr' -> Some (nnpointer (ty, ptr'))
        | None -> None
      else
        None
    | _ -> None

op SUB_v (state:State) (val1:Value) (val2:Value): Option Value =
  if integerValue? val1 then
    if integerValue? val2 then
      SUB_i val1 val2
    else
      None
  else % ~ (integerValue? val1)
    case val1 of
    | nnpointer (ty, ptr) ->
      if integerValue? val2 then
        case add_int_to_pointer state (- (mathIntOfValue val2)) ptr of
        | Some ptr' -> Some (nnpointer (ty, ptr'))
        | None -> None
      else
        None
    | _ -> None

(* We define a shallow embedding of (some) C expressions [ISO 6.5].
We consider only side-effect-free expressions for now,
modeling assignments as statements (see below).
Thus, in our model an expression yields as result
either a value or an object designator [ISO 6.5/1].
In the shallow embedding,
a semantic expression is a function from states to expression results,
with errors modeled by None. *)

type ExpressionResult =
  | object ObjectDesignator
  | value Value

type Expression = State -> Option ExpressionResult

(* Lvalue conversion [ISO 6.3.2.1/2] is applied to all operands
except the operands of sizeof, unary &, ++, --,
and the left operand of the . and assignment operators.
Lvalue conversion applies to non-array expressions.
The array conversion specified in [ISO 6.3.2.1/3]
is applied to array expressions that are not operands of sizeof and unary &.
Therefore:
- operands of sizeof and unary & undergo no lvalue or array conversion;
- the left operand of the . and assignment operators undergo array conversion;
- all other operands undergo both lvalue and array conversion.
The following op convertLA applies both lvalue and array conversion,
while the following op convertA applies array convertion only. *)

op convertLA (e:Expression): Expression =
  fn state:State ->
    case e state of
    | Some (object obj) ->
      (case readObject state obj of
      | Some (array (ty, _)) -> % array conversion:
        Some (value (nnpointer (ty, (object (subscript (obj, 0))))))
      | Some val -> % lvalue conversion:
        Some (value val)
      | None -> None)
    | Some (value val) -> Some (value val)
    | None -> None

op convertA (e:Expression): Expression =
  fn state:State ->
    case e state of
    | Some (object obj) ->
      (case readObject state obj of
      | Some (array (ty, _)) -> % array conversion:
        Some (value (nnpointer (ty, (object (subscript (obj, 0))))))
      | Some _ -> Some (object obj) % no value conversion
      | None -> None)
    | Some (value val) -> Some (value val)
    | None -> None

(* A constant expression [ISO 6.5.1/3] yields a value,
which is independent from the state. *)

op constant (c:IntegerConstant): Expression =
  fn state:State ->
    case valueOfIntegerConstant c of
    | Some val -> Some (value val)
    | None -> None

(* In our shallow embedding,
automatic [ISO 6.2.4/5] variables are represented
as identifiers in the automatic storage component of the state. *)

op variable (var:Identifier): Expression =
  fn state:State ->
    if state.automatic = []
    then None % no automatic variables
    else case last state.automatic var of
         | Some val -> Some (value val)
         | None -> None

(* The address operator &
must be applied to an expression that designates an object [ISO 6.5.3.2/1]
(our model does not have function designators for now),
and the object designator is turned into a pointer value [ISO 6.5.3.2/3].
No lvalue or array conversions are applied to the sub-expression
[ISO 6.3.2.1/2-3]. *)

op AMP(*ersand*) (e:Expression): Expression =
  fn state:State ->
    case e state of
    | Some (object obj) ->
      (case readObject state obj of
      | Some val ->
        let ty = typeOfValue val in
        Some (value (nnpointer (ty, object obj)))
      | None -> None)
    | _ -> None

(* The indirection operator *
must be applied to a non-null pointer value [ISO 6.5.3.2/2],
which is turned into an object designator [ISO 6.5.3.2/4],
provided that the pointer points to an object. *)

op STAR (e:Expression): Expression =
  fn state:State ->
    case convertLA e state of
    | Some (value (nnpointer (_, object obj))) -> Some (object obj)
    | _ -> None

(* The unary arithmetic operators and the binary operators defined earlier
are lifted from values to expressions.
The priorities of the infix ..._e ops are chosen
in the same order as in [ISO]. *)

op liftUnary (OP: Value -> Option Value) (e:Expression): Expression =
  fn state:State ->
    case convertLA e state of
    | Some (value val) ->
      (case OP val of
      | Some val' -> Some (value val')
      | None -> None)
    | _ -> None

op PLUS (e:Expression): Expression =
  liftUnary PLUS_v e

op MINUS (e:Expression): Expression =
  liftUnary MINUS_v e

op NOT (e:Expression): Expression =
  liftUnary NOT_v e

op NEG (e:Expression): Expression =
  liftUnary NEG_v e

op liftBinary
  (OP: Value -> Value -> Option Value) (e1:Expression) (e2:Expression)
  : Expression =
  fn state:State ->
    case (convertLA e1 state, convertLA e2 state) of
    | (Some (value val1), Some (value val2)) ->
      (case OP val1 val2 of
      | Some val -> Some (value val)
      | None -> None)
    | _ -> None

op MUL (e1:Expression, e2:Expression) infixl 50: Expression =
  liftBinary MUL_v e1 e1

op DIV (e1:Expression, e2:Expression) infixl 50: Expression =
  liftBinary DIV_v e1 e1

op REM (e1:Expression, e2:Expression) infixl 50: Expression =
  liftBinary REM_v e1 e1

op ADD (e1:Expression, e2:Expression) infixl 49: Expression =
  % we cannot use liftBinary here because ADD_v depends on the state
  fn state:State ->
    case (convertLA e1 state, convertLA e2 state) of
    | (Some (value val1), Some (value val2)) ->
      (case ADD_v state val1 val2 of
      | Some val -> Some (value val)
      | None -> None)
    | _ -> None
    
op SUB (e1:Expression, e2:Expression) infixl 49: Expression =
  % we cannot use liftBinary here because SUB_v depends on the state
  fn state:State ->
    case (convertLA e1 state, convertLA e2 state) of
    | (Some (value val1), Some (value val2)) ->
      (case SUB_v state val1 val2 of
      | Some val -> Some (value val)
      | None -> None)
    | _ -> None

op SHL (e1:Expression, e2:Expression) infixl 48: Expression =
  liftBinary SHL_v e1 e1

op SHR (e1:Expression, e2:Expression) infixl 48: Expression =
  liftBinary SHR_v e1 e1

op LT (e1:Expression, e2:Expression) infixl 47: Expression =
  liftBinary LT_v e1 e1

op GT (e1:Expression, e2:Expression) infixl 47: Expression =
  liftBinary GT_v e1 e1

op LE (e1:Expression, e2:Expression) infixl 47: Expression =
  liftBinary LE_v e1 e1

op GE (e1:Expression, e2:Expression) infixl 47: Expression =
  liftBinary GE_v e1 e1

op EQ (e1:Expression, e2:Expression) infixl 46: Expression =
  liftBinary EQ_v e1 e1

op NE (e1:Expression, e2:Expression) infixl 46: Expression =
  liftBinary NE_v e1 e1

op AND (e1:Expression, e2:Expression) infixl 45: Expression =
  liftBinary AND_v e1 e1

op XOR (e1:Expression, e2:Expression) infixl 44: Expression =
  liftBinary XOR_v e1 e1

op IOR (e1:Expression, e2:Expression) infixl 43: Expression =
  liftBinary IOR_v e1 e1

(* Array subscripting is defined in terms of indirection of pointer addition
[ISO 6.5.2.1]. *)

op SBS (e1:Expression) (e2:Expression) infixl 51: Expression =
  STAR (e1 ADD e2)

(* The logical AND/OR operators && || [ISO 6.5.13, 6.5.14] are non-strict. *)

op LAND (e1:Expression, e2:Expression) infixl 42: Expression =
  fn state:State ->
    case convertLA e1 state of
    | Some (value val1) ->
      if scalarValue? val1 then
        if zeroScalar? val1 then Some (value int0)
        else case convertLA e2 state of
             | Some (value val2) ->
               if scalarValue? val2 then
                 if zeroScalar? val2 then Some (value int0)
                 else Some (value int1)
               else None
             | _ -> None
      else None
    | _ -> None

op LOR (e1:Expression, e2:Expression) infixl 41: Expression =
  fn state:State ->
    case convertLA e1 state of
    | Some (value val1) ->
      if scalarValue? val1 then
        if ~(zeroScalar? val1) then Some (value int1)
        else case convertLA e2 state of
             | Some (value val2) ->
               if scalarValue? val2 then
                 if zeroScalar? val2 then Some (value int0)
                 else Some (value int1)
               else None
             | _ -> None
      else None
    | _ -> None

(* We introduce a state-error monad, with error modeled by None.
Op monadBind enables the use of monadic syntax in Specware. *)

type Monad a = State -> Option (State * a)

op [a,b] monadBind (m: Monad a, f: a -> Monad b): Monad b =
  fn state:State ->
    case m state of
    | Some (state', x) -> f x state'
    | None -> None

op [a] monadReturn (x:a): Monad a =
  fn state:State -> Some (state, x)

op [a] monadError: Monad a =
  fn state:State -> None

(* A statement [ISO 6.8] transforms the state and may generate an error.
As in the deep embedding,
to model the execution of a function call that returns a value,
we regard a statement as also potentially returning a value.
Thus, the type of semantic statements is defined as a synonym of Monad;
this type is more general than needed,
because the type parameter will be always instantiated
to a subtype of Value, or to () for void. *)

type Statement a = Monad a

(* While assignment is an expression in C [ISO 6.5.16],
in our model we consider it a statement
because expressions in our model have no side effects.
Since expressions have no side effects in our model,
we can define compound assignments [ISO 6.5.16.2]
in terms of simple assignments [ISO 6.5.16.1]. *)

op ASG (e1:Expression, e2:Expression) infixl 40: Statement () =
  fn state:State ->
    case (convertA e1 state, convertLA e2 state) of
    | (Some (object obj), Some (value val)) ->
      (case writeObject state obj val of
      | Some state' -> Some (state', ())
      | None -> None)
    | _ -> None

op ASG_MUL (e1:Expression, e2:Expression) infixl 40: Statement () =
  e1 ASG (e1 MUL e2)

op ASG_DIV (e1:Expression, e2:Expression) infixl 40: Statement () =
   e1 ASG (e1 DIV e2)

op ASG_REM (e1:Expression, e2:Expression) infixl 40: Statement () =
   e1 ASG (e1 REM e2)

op ASG_ADD (e1:Expression, e2:Expression) infixl 40: Statement () =
   e1 ASG (e1 ADD e2)

op ASG_SUB (e1:Expression, e2:Expression) infixl 40: Statement () =
   e1 ASG (e1 SUB e2)

op ASG_SHL (e1:Expression, e2:Expression) infixl 40: Statement () =
   e1 ASG (e1 SHL e2)

op ASG_SHR (e1:Expression, e2:Expression) infixl 40: Statement () =
   e1 ASG (e1 SHR e2)

op ASG_AND (e1:Expression, e2:Expression) infixl 40: Statement () =
   e1 ASG (e1 AND e2)

op ASG_XOR (e1:Expression, e2:Expression) infixl 40: Statement () =
   e1 ASG (e1 XOR e2)

op ASG_IOR (e1:Expression, e2:Expression) infixl 40: Statement () =
   e1 ASG (e1 IOR e2)

(* Because expressions are pure in our model,
increment and decrement [ISO 6.5.2.4, 6.5.3.1]
are defined in terms of assignment.
Given that increment and decrement are statements in our model,
the distinction between prefix and postfix is immaterial. *)

op INC (e:Expression): Statement () =
  e ASG_ADD (constant integerConstant1)

op DEC (e:Expression): Statement () =
  e ASG_SUB (constant integerConstant1)

(* We model automatic variable declarations [ISO 6.7] as statement,
even though declarations are not statements [ISO 6.8.2].
This modeling is justified by the fact that, semantically,
an automatic variable declaration
transforms the state and may generate an error.
For now we only allow scalar types for automatic variables.
The declaration specifies the type and name of the variable,
and requires an initializing expression [ISO 6.7.9].
The variable is added to the topmost frame,
unless one with the same name already exists. *)

op DECL (ty:Type) (id:Identifier) (e:Expression): Statement () =
  fn state:State ->
    if scalarType? ty &&
       state.automatic ~= [] &&
       id nin? domain (last state.automatic)
    then case convertLA e state of
         | Some (value val) ->
           if typeOfValue val = ty
           then let newFrame = update (last state.automatic) id val in
                let newAuto = update (state.automatic,
                                      length state.automatic - 1,
                                      newFrame) in
                let newState = state << {automatic = newAuto} in
                Some (newState, ())
           else None
         | _ -> None
    else None

(* In our shallow embedding, we represent
a C function with n >= 0 arguments
as a Specware op of the form

  op f (arg_1:Ty_1) ... (arg_n:Ty_n): Monad Ty

where:
- each Ty_i is one of the Specware types
  UcharValue, ScharValue, CharValue,
  UshortValue, SshortValue,
  UintValue, SintValue,
  UlongValue, SlongValue,
  UllongValue, SllongValue,
  and (PointerValue | totype? ty) for some C type ty:Type;
- Ty is () if the C function returns void,
  otherwise T is one of the types above admissible for the Ty_i's.
The monad captures the fact that
the function transforms the state, may yield an error, and may return a result.

In order to handle all functions of this form uniformly,
for each such f there is another op of the form

  op f' (args: List Value): Monad Ty =
    if length args = n && map typeOfValue args = [ty_1, ..., ty_n]
    then f (args@0) ... (args@(n-1))
    else monadError

where each ty_i:Type is the C type of the values in Ty_i.
In other words, f' wraps f to
take a list of values,
check that they match f's arguments in number and types,
and returns f's result.
Note that f' can be mechanically generated from f.

In our shallow embedding, we represent
calls to f by applying one of two ops to f':
the first op (CALL) models the case in which
the function is called for its side effects only,
and the return value (if any) is discarded;
the second op (ASGCALL) models the case in which
the function's return value is assigned to an lvalue. *)

type WrappedFunction a = List Value -> Monad a

op eval_arguments (eargs: List Expression): Monad (List Value) =
  fn state:State ->
    case eargs of
    | [] -> Some (state, [])
    | earg::eargs ->
      (case convertLA earg state of
      | Some (value arg) ->
        (case eval_arguments eargs state of
        | Some (_, args) -> Some (state, arg::args)
        | None -> None)
      | _ -> None)

op [a] CALL (f': WrappedFunction a) (eargs: List Expression): Statement () =
 {args <- eval_arguments eargs;
  f' args;
  monadReturn ()} % discard any return value

op ASGCALL
  (lvalue:Expression) (f': WrappedFunction Value) (eargs: List Expression)
  : Statement () =
 {assignee <- (fn state:State ->
                case convertA lvalue state of
                | Some result -> Some (state, result)
                | None -> None);
  case assignee of
  | object obj ->
    {args <- eval_arguments eargs;
     retVal <- f' args;
     (fn state:State ->
       case writeObject state obj retVal of
       | Some state' -> Some (state', ())
       | None -> None)}
  | _ -> monadError}

(* The argument values of a function must be incorporated into the state
before they can be operated upon by expressions and statements.
The following op does that:
it takes a list of names for the function's formal parameters
and a list of values for the function's actual arguments,
and pushes a new frame with the arguments associated to the parameters.
The name of this op is motivated by the fact that
it "initializes" a function for execution.
This op does not correspond to any C construct,
but is needed as part of the shallow embedding. *)

op INIT (params:List Identifier | noRepetitions? params)
        (args:List Value)
        : Monad () =
  fn state:State ->
    if length params ~= length args then None
    else let newFrame = fromAssocList (zip (params, args)) in
         Some (state << {automatic = state.automatic ++ [newFrame]}, ())

(* A return statement [ISO 6.8.6.4] with an expression
lifts an expression to a statement that yields a value.
This model does not terminate the execution of a function:
when representing C functions in the shallow embedding,
care must be taken to use op RETURN
only as the last action of a Specware op that represents a C function.
A better approach might be to incorporate return from function into the monad
and propagate it in the same way as errors are propagated;
this possibility may be investigated in the future.
We do not model return statements without expressions;
Specware ops that represent void C functions simply terminate execution. *)

op RETURN (e:Expression): Statement Value =
  fn state:State ->
    case convertLA e state of
    | Some (value val) -> % pop frame and return value
      if state.automatic = [] then None
      else Some (state << {automatic = butLast state.automatic}, val)
    | _ -> None

(* In our model, a return statement without an expression
pops the topmost frame of the stack.
Every shallowly embedded C function returning void
must use this op to properly pop the frame stack.
This could be checked by the code generator. *)

op RETURNv: Statement () =
  fn state:State ->
    if state.automatic = [] then None
    else Some (state << {automatic = butLast state.automatic}, ())

(* We define the if statement [ISO 6.8.4.1], with and without else.
The form with else (i.e. IFELSE) has a polymorphic type,
enabling the use of IFELSE with
both branches that return nothing and branches that return values.
The form without else (e.g. IF) has a monomorphic type,
because the implicit else branch returns nothing. *)

op [a] IFELSE (test:Expression)
              (truebranch:Statement a)
              (falsebranch:Statement a)
              : Statement a =
  fn state:State ->
    case convertLA test state of
    | Some (value val) ->
      if scalarValue? val
      then if zeroScalar? val
           then falsebranch state
           else truebranch state
      else None
    | _ -> None

op IF (test:Expression) (branch:Statement ()): Statement () =
  IFELSE test branch (monadReturn ())

(* A while statement is characterized by
a test (i.e. controlling expression) and a body statement.
The loop is to continue in a state iff
the expression yields a non-zero scalar value in that state. *)

op loopContinues? (test:Expression) (state:State): Bool =
  case convertLA test state of
  | Some (value val) -> scalarValue? val && zeroScalar? val
  | _ -> false

(* A loop invariant is a predicate over states that
is preserved by the loop body
under the assumption that the loop's test is true
and under the assumption that the body does not yield an error. *)

op loopInvariant?
  (test:Expression) (body:Statement ()) (inv: State -> Bool): Bool =
  fa (state:State)
    loopContinues? test state &&
    inv state =>
    (case body state of
    | Some (state', ()) -> inv state'
    | None -> true)

(* A loop terminates in a state iff
execution of the loop starting from that state
eventually leads to an error or to a state where the test is false.
As customary, this can be formalized by saying that
each loop iteration must "decrease" the state
according to some well-founded relation over states.
The following op says when a statement (the body of a loop)
decreases a state according to a well-founded relation.
If the statement generates an error,
the following op returns true
because errors cause termination. *)

op decreasesState?
  (s:Statement ()) (rel:WellFoundedRelation State) (state:State): Bool =
  case s state of
  | Some (state', ()) -> rel (state', state)
  | None -> true

(* If a well-founded relation exists
such that decreaseState? holds
for the body of a loop
for all the states for which loopContinues? holds,
the loop always terminates.
However, this may be an excessively strong condition to show---
we want to generate termination proofs for our generated C code.
It suffices that the loop body decreases states
that satisfy some loop invariant.
A loop terminates in a state if
there exist some well-founded relation and some loop invariant such that
the invariant holds in the state
(and thus holds at every successive iteration, by definition of invariant)
and the body decreases each state
that satisfies the invariant and that passes the test. *)

op loopTerminates? (test:Expression) (body:Statement ()) (state:State): Bool =
  ex (rel: WellFoundedRelation State, inv: State -> Bool)
    inv state &&
    loopInvariant? test body inv &&
    (fa (state':State)
      loopContinues? test state' && decreasesState? body rel state')

(* For now we are only interested in generating terminating C functions,
and in particular terminating loops.
We model non-termination as an error. *)

op WHILE (test:Expression) (body:Statement ()): Statement () =
  fn state:State ->
    if loopTerminates? test body state then
      if loopContinues? test state then
        % execute body and execute the while statement again:
        case body state of
        | Some (state', ()) -> WHILE test body state'
        | None -> None
      else
        % exit loop:
        Some (state, ())
    else % loop does not terminate
      None

(* The do and for statements are defined in terms of the while statement.
In the definition of the following two ops,
we arrange the monadic syntax in a way that resembles C syntax. *)

op DO (body:Statement ()) (test:Expression): Statement () = {
  body;
  WHILE (test)
    body
}

op FOR (init:Statement ())
       (test:Expression)
       (update:Statement ())
       (body: Statement ())
       : Statement () = {
  init;
  WHILE (test) {
    body;
    update
  }
}

endspec
