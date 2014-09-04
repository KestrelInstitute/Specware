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

op scalarType? (ty:Type): Bool % = ...
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

(* We model automatic storage [ISO 6.2.4/5] as
a list of finite maps from identifiers to values.
The list corresponds to the call stack,
with the bottom at the left end the top at the rigth end.
Each element of the list is the block of the corresponding function;
for now we do not model nested blocks, so there is one block per function. *)

type Identifier % = ...
  % same definition as C deep embedding

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
  | pointer (ty, object obj) ->
    (case readObject state obj of
    | Some val -> typeOfValue val = ty  % designates object of correct type
    | None -> false)
  | pointer (ty, past1 obj) ->
    (case readObject state obj of
    | Some val ->  % obj designates an object in the state
      embed? outside obj ||  % top-level object (array or not)
      embed? array val  % or array (top-level or element of an outer array)
    | None -> false)
  | _ -> true  % null pointer and integer values always well-formed

(* A state is well-formed iff all its values are well-formed (in the state)
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
We start with an op that adds a mathematical integer to a pointer.
If ptr designates a top-level non-array object, i must be
either 0 (in which case the pointer is unchanged)
or 1 (in which case the pointer one past the object is returned).
The case of ptr designating a top-level array object
should not occur due to array conversion [ISO 6.3.2.1/3]
(this claim should be proved formally);
the following op treats a top-level array object
the same as a top-level non-array object. *)

op add_int_to_pointer
  (state:State) (i:Int) (ptr:Pointer): Option Pointer =
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
      | pointer (ty, ptr) ->
        (case add_int_to_pointer state (mathIntOfValue val1) ptr of
        | Some ptr' -> Some (pointer (ty, ptr'))
        | None -> None)
      | _ -> None
  else % ~ (integerValue? val1)
    case val1 of
    | pointer (ty, ptr) ->
      if integerValue? val2 then
        case add_int_to_pointer state (mathIntOfValue val2) ptr of
        | Some ptr' -> Some (pointer (ty, ptr'))
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
    | pointer (ty, ptr) ->
      if integerValue? val2 then
        case add_int_to_pointer state (- (mathIntOfValue val2)) ptr of
        | Some ptr' -> Some (pointer (ty, ptr'))
        | None -> None
      else
        None
    | _ -> None

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

(* A constant expression [ISO 6.5.1/3] yields a value,
which is independent from the state. *)

op constant (c:IntegerConstant): Expression =
  fn state:State ->
    case valueOfIntegerConstant c of
    | Some val -> Some (value val)
    | None -> None

(* In our shallow embedding,
automatic [ISO 6.2.4/5] variables may be represented
as identifiers in the automatic storage component of the state,
but also as Specware bound variables
(e.g. op arguments, let-bound variables, monad-bound variables).
Op svariable captures the first case ('s' for 'state');
identifiers are looked up only in the top frame, if any.
Op bvariable captures the second case ('b' for 'bound');
it takes a value as argument
because that is the Specware type of the bound variables. *)

op svariable (var:Identifier): Expression =
  fn state:State ->
    if state.automatic = []
    then None % no automatic variables
    else case last state.automatic var of
         | Some val -> Some (value val)
         | None -> None

op bvariable (var:Value): Expression =
  fn state:State -> Some (value var)

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
        Some (value (pointer (ty, object obj)))
      | None -> None)
    | _ -> None

(* The indirection operator *
must be applied to a pointer value [ISO 6.5.3.2/2],
which is turned into an object designator [ISO 6.5.3.2/4],
provided that the pointer points to an object. *)

op STAR (e:Expression): Expression =
  fn state:State ->
    case (convertArray (convertLvalue e)) state of
    | Some (value (pointer (_, object obj))) -> Some (object obj)
    | _ -> None

(* The unary arithmetic operators and the binary operators defined earlier
are lifted from values to expressions.
The priorities of the infix ..._e ops are chosen
in the same order as in [ISO]. *)

op liftUnary (OP: Value -> Option Value) (e:Expression): Expression =
  fn state:State ->
    case (convertArray (convertLvalue e)) state of
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
    case ((convertArray (convertLvalue e1)) state,
          (convertArray (convertLvalue e2)) state) of
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
    case ((convertArray (convertLvalue e1)) state,
          (convertArray (convertLvalue e2)) state) of
    | (Some (value val1), Some (value val2)) ->
      (case ADD_v state val1 val2 of
      | Some val -> Some (value val)
      | None -> None)
    | _ -> None
    
op SUB (e1:Expression, e2:Expression) infixl 49: Expression =
  % we cannot use liftBinary here because SUB_v depends on the state
  fn state:State ->
    case ((convertArray (convertLvalue e1)) state,
          (convertArray (convertLvalue e2)) state) of
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
    case (convertArray (convertLvalue e1)) state of
    | Some (value val1) ->
      if scalarValue? val1 then
        if zeroScalar? val1 then Some (value int0)
        else case (convertArray (convertLvalue e2)) state of
             | Some (value val2) ->
               if scalarValue? val2 then
                 if zeroScalar? val2 then Some (value int0)
                 else Some (value int1)
               else None
             | _ -> None
      else None
    | _ -> None

op LOR (e1:Expression, e2:Expression) infixl 42: Expression =
  fn state:State ->
    case (convertArray (convertLvalue e1)) state of
    | Some (value val1) ->
      if scalarValue? val1 then
        if ~(zeroScalar? val1) then Some (value int1)
        else case (convertArray (convertLvalue e2)) state of
             | Some (value val2) ->
               if scalarValue? val2 then
                 if zeroScalar? val2 then Some (value int0)
                 else Some (value int1)
               else None
             | _ -> None
      else None
    | _ -> None

% TODO as statements:
% - function call
% - increment/decrement?
% - simple assignment
% - compound assignment?
% - automatic variable declaration
% - selection -- if
% - iteration -- while do-while for
% - jump -- return

%%%%%%%%%% IN PROGRESS...

%%%%%%%%%% RE-INTRODUCE AS NEEDED:

% (* We introduce a state-error monad for C, with error modeled by None.
% Op monadBind enables the use of monadic syntax in Specware. *)

% type C a = State -> Option (State * a)

% op [a,b] monadBind (comp1: C a, comp2: a -> C b): C b =
%   fn state:State ->
%     case comp1 state of
%     | Some (state', x) -> comp2 x state'
%     | None -> None

% (* Lift constants and functions to C monad. *)

% op [a] conC (x:a): C a =  % monad return
%   fn state:State -> Some (state, x)

% op [a,b] funC (f: a -> b): a -> C b =
%   fn x:a -> fn state:State -> Some (state, f x)

% (* Move state out of and into the C monad. *)

% op outC: C State =
%   fn state:State -> Some (state, state)

% op inC (state:State): C () =
%   fn state':State -> Some (state, ())

% (* Monadic versions of readObject and writeObject. *)

% op readObjectC (obj:ObjectDesignator): C Value =
%   fn state:State ->
%     case readObject state obj of
%     | Some val -> Some (state, val)
%     | None -> None

% op writeObjectC (obj:ObjectDesignator) (newVal:Value): C () =
%   fn state:State ->
%     case writeObject state obj newVal of
%     | Some state' -> Some (state', ())
%     | None -> None

endspec
