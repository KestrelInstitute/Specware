(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

C qualifying spec

%import /Library/General/TwosComplementNumber
import /Library/Structures/Data/TwosComplementNumber
import /Library/Structures/Data/IMap
import /Library/General/OptionExt


(* FIXME HERE NOW: values should *not* contain their types, because types should
not exist dynamically; instead, types should only exist statically, in
expressions. Conversions between types should be handled by having both the
"from" and "to" types in the expression, rather than looking up the "from" type
in the dynamic value being converted. *)


%section (* Introduction *)

(* We formalize a subset of C, which we will incrementally extend as needed.

Our formalization is based on the C11 standard, i.e. ISO/IEC 9899, "Information
technology - Programming languages - C", Second edition (2011-12-15).

In the comments in this spec, we reference the ISO standard as '[ISO]', possibly
including (dotted) (sub)section numbers (e.g. '[ISO 6.5.9]') and paragraph
numbers separated by '/' (e.g. '[ISO 6.5.9/2]'). We use ',' to indicate multiple
sub-references (e.g. '[ISO 6.5.4/3, 5.2.1]') and we use '-' to indicate ranges
of contiguous sub-references (e.g. '[ISO 6.5.4-6.5.6]' is the same as '[ISO
6.5.4, 6.5.5, 6.5.6]'). *)


%section (* Environment *)

(* Some aspects of the C language depend on the environment [ISO 5], i.e. on the
implementation. From the point of view of our formalized C subset, we partition
these environmental aspects into three groups:

1. aspects for which our formalization makes a specific choice out of the ones
allowed by [ISO];

2. aspects for which our formalization allows all the choices allowed by [ISO];

3. aspects for which our formalization neither makes a specific choice nor
allows all the choices, but instead tags as 'non-standard'.

The significance of the first group is that our formal model captures only those
implementations of the C language that make the same choices for the aspects in
the group. The significance of the second group is that our formal model can be
instantiated to capture different implementations that make different choices
for the aspects in the group. The third group consists of run-time behaviors
that are not prescribed by [ISO] (e.g. the behavior of signed addition when the
true result is not representable): our formalization denotes such behaviors as
'non-standard', and anything that depends on those behaviors is denoted as
'non-standard' as well.

The following subsections describe our choices for the aspects in the first
group and introduce underspecified Specware constants to capture the aspects in
the second group. The third group is handled later, in the part of the
formalization that formalizes the semantics. *)


%subsection (* Character sets *)

(* We assume that both the source and the execution character sets [ISO 5.2.1]
consist of the 128 ASCII characters. These are all members of the basic
character set, which coincides with the extended character set in our model,
i.e. there are no extended characters in our model. *)


%subsection (* Identifier non-digits *)

(* As formalized later, we assume that an identifier non-digit [ISO 6.4.2.1] can
only be a letter [ISO 5.2.1/4] or an underscore. In other words, we exclude
universal character names and "other implementation-defined characters". *)


%subsection (* Bytes and the unsigned char type *)

(* The number of bits that comprise a byte [ISO 3.6] is expressed by CHAR_BIT
[ISO 5.2.4.2.1/1], which must be at least 8. [ISO 5.2.4.2.1/2] constrains
UCHAR_MAX [ISO 5.2.4.2.1/1] to be 2^CHAR_BIT-1, and [ISO 6.2.6.1/3] constrains
unsigned char objects to be represented using a pure binary notation, i.e. to
range from 0 to 2^CHAR_BIT-1. Thus, unsigned char objects are always bytes in C,
and every object consists of 1 or more bytes [ISO 6.2.6.1/4].

In our formalization, we assume that bytes consist of 8 bits (as is common),
i.e. that CHAR_BIT is 8. Consequently, UCHAR_MAX is 255. *)

op CHAR_BIT : Nat = 8

op UCHAR_MAX : Nat = 2 ** CHAR_BIT - 1

theorem UCHAR_MAX_VAL is
  UCHAR_MAX = 255


%subsection (* The signed char type *)

(* The sizeof operator [ISO 6.5.3.4], which returns the size in bytes of its
operand [ISO 6.5.3.4/2], must return 1 when applied to a char, unsigned char, or
signed char object [ISO 6.5.3.4/4]. This implies that signed char objects
consist, like unsigned char objects, of 1 byte, which in our formalization is 8
bits. [ISO 6.2.6.2/2] says that a signed char object must include a sign bit and
that the other (7) bits are divided among value and padding bits. The constraint
that SCHAR_MAX is at least +127 [ISO 5.2.4.2.1/1] implies that all the 7 bits
must be value bits (otherwise it would not be possible to represent +127). Since
no number greater than 127 can be represented in 7 bits, SCHAR_MAX must be
+127. *)

op SCHAR_MAX : Nat = 127

(* There is still a choice on SCHAR_MIN, depending on whether negative signed
char objects are represented as sign and magnitude, two's complement, or one's
complement [ISO 6.2.6.2/2]. In the first and third case, SCHAR_MIN has to be
-127; in the second case, SCHAR_MIN has to be -128. We assume a two's complement
representation. *)

op SCHAR_MIN : Int = -128


%subsection (* The plain char type *)

(* Plain char objects have the same range and representation as either signed
char objects or unsigned char objects [ISO 6.2.5/15]. We leave this choice open
in our model, by introducing an uninterpreted boolean constant that is true iff
plain char objects are signed. We also define its negation, for convenience. *)

op plainCharsAreSigned : Bool

op plainCharsAreUnsigned : Bool = ~ plainCharsAreSigned

(* The values of CHAR_MIN and CHAR_MAX [ISO 5.2.4.2.1/2] depend on the flag just
introduced. *)

op CHAR_MIN : Int = if plainCharsAreSigned then SCHAR_MIN else 0

op CHAR_MAX : Nat = if plainCharsAreSigned then SCHAR_MAX else UCHAR_MAX

(* Note that, regardless of whether plain chars are signed or unsigned, each of
the 128 ASCII characters (which, as stated earlier, constitute our basic
character set) can be stored into a (plain) char and the resulting value is
non-negative [ISO 6.2.5/3]. *)


%subsection (* The other integer types *)

(* The representation of an unsigned integer type other than unsigned char, must
consist of N value bits plus 0 or more padding bits, yielding a range of values
between 0 and 2^N-1 [ISO 6.2.6.2/1]. This constrains the U..._MAX value of each
unsigned integer type to be 2^N-1. We assume that no padding bits are used, so
that the representation consists of exactly N (value) bits. Since every object
(including integers) has a size in bytes [ISO 6.5.3.4/2, 6.2.6.1/4], N must be a
multiple of CHAR_BIT, i.e. 8 as defined above.

We leave the exact number of bits N open, by introducing the following
sizeof_... underspecified constants which express the size, in bytes, of each
unsigned integer type other than unsigned char (which we have covered earlier).
So, for each unsigned integer type, the number of bits N is CHAR_BIT times the
sizeof_... constants introduced below. For convenience, we also define ..._bit
constants that express the size in bits of the types.

The minimum magnitude constraints on the U..._MAX values given in [ISO
5.2.4.2.1/1] correspond to the minimum magnitude constraints on the sizeof_...
constants captured by the axioms below. *)

op sizeof_short : Nat
op sizeof_int   : Nat
op sizeof_long  : Nat
op sizeof_llong : Nat

op short_bits : Nat = sizeof_short * CHAR_BIT
op   int_bits : Nat = sizeof_int   * CHAR_BIT
op  long_bits : Nat = sizeof_long  * CHAR_BIT
op llong_bits : Nat = sizeof_llong * CHAR_BIT

axiom min_sizeof_short is  sizeof_short >= 2
axiom min_sizeof_int   is  sizeof_int   >= 2
axiom min_sizeof_long  is  sizeof_long  >= 4
axiom min_sizeof_llong is  sizeof_llong >= 8

theorem min_short_bits is  short_bits >= 16
theorem min_int_bits   is    int_bits >= 16
theorem min_long_bits  is   long_bits >= 32
theorem min_llong_bits is  llong_bits >= 64

op  USHRT_MAX : Nat = 2 ** short_bits - 1
op   UINT_MAX : Nat = 2 **   int_bits - 1
op  ULONG_MAX : Nat = 2 **  long_bits - 1
op ULLONG_MAX : Nat = 2 ** llong_bits - 1

theorem min_USHRT_MAX  is  USHRT_MAX  >= 2 ** 16 - 1
theorem min_UINT_MAX   is  UINT_MAX   >= 2 ** 16 - 1
theorem min_ULONG_MAX  is  ULONG_MAX  >= 2 ** 32 - 1
theorem min_ULLONG_MAX is  ULLONG_MAX >= 2 ** 64 - 1

(* The signed integer types use the same amount of storage as their unsigned
counterparts [ISO 6.2.5/6]. Thus, the sizeof_... and ..._bits constants
introduced above also apply to the signed integer types, not only the unsigned
ones. This is why the names of those constants make no reference to
(un)signedness.

Similarly to the signed char type, we assume that the other signed integer types
use a two's complement representation with no padding bits [ISO 6.2.6.2/2].
Thus, the sizeof_... constants determine the following values for the ..._MIN
and ..._MAX limits of the signed integer types [ISO 5.2.4.2.1/1]. *)

op  SHRT_MIN : Int = - (2 ** (short_bits - 1))
op   INT_MIN : Int = - (2 ** (  int_bits - 1))
op  LONG_MIN : Int = - (2 ** ( long_bits - 1))
op LLONG_MIN : Int = - (2 ** (llong_bits - 1))

op  SHRT_MAX : Nat =   2 ** (short_bits - 1) - 1
op   INT_MAX : Nat =   2 ** (  int_bits - 1) - 1
op  LONG_MAX : Nat =   2 ** ( long_bits - 1) - 1
op LLONG_MAX : Nat =   2 ** (llong_bits - 1) - 1

theorem min_SHRT_MIN  is   SHRT_MIN <= - (2 ** 15)
theorem min_INT_MIN   is    INT_MIN <= - (2 ** 15)
theorem min_LONG_MIN  is   LONG_MIN <= - (2 ** 31)
theorem min_LLONG_MIN is  LLONG_MIN <= - (2 ** 63)

theorem min_SHRT_MAX  is   SHRT_MAX >=    2 ** 15 - 1
theorem min_INT_MAX   is    INT_MAX >=    2 ** 15 - 1
theorem min_LONG_MAX  is   LONG_MAX >=    2 ** 31 - 1
theorem min_LLONG_MAX is  LLONG_MAX >=    2 ** 63 - 1

(* There are inclusion constraints among the ranges of the integer types [ISO
6.2.5/8], determined by the integer conversion ranks [ISO 6.3.1.1/1]. Given our
assumptions and constants introduced above, these inclusion constraints are
expressed via the following axioms on the sizeof_... constants. *)

axiom sizeof_short_int  is  sizeof_short <= sizeof_int
axiom sizeof_int_long   is  sizeof_int   <= sizeof_long
axiom sizeof_long_llong is  sizeof_long  <= sizeof_llong


%section (* Syntax *)

(* We only formalize abstract syntax, not concrete syntax. *)


%subsection (* Identifiers *)

(* As stated earlier, we assume that an identifier non-digit [ISO 6.4.2.1] can
only be a letter or an underscore. Thus, an identifier [ISO 6.4.2.1] in our C
subset is a non-empty sequence of letters (upper and lower case), digits, and
underscores, starting with a letter or an underscore. Note that the first 128
characters in Specware are the ASCII characters, matching our assumption, stated
earlier, that the source character set in our C subset consists of the 128 ASCII
characters.

Identifiers (as defined in [ISO 6.4.2.1/1]) that are keywords [ISO 6.4.1] become
keywords after preprocessing [ISO 6.4.2.1/4]. So the predicate ppIdentifier?
defined below captures preprocessing identifiers [ISO 6.4/1], while the
predicate identifier? and the type Identifier capture identifiers after
preprocessing. *)

op digit? (ch:Char) : Bool =
  isNum ch  % 0-9

op nonDigit? (ch:Char) : Bool =
  isAlpha ch || ch = #_  % A-Z, a-z, _

op identifierNonDigit? (ch:Char) : Bool =
  nonDigit? ch

op ppIdentifier? (str:String) : Bool =
  let chars = explode str in
  nonEmpty? chars &&
  forall? (fn c -> identifierNonDigit? c || digit? c) chars &&
  ~ (digit? (head chars))

op keywords : List String =
  ["auto",
   "break",
   "case",
   "char",
   "const",
   "continue",
   "default",
   "do",
   "double",
   "else",
   "enum",
   "extern",
   "float",
   "for",
   "goto",
   "if",
   "inline",
   "int",
   "long",
   "register",
   "restrict",
   "return",
   "short",
   "signed",
   "sizeof",
   "static",
   "struct",
   "switch",
   "typedef",
   "union",
   "unsigned",
   "void",
   "volatile",
   "while",
   "_Alignas",
   "_Alignof",
   "_Atomic",
   "_Bool",
   "_Complex",
   "_Generic",
   "_Imaginary",
   "_Noreturn",
   "_Static_assert",
   "_Thread_local"]

op identifier? (str:String) : Bool =
  ppIdentifier? str && str nin? keywords

type Identifier = (String | identifier?)


%subsection (* Types *)

(* Our C subset features the following types [ISO 6.2.5]: the standard signed
and unsigned integer types, the (plain) char type, structure types, pointer
types, array types, and the void type. Each of the signed/unsigned
short/int/long/longlong types can be denoted via multiple, equivalent
combinations of type specifiers [ISO 6.7.2]; even though some of these types may
have identical representations in an implementation, they are nevertheless
different types [ISO 6.2.5/14]. A structure type is denoted by its optional tag,
where a None tag indicates an anonymous struct, as well as the names and types
of its members [ISO 6.2.5/20]. In order to handle recursive struct types, we
allow the member types in a struct type with tag S to refer to that whole struct
type just by the name S, without containing the member types of S; e.g., the
type T_struct (Some "S", ("f", T_pointer (T_structName "S"))) defines a struct
type for a simple linked list. An array type includes the number of elements
[ISO 6.2.5/20]; our C subset only includes array types with known size. *)

(* FIXME: things might be easier if we separated object vs function types... *)

type Type =
  | T_char                        %          char
  | T_uchar                       % unsigned char
  | T_schar                       %   signed char
  | T_ushort                      % unsigned short
  | T_sshort                      %   signed short
  | T_uint                        % unsigned int
  | T_sint                        %   signed int
  | T_ulong                       % unsigned long
  | T_slong                       %   signed long
  | T_ullong                      % unsigned long long
  | T_sllong                      %   signed long long
  | T_struct                      % structure
      (Option Identifier *
         {l:List (Identifier * Type) | noRepetitions? (unzip l).1})
  | T_structName Identifier       % recursive reference to a structure type
  | T_pointer Type                % pointer (to type)
  | T_array   Type * Nat          % array (of type of size)
  | T_void                        % void
  | T_function (Type * List Type) % function (with return type and argument types)

%% StructType and StructMemberTypes are unfolded in Type because of Isabelle's restrictions on type recursion
type StructMemberTypes = {l:List (Identifier * Type) | noRepetitions? (unzip l).1}
type StructType = Option Identifier * StructMemberTypes
type FunType = Type * List Type

(* The following are the standard signed integer types [ISO 6.2.5/4] *)

op standardSignedIntegerType? (ty:Type) : Bool =
  ty = T_schar || ty = T_sshort || ty = T_sint || ty = T_slong || ty = T_sllong

(* Our C subset has no extended signed integer types [ISO 6.2.5/4], so the
signed integer types [ISO 6.2.5/4] coincide with the standard signed integer
types. *)

op signedIntegerType? (ty:Type) : Bool = standardSignedIntegerType? ty

(* The following are the standard unsigned integer types [ISO 6.2.5/6]. *)

op standardUnsignedIntegerType? (ty:Type) : Bool =
  ty = T_uchar || ty = T_ushort || ty = T_uint || ty = T_ulong || ty = T_ullong

(* Our C subset has no extended unsigned integer types [ISO 6.2.5/6], so the
unsigned integer types [ISO 6.2.5/6] coincide with the standard unsigned integer
types. *)

op unsignedIntegerType? (ty:Type) : Bool =
  standardUnsignedIntegerType? ty

(* The following are the standard integer types [ISO 6.2.5/7]. *)

op standardIntegerTypes? (ty:Type) : Bool =
  standardSignedIntegerType? ty || standardUnsignedIntegerType? ty

(* The following are the basic types [ISO 6.2.5/14]. Our C subset has no
floating types. *)

op basicType? (ty:Type) : Bool =
  ty = T_char || signedIntegerType? ty || unsignedIntegerType? ty

(* The following are the character types [ISO 6.2.5/15]. *)

op characterType? (ty:Type) : Bool =
  ty = T_char || ty = T_uchar || ty = T_schar

(* The following are the integer types [ISO 6.2.5/17]. Our C subset has no
enumerated types. *)

op integerType? (ty:Type) : Bool =
  ty = T_char || signedIntegerType? ty || unsignedIntegerType? ty

(* The following are the real types [ISO 6.2.5/17]. Our C subset has no floating
types. *)

op realType? (ty:Type) : Bool =
  integerType? ty

(* The following are the arithmetic types [ISO 6.2.5/18]. Our C subset has no
floating types. *)

op arithmeticType? (ty:Type) : Bool =
  integerType? ty

(* The following are the derived types [ISO 6.2.5/20]. Our C subset has no
union and no atomic types. *)

op derivedType? (ty:Type) : Bool =
  embed? T_struct ty || embed? T_pointer ty || embed? T_array ty || embed? T_function ty

(* The following are the scalar types [ISO 6.2.5/21]. *)

op scalarType? (ty:Type) : Bool =
  arithmeticType? ty || embed? T_pointer ty

(* The following are the aggregate types [ISO 6.2.5/21]. *)

op aggregateType? (ty:Type) : Bool =
  embed? T_struct ty || embed? T_array ty

(* In our C subset, all types are complete types [ISO 6.2.5/1] except void [ISO
6.2.5/19]. *)

op completeType? (ty:Type) : Bool =
  ty ~= T_void

(* The following predicates are not explicitly defined in [ISO 6.2.5] but are
useful in our formalization. *)

op shortType? (ty:Type) : Bool =
  ty = T_sshort || ty = T_ushort

op intType? (ty:Type) : Bool =
  ty = T_sint || ty = T_uint

op longType? (ty:Type) : Bool =
  ty = T_slong || ty = T_ulong

op llongType? (ty:Type) : Bool =
  ty = T_sllong || ty = T_ullong

(* Whether ty is a function pointer type *)
op functionPointerType? (ty:Type) : Bool =
  case ty of
    | T_pointer (T_function _) -> true
    | _ -> false

op pointerType? (tp:Type) : Bool = embed? T_pointer tp

(* Whether tp is a complete object type, i.e., it is not a void or function
type. This also ensures that the type is well-formed, meaning that it is not a
struct or array type that transitively contains a void or function type and also
that it does not contain any "bare" occurrences of T_structName, which is only
supposed to occur inside a pointer type in a T_struct with the same name.  *)
op objectType? (tp:Type) : Bool =
   case tp of
     | T_struct (_, membs) ->
       forall? objectType? (unzip membs).2
     | T_structName _ -> false
     | T_array (elem_tp, _) -> objectType? elem_tp
     | T_void -> false
     | T_function _ -> false
     | _ -> true


(* Each integer type has a size in bits. *)

op typeBits (ty:Type | integerType? ty) : Nat =
  if characterType? ty then CHAR_BIT
  else if shortType? ty then short_bits
  else if intType? ty then int_bits
  else if longType? ty then long_bits
  else llong_bits

(* In our C subset, two types are compatible [ISO 6.2.7] iff they are the same
type; this is essentially because all our types are complete. *)

op compatibleTypes? (ty1:Type, ty2:Type) : Bool =
  ty1 = ty2

(* Given the above definition, the composite type of two compatible types [ISO
6.2.7] is the same type. *)

op compositeType (ty1:Type, ty2:Type | compatibleTypes? (ty1, ty2)) : Type =
  ty1

(* Substitute a full T_struct struct type containing the given field types for
any T_structName occurrences of the given struct tag in tp. *)
op substStructMemberTypes (tag : Identifier, membs : StructMemberTypes) (tp : Type) : Type =
  case tp of
    | T_structName tag' ->
      if tag = tag' then
        T_struct (Some tag, membs)
      else tp
    | T_struct (tag_opt, membs') ->
      if Some tag = tag_opt then
        (* Avoid name capture *)
        tp
      else
        T_struct (tag_opt,
                  map (fn (f,f_tp) ->
                         (f, substStructMemberTypes (tag, membs) f_tp)) membs')
    | T_pointer tp' ->
      T_pointer (substStructMemberTypes (tag, membs) tp')
    | T_array (tp', n) ->
      T_array (substStructMemberTypes (tag, membs) tp', n)
    | T_function (retTp, paramsTypes) ->
      T_function (substStructMemberTypes (tag, membs) retTp,
                  map (substStructMemberTypes (tag, membs)) paramsTypes)
    | _ -> tp

(* Expand the field types of a struct type by substituting the whole T_struct
struct type for occurrences of T_structName in the field types. *)
op expandStructMemberTypes (struct_tp : StructType) : StructMemberTypes =
  case struct_tp.1 of
    | None ->
      (* No need to expand *)
      struct_tp.2
    | Some tag ->
      map (fn (f,f_tp) -> (f, substStructMemberTypes (tag, struct_tp.2) f_tp)) struct_tp.2


%subsubsection (* Sizes of types *)

(* The size of a pointer is implementation-defined *)
op sizeof_pointer : Nat

(* There might be extra padding in a struct, defined in an
implementation-defined way [ISO 6.7.2.1/15]. This op describes this
implementation-defined padding, which we assume can be computed from the list of
member types in a struct. *)
op struct_padding : List Type -> Nat

(* Each object type has a size, which is returned by the sizeof operator applied
to an expression of that type [ISO 6.5.3.4]. This op calculates this size from
the type itself, assuming that sizeof is valid on this type, i.e., that tp is an
object type. *)
op sizeof (tp:Type | objectType? tp) : Nat =
   case tp of
     | T_char -> 1
     | T_uchar -> 1
     | T_schar -> 1
     | T_ushort -> sizeof_short
     | T_sshort -> sizeof_short
     | T_uint -> sizeof_int
     | T_sint -> sizeof_int
     | T_ulong -> sizeof_long
     | T_slong -> sizeof_long
     | T_ullong -> sizeof_llong
     | T_sllong -> sizeof_llong
     | T_struct (_, membs) ->
       let tps = (unzip membs).2 in
       foldl (Nat.+) (struct_padding tps) (map sizeof tps)
     | T_structName _ -> 0
     | T_pointer _ -> sizeof_pointer
     | T_array (elem_tp, len) -> len * sizeof (elem_tp)
     | T_void -> 0
     | T_function _ -> 0


%subsubsection (* Minimum, maximum, and range of integer types *)

(* We introduce ops to map each integer type to its min and max value, as well
as range of values.*)

op minOfIntegerType (ty:Type | integerType? ty) : Int =
  case ty of
  |  T_char  ->  CHAR_MIN
  | T_uchar  ->         0
  | T_schar  -> SCHAR_MIN
  | T_ushort ->         0
  | T_sshort ->  SHRT_MIN
  | T_uint   ->         0
  | T_sint   ->   INT_MIN
  | T_ulong  ->         0
  | T_slong  ->  LONG_MIN
  | T_ullong ->         0
  | T_sllong -> LLONG_MIN

op maxOfIntegerType (ty:Type | integerType? ty) : Int =
  case ty of
  |  T_char  ->   CHAR_MAX
  | T_uchar  ->  UCHAR_MAX
  | T_schar  ->  SCHAR_MAX
  | T_ushort ->  USHRT_MAX
  | T_sshort ->   SHRT_MAX
  | T_uint   ->   UINT_MAX
  | T_sint   ->    INT_MAX
  | T_ulong  ->  ULONG_MAX
  | T_slong  ->   LONG_MAX
  | T_ullong -> ULLONG_MAX
  | T_sllong ->  LLONG_MAX

op rangeOfIntegerType (ty:Type | integerType? ty) : ISet Int =
  fn x:Int -> minOfIntegerType ty <= x && x <= maxOfIntegerType ty


%subsubection (* Corresponding signed/unsigned integer types *)

(* The following ops associate each signed/unsigned integer type to the
corresponding unsigned/signed integer type. *)

op correspondingUnsignedOf (ty:Type | signedIntegerType? ty) : Type =
  case ty of
  | T_schar  -> T_uchar
  | T_sshort -> T_ushort
  | T_sint   -> T_uint
  | T_slong  -> T_ulong
  | T_sllong -> T_ullong

op correspondingSignedOf (ty:Type | unsignedIntegerType? ty) : Type =
  case ty of
  | T_uchar  -> T_schar
  | T_ushort -> T_sshort
  | T_uint   -> T_sint
  | T_ulong  -> T_slong
  | T_ullong -> T_sllong


%subsubsection (* Integer conversion ranks *)

(* The integer conversion ranks [ISO 6.3.1.1/1] can be expressed via a list of
lists of (integer) types, where the types in each inner list all have the same
rank, and where the inner lists are ordered, within the outer list, with
increasing ranks. *)

op rankedTypes : List (List Type) =
  [[T_char, T_uchar, T_schar],
   [T_sshort, T_ushort],
   [T_sint, T_uint],
   [T_slong, T_ulong],
   [T_sllong, T_ullong]]

(* From the above structure, we can easily define binary relations for
equal/greater/smaller ranks. *)

op rank_= (ty1:Type, ty2:Type) infixl 20 : Bool =
  ex(inner:List Type)
    inner in? rankedTypes && ty1 in? inner && ty2 in? inner

op rank_~= (ty1:Type, ty2:Type) infixl 20 : Bool =
  ~ (ty1 rank_= ty2)

op rank_< (ty1:Type, ty2:Type) infixl 20 : Bool =
  ex (i1:Nat, i2:Nat)
    i1 < i2 && i2 < length rankedTypes &&
    ty1 in? (rankedTypes @ i1) && ty2 in? (rankedTypes @ i2)

op rank_> (ty1:Type, ty2:Type) infixl 20 : Bool =
  ty2 rank_< ty1

op rank_<=  (ty1:Type, ty2:Type) infixl 20 : Bool =
  ty1 rank_< ty2 || ty1 rank_= ty2

op rank_>= (ty1:Type, ty2:Type) infixl 20 : Bool =
  ty2 rank_<= ty1


%subsubsection (* Integer promotions *)

(* At compile time, integer promotion [ISO 6.3.1.1/2] [ISO C2.10] can be
expressed as a mapping from types to types. The result type is the type of the
promoted value, given that the initial value has the argument type. *)

op promoteType (ty:Type) : Type =
  if ty rank_<= T_sint then
    if subset? (rangeOfIntegerType ty, rangeOfIntegerType T_sint) then T_sint else T_uint
  else
    ty  % unchanged


%subsubsection (* Usual arithmetic conversions *)

(* At compile time, the 'usual arithmetic conversions' [ISO 6.3.1.8] can be
expressed as a mapping from two types to a common type. The result type is the
type of the converted values, given that the initial values have the argument
types. *)

op arithConvertTypes
   (ty1:Type, ty2:Type | arithmeticType? ty1 && arithmeticType? ty2) : Type =
  % integer promotion:
  let ty1 = promoteType ty1 in
  let ty2 = promoteType ty2 in
  % both signed or both unsigned:
  if signedIntegerType? ty1 && signedIntegerType? ty2 ||
     unsignedIntegerType? ty1 && unsignedIntegerType? ty2 then
    % convert to type of maximum rank:
    if ty1 rank_< ty2 then ty2 else ty1
  % one signed, one unsigned:
  else
    let sty = if signedIntegerType? ty1 then ty1 else ty2 in  % signed one
    let uty = if unsignedIntegerType? ty1 then ty1 else ty2 in  % unsigned one
    if uty rank_>= sty then uty
    else if subset? (rangeOfIntegerType uty, rangeOfIntegerType sty) then sty
    else correspondingUnsignedOf sty


%subsection (* Constants *)

(* Our C subset only includes integer constants [ISO 6.4.4.1]. It has no
floating [ISO 6.4.4.2], enumeration [ISO 6.4.4.3], or character [ISO 6.4.4.4]
constants.

A decimal constant is a sequence of one or more digits, not starting with 0. *)

op decimalConstant? (str:String) : Bool =
  let chars = explode str in
  nonEmpty? chars &&
  forall? digit? chars &&
  head chars ~= #0

(* An octal constant is a sequence of one or more octal digits (i.e. decimal
except for 8 and 9), starting with 0. *)

op octalDigit? (ch:Char) : Bool =
  digit? ch && ch ~= #8 && ch ~= #9  % 0-7

op octalConstant? (str:String) : Bool =
  let chars = explode str in
  nonEmpty? chars &&
  forall? octalDigit? chars &&
  head chars = #0

(* A hexadecimal constant is a sequence of one or more hexadecimal digits (i.e.
decimal plus a-f and A-F), prepended by the prefix 0x or 0X. *)

op hexadecimalDigit? (ch:Char) : Bool =
  digit? ch ||                               % 0-9
  (ord #A <= ord ch && ord ch <= ord #F) ||  % A-F
  (ord #a <= ord ch && ord ch <= ord #f)     % a-f

op hexadecimalConstant? (str:String) : Bool =
  let chars = explode str in
  length chars > 2 && chars @ 0 = #0 && chars @ 1 = #x &&
  forall? hexadecimalDigit? (removePrefix (chars, 2))

(* Remove any unsigned suffix, and return whether it was removed *)
op removeUnsignedSuffix (str:String) : String * Bool =
  let chars = explode str in
  if length chars > 0 && (last chars = #u || last chars = #U) then
    (implode (butLast chars), true)
  else
    (str, false)

(* Remove any long long suffix, and return whether it was removed *)
op removeLongLongSuffix (str:String) : String * Bool =
  let chars = explode str in
  if length chars > 1 && (suffix (chars, 2) = [#l, #l] || suffix (chars, 2) = [#L, #L]) then
    (implode (removeSuffix (chars, 2)), true)
  else
    (str, false)

(* Remove any long long suffix, and return whether it was removed *)
op removeLongSuffix (str:String) : String * Bool =
  let chars = explode str in
  if length chars > 0 && (last chars = #l || last chars = #L) then
    (implode (butLast chars), true)
  else
    (str, false)


(* Remove any optional suffixes from an integer constant, and return the triple
(prefix, {unsigned?, longlong?, long?}) *)

type IntegerSuffixes =
   {unsigned_suffix : Bool,
    long_suffix : Bool,
    longlong_suffix : Bool}

op removeIntegerSuffixes (str:String) : String * IntegerSuffixes =
  let (str1, unsigned1?) = removeUnsignedSuffix str in
  let (str2, longlong?) = removeLongLongSuffix str1 in
  let (str3, long?) =
    if longlong? then (str2, false) else removeLongLongSuffix str2
  in
  let (str4, unsigned?) =
    if unsigned1? then (str3, true) else removeUnsignedSuffix str3
  in
  (str4, {unsigned_suffix = unsigned?,
          longlong_suffix = longlong?,
          long_suffix = long?})

(* Finally, we define an integer constant as a decimal, octal, or hexadecimal
constant, followed by an optional integer suffix. *)

op integerConstant? (str:String) : Bool =
  let (prefix, _) = removeIntegerSuffixes str in
  (decimalConstant? prefix
     || octalConstant? prefix
     || hexadecimalConstant? prefix)

type IntegerConstant = (String | integerConstant?)


(* The value of an integer constant [ISO 6.4.4.1/4] is known at compile time. It
is a natural number.

We start with the value of a digit, including hex(adecimal) digits. *)

op digitValue (ch:Char | digit? ch) : Nat =
  ord ch - ord #0

op hexDigitValue (ch:Char | hexadecimalDigit? ch) : Nat =
  if digit? ch then digitValue ch
  else if isUpperCase ch then ord ch - ord #A + 10
                         else ord ch - ord #a + 10


(* Conversion functions for strings *)

(* Combine a sequence of digit values into a number value. We do not use
fromBigEndian, because that operation is not executable. *)
op combineDigitValues (digits : List Nat, base : Nat) : Nat =
  foldl (fn (val, digit) -> digit + val * base) 0 digits

op decimalConstantValue (str:String | decimalConstant? str) : Nat =
  combineDigitValues (map digitValue (explode str), 10)

op octalConstantValue (str:String | octalConstant? str) : Nat =
  combineDigitValues (map digitValue (explode str), 8)

op hexadecimalConstantValue (str:String | hexadecimalConstant? str) : Nat =
  let digits = removePrefix (explode str, 2) in
  combineDigitValues (map hexDigitValue digits, 16)

(* To calculate the value of an integer constant, we remove the suffix (if any)
and then we use one of the three ops just defined. Note that the suffix does not
contribute to the value of the constant. *)

op integerConstantValue (str:IntegerConstant) : Nat =
  let (unsuffixed,_) = removeIntegerSuffixes str in
       if decimalConstant? unsuffixed then     decimalConstantValue unsuffixed
  else if   octalConstant? unsuffixed then       octalConstantValue unsuffixed
  else                                     hexadecimalConstantValue unsuffixed


(* An integer constant must have a type into which the value of the constant
fits [ISO 6.4.4.1/5]. The type is determined using the table in [ISO 6.4.4.1/5],
which associates to each integer constant a list of candidate types, based on
the suffixes and the base of the constant. The type of the constant is the first
in the associated list into which the constant's value fits. The checking op for
integer constants returns the type of the constant, or 'None' if the constant
cannot be assigned any type. *)

op integerConstantCandidateTypes (c:IntegerConstant) : List Type =
  let (unsuffixed,suffixes) = removeIntegerSuffixes c in
  let decimal? = decimalConstant? unsuffixed in
  if ~ (suffixes.unsigned_suffix) &&
     ~ (suffixes.long_suffix) &&
     ~ (suffixes.longlong_suffix) then
    if decimal? then [T_sint, T_slong, T_sllong]
                else [T_sint, T_uint, T_slong, T_ulong, T_sllong, T_ullong]
  else if (suffixes.unsigned_suffix) &&
          ~ (suffixes.long_suffix) &&
          ~ (suffixes.longlong_suffix)
  then
    [T_uint, T_ulong, T_ullong]
  else if ~ (suffixes.unsigned_suffix) && (suffixes.long_suffix) then
    if decimal? then [T_slong, T_sllong]
                else [T_slong, T_ulong, T_sllong, T_ullong]
  else if suffixes.unsigned_suffix && suffixes.long_suffix then
    [T_ulong, T_ullong]
  else if ~ suffixes.unsigned_suffix && suffixes.longlong_suffix then
    if decimal? then [T_sllong]
                else [T_sllong, T_ullong]
  else
    [T_ullong]

op integerConstantType (c:IntegerConstant) : Option Type =
  let tys = integerConstantCandidateTypes c in
  let val = integerConstantValue c in
  findLeftmost (fn tp -> (val:Int) memb? rangeOfIntegerType tp) tys


%subsection (* Unary operators *)

(* Of the unary operators in [ISO 6.5.3], our C subset contains the unary
arithmetic operators [ISO 6.5.3.3]. It also includes the address and indirection
operators [ISO 6.5.3.2], but these are handled separately, because they affect
whether an expression is an lvalue or not. *)

type UnaryOp =
  | UOp_PLUS   % unary +
  | UOp_MINUS  % unary -
  | UOp_NOT    % bitwise complement ~
  | UOp_NEG    % logical negation !


%subsection (* Binary operators *)

(* Even though the grammar in [ISO] has no explicit non-terminal for binary
operators (unlike unary operators [ISO 6.5.3/1]), in our formalization we
introduce a notion of binary operator to enable a more compact definition of
expressions later. Our C subset includes all the operators in [ISO
6.5.5-6.5.14]. *)

type BinaryOp =
  | BinOp_MUL   % multiplication *
  | BinOp_DIV   % division       /
  | BinOp_REM   % remainder      %
  | BinOp_ADD   % addition       +
  | BinOp_SUB   % subtraction    -
  | BinOp_SHL   % bitwise shift left  <<
  | BinOp_SHR   % bitwise shirt right >>
  | BinOp_LT    %    less-than             relation <
  | BinOp_GT    % greater-than             relation >
  | BinOp_LE    %    less-than-or-equal-to relation <=
  | BinOp_GE    % greater-than-or-equal-to relation >=
  | BinOp_EQ    %     equal-to relation ==
  | BinOp_NE    % not-equal-to relation !=
  | BinOp_AND   % bitwise           AND &
  | BinOp_XOR   % bitwise exclusive OR  ^
  | BinOp_IOR   % bitwise inclusive OR  |
  | BinOp_LAND  % logical AND &&
  | BinOp_LOR   % logical OR ||


%subsection (* Type names *)

(* The C syntax of object declarations [ISO 6.7] is complicated by the fact that
the declared type of an identifier may be indicated by syntax "around" the
identifier, as opposed to preceding the identifier completely as in other
languages. For example, to declare x to be an array of 3 ints, the C syntax is
'int x[3]', as opposed to something like 'int[3] x'. As another example, to
declare y to be a pointer to an array of 2 ints, the C syntax is 'int *y[2]', as
opposed to something like 'int[3]* y'. (The rationale for the C syntax appears
to be the desire of mirroring the syntax of the expressions that correspond to
the type.)

In the abstract syntax, it is more convenient to separate the identifier from
its declared type completely, instead of potentially mixing them as in the
concrete syntax. In our formalization, we could just use (Specware) values of
(Specware) type Type, except that those do not cover the syntactic case of a
typedef name [ISO 6.7.8]. That is, if the program includes a 'typedef int T;'
declaration, T is a synonym of int in the scope of that declaration, and thus a
further declaration could use T, as in 'T x;'. Typedef names are not part of
type Type, and so if we were to use type Type to model a declaration, we would
be unable to include type identifiers. Extending type Type itself to include
typedef names does not seem appropriate because type Type is meant to capture
the actual types of the C language described in [ISO 6.2.5], while typedef names
are just synonyms.

In essence, to model an object declaration in the abstract syntax, we want to
pair an identifier with either a type (i.e. a value of type Type) or a typedef
name (or a combination thereof, e.g. pointer to typedef name). This notion
corresponds to a type name [ISO 6.7.7], which is syntactically a declaration
that omits the identifier [ISO 6.7.7/2]. Note that suitable sequences of type
specifiers [ISO 6.7.2] can denote most types (of type Type) and also typedef
names, but cannot denote pointers and arrays (which in fact have their own
declarators that follow the type specifiers [ISO 6.7.6.1, 6.7.6.2]), so we could
not use type specifiers to model declarations in our abstract syntax.

Abstracting from the concrete syntactic peculiarities of type names [ISO 6.7.7],
we define a type name as follows. This is the same definition as type Type,
extended with typedef names. Note that the recursion implies that we can form
pointers and arrays of typedef names.
 *)

(* In a type name, a struct can also be referred to by name *)
type StructName = | NamedStruct Identifier

type TypeName =
  % same as type Type:
  | TN_char
  | TN_uchar
  | TN_schar
  | TN_ushort
  | TN_sshort
  | TN_uint
  | TN_sint
  | TN_ulong
  | TN_slong
  | TN_ullong
  | TN_sllong
  | TN_struct  Identifier
  | TN_pointer TypeName
  | TN_array   TypeName * Nat
  | TN_void
  | TN_function TypeName * (List TypeName)
  % typedef name:
  | TN_typedef Identifier


%subsection (* Expressions *)

(* Our C subset includes only expressions which do not have side effects. This
is because the order in which side effects occur in expressions is unspecified
[ISO 6.5/2], but trying to model exactly when such unspecified behavior could
occur is complex and difficult. Thus, any side-effecting expressions (such as
assignment expressions) are promoted to statements in our formalism.

Our C subset includes the following kinds of expressions [ISO 6.5]: identifiers
[ISO 6.5.1/1], integer constants [ISO 6.5.1/1], unary expressions using the
unary operators introduced above, binary expressions using the binary operators
introduced above, conditional expressions [ISO 6.5.15], structure member
expressions (i.e. the '.' and '->' operators, respectively denoted by the
constructors 'member' and 'memberp', where 'p' suggests that the left operand
must be a pointer, as required for '->') [ISO 6.5.2.3], array subscripting [ISO
6.5.2.1], and cast expressions [ISO 6.5.4].

C expressions are typed, and the type of an expression determines the meaning of
the value accessed by it [ISO 6.2.5/1]. Thus, our Expressions contain enough
additional information to determine the type of an expression; this really only
includes the return type of conditional expressions.

Additionally, lvalues are defined as a separate syntactic class from ordinary
expressions. This means that lvalues are distinguished from ordinary expressions
syntactically, not semantically. Although the definition of lvalues [ISO
6.3.2.1/1] is not entirely clear on this distinction, all of the rules about
whether an expression is an lvalue [ISO 6.5.1, 6.5.2.1, 6.5.2.3, 6.5.3.2] give
entirely syntactic rules for determining whether an expression is an lvalue, so
this decision is consistent with the ISO specification. Technically speaking,
our definition of lvalue in fact includes function designators [ISO 6.3.2.1/4],
lumping together expressions that potentially designate objects with those that
potentially designate functions; this simplifies our syntactic definition of the
identifiers and the indirection operator, which can potentially create lvalues
or function designators depending on the type. To separate the lvalues from the
non-lvalue expressions, we define the types LValue and StrictExpression,
respectively, where the type Expression includes both. In our C subset, the
lvalues include the identifiers [ISO 6.5.1], the indirection operator [ISO
6.5.3.2], the structure member operators "." and "->" [ISO 6.5.2.3], and the
array subscript operator [ISO 6.5.2.1]. The address operator "&" requires it
argument to be an lvalue [ISO 6.5.3.2/1], and the structure member operator "."
is an lvalue iff its left-hand side is an lvalue [ISO 6.5.2.3/3]; otherwise, all
expression constructs can take either an lvalue or a non-lvalue expression,
represented by the type ExprOrLValue. *)

type StrictExpression =
  | E_const     IntegerConstant
  | E_unary     UnaryOp * Expression
  | E_addr      LValue
  | E_binary    Expression * BinaryOp * Expression
  | E_cond      Expression * Expression * Expression * TypeName
  | E_member    StrictExpression * Identifier
  | E_cast      TypeName * Expression
type LValue =
  | LV_ident    Identifier
  | LV_star     Expression
  | LV_member   LValue * Identifier
  | LV_memberp   Expression * Identifier
  | LV_subscript Expression * Expression
type Expression =
  | E_strict StrictExpression
  | E_lvalue LValue


%subsection (* Statements *)

(* Our C subset features expression statements [ISO 6.8.3] that are: (i) simple
assignment expressions [ISO 6.5.16.1] (whose left and right operands are
expressions in our C subset); (ii) simple assignment expressions whose left
operand is an expression in our C subset but whose right operand is a function
call [ISO 6.5.2.2]; or (iii) function calls [ISO 6.5.2.2]. Cases (ii) and (iii)
are consolidated in constructor 'call' below, where the left operand is an
optional expression (in our C subset) and the right operand consists of the
function being called plus a list of argument expressions. By modeling
assignments and function calls as statements in our model (vs. expressions as in
full C), we limit such expressions to occur at the top level (or second level
from the top, in the case of a function call assigned to an expression), i.e. as
expression statements. In particular, we exclude multiple assignments like 'a =
b = ...' Note also that, by having function calls not be expressions in our
subset, we maintain expressions free of side effects.

Besides these expression statements, our C subset includes 'if' selection
statements [ISO 6.8.4.1], 'return' jump statements [ISO 6.8.6.4], 'while', and
'do' iteration statements [ISO 6.8.5], and compound statements (i.e. blocks)
[ISO 6.8.2]. (We currently expect that "for" statements are just treated as
"while" statements, possibly with additional statements added before the loop
and at the end of each iteration of the loop.)

Our 'if' statement captures both the variant with 'else' and the
variant without 'else', based on the presence of the second, optional statement.
A 'return' statement [ISO 6.8.6.4] includes an optional expression.

Because of our treatment of assignments and function calls as statements, we use
statements as the first and third (optional) expressions of a 'for' statement.
Later in our model we restrict such statements to assignments and function
calls. Expressions in our model have no side effects, so allowing expressions in
(our model of) 'for' statements would not be very useful.

Besides statements, we only allow object declarations as block items [ISO
6.8.2], not other kinds of declarations. *)

type Statement =
  | S_assign LValue * Expression
  | S_call   Option LValue * Expression * List Expression
  | S_if     Expression * Statement * Option Statement
  | S_return Option Expression
  | S_while  Expression * Statement
  | S_do     Statement * Expression
  | S_for    Statement * Expression * Statement * Statement
  | S_block  List BlockItem

type BlockItem =
  | BlockItem_declaration TypeName * Identifier
  | BlockItem_statement   Statement


%subsection (* Declarations and External Declarations *)

(* We model an object [ISO 3.15] declaration [ISO 6.7] as a pair consisting of a
type name and an identifier. Such a named object is commonly referred to as
'variable', even though [ISO] seems to carefully avoid this term.

Our model of object declarations excludes type qualifiers [ISO 6.7.3],
initializers [ISO 6.7.6], and all explicit storage class specifiers [ISO 6.7.1]
other than "extern", which is here represented as a Boolean indicating whether
extern is present or not. Our model also excludes any declarator other than a
simple identifier [ISO 6.7.6], since these can all be modeled using simple
identifiers with more complex types. *)

type ObjectDeclaration =
 {ObjDecl_type : TypeName,
  ObjDecl_name : Identifier,
  ObjDecl_isExtern : Bool}

(* [ISO 6.7.2.1/1] uses the term 'struct-declaration' for the members of a
structure or union type specifier. This term seems unfortunate because it is a
declaration for a member of a structure, not for the whole structure, and it
also applies to unions, which are not structures. Thus, we prefer to deviate
from the [ISO 6.7.2.1/1] terminology and use the term 'member declaration',
which we model as a pair consisting of a type name and an identifier. *)

type MemberDeclaration =
  {MemDecl_type : TypeName,
   MemDecl_name : Identifier}

(* We model a structure specifier [ISO 6.7.2.1] as a pair consisting of a tag
(which is an identifier) and a list of member declarations. Thus, we require the
tag and the members to be always present and we exclude bit fields. *)

type StructSpecifier =
  {StructSpec_tag     : Identifier,
   StructSpec_members : List MemberDeclaration}

(* We model a type definition [ISO 6.7.8] as a pair consisting of a type name
and an identifier. *)

type TypeDefinition =
  {Typedef_type : TypeName,
   Typedef_name : Identifier}

(* In our C subset, a (function) parameter declaration [ISO 6.7.6/1] consists of
a type name and a name. A parameter list [ISO 6.7.6/1] is a list of parameter
declarations. In our C subset, a parameter list is also a parameter type list
[ISO 6.7.6/1], because we disallow ellipsis in function definitions. *)

type ParameterDeclaration = TypeName * Identifier
type ParameterList = List ParameterDeclaration

(* We combine function declarations [ISO 6.7.6.3] and definitions [ISO 6.9.1]
into the same type, which contains a return type (name), a name, a parameter
list, and an optional body, where the body is supplied for a function definition
and not supplied for a function declaration. We also support the "extern"
storage class specifier for function declarations, allowing functions to call
other functions in different translation units, but it is an error for a
function definition to be marked "extern". *)

type FunctionDeclaration =
 {FDef_retType    : TypeName,
  FDef_name       : Identifier,
  FDef_params     : ParameterList,
  FDef_body       : Option Statement,
  FDef_isExtern   : Bool}

(* The following are the declarations [ISO 6.7] that, as defined later, can
appear at the top level in a translation unit in our C subset. *)

(* FIXME: these are allowed inside functions, however, which is why they are
separated from the external declarations *)

type Declaration =
  | Decl_struct   StructSpecifier
  | Decl_object   ObjectDeclaration
  | Decl_typedef  TypeDefinition


%subsection (* Translation units *)

(* In the C standard, source files are called "preprocessing translation units"
[ISO 5.1.1.1/1], which are then preprocessed into "translation units". We
combine these two steps, so we just call input files "translation units". The
only preprocessing we support, however, is include directives [ISO 6.10.2], so
our translation units are lists of include directives and external declarations,
where the latter include function definitions and declarations [ISO 6.9/1].
Include directives can either use the "<" and ">" delimeters or double quotes as
delimiters, so the XU_include constructor includes a boolean flag which is true
iff the "<" and ">" delimiters are intended. *)
type TranslationUnitElem =
  | XU_declaration Declaration
  | XU_function FunctionDeclaration
  | XU_include String * Bool

type TranslationUnit = List TranslationUnitElem


%section (* Semantics *)

(* Besides syntax and syntactic constraints, [ISO] describes the semantics (i.e.
execution) of C programs. *)


%subsection (* Object and Function Designators *)

(* Each object declaration in a program in our C subset introduces an object
[ISO 3.15]. When such an object is a structure, its members are subobjects of
the object, which can be independently written to via a suitable lvalue [ISO
6.3.2.1/1]. Similarly, when the object is an array, its elements are subobjects
and they can be written independently via a suitable lvalue. This recursively
applies to members and elements of structure members and array elements.

For all of these objects, we introduce the object designators, as entities that
refer to these objects. Intuitively, an object designator is a pointer to an
object in the heap, and, in fact, this is how pointer values are defined below.

At the top level of the nesting of subobjects inside other objects are the
global variables, the local (i.e., stack) variables, and the heap-allocated
objects (returned by, e.g., malloc). These three classes of top-level objects
correspond to the three sorts of storage [ISO 6.2.4] in C (not including thread
storage, which we do not support here): static storage for global variables,
automatic storage for local (i.e., stack) variables, and allocated storage for
heap-allocated objects. Top-level objects in static and automatic storage are
referred to by name, since each object in static and automatic storage
corresponds to a, respectively, global or local variable. However, because of
variable shadowing, the same name can refer to multiple objects. Thus, to form a
unique reference to a named top-level object, a variable name must be combined
with a "scope designator" that specifies either global or local scope,
corresponding to static or automatic variables, respectively. For local scope,
the scope designator must additionally specify which scope is being referred to,
using a ScopeID. *)

type ScopeID = | ScopeID Nat

type ScopeDesignator =
  | GlobalScope
  | LocalScope ScopeID

type AllocatedID = | AllocatedID Nat

type ObjectDesignator =
  | OD_Top        ScopeDesignator * Identifier
  | OD_Allocated  AllocatedID
  | OD_Member     ObjectDesignator * Identifier
  | OD_Subscript  ObjectDesignator * Nat

(* Whether d1 is a prefix of d2 *)
op object_desig_prefix? : PartialOrder (ObjectDesignator) =
  fn (d1,d2) ->
    d1 = d2 ||
    (case d2 of
       | OD_Member (d2', _) -> object_desig_prefix? (d1,d2')
       | OD_Subscript (d2', _) -> object_desig_prefix? (d1,d2')
       | OD_Top _ -> false
       | OD_Allocated _ -> false)


(* A function designator [ISO 6.3.2.1] is defined to be any expression that has
function type. We diverge slightly from this definition, and define a function
designator to be any identifier that has function type. Note that any function
designator in the C spec will always evaluate to the function defined by some
named function definition somewhere in the program, and thus the value of an
expression of function type (the C spec's definition of "function designator")
will always be an element of the FunctionDesignator type defined here. Later,
when we define the Monad type, we will define a lookup table for finding the
actual monadic function associated with a FunctionDesignator. *)

type FunctionDesignator = | FunctionDesignator Identifier


(* A pointer is a reference to an object or a function [ISO 6.2.5/20]. *)

type Pointer =
  | ObjPointer ObjectDesignator
  | FunPointer FunctionDesignator


%subsection (* Values *)

(* We represent integers in values with a tagged integer type, because values in
C are always interpreted at a specific type [ISO 3.19] and the type of an
integer affects the semantics of C in a lot of places *)
type TypedInt = { ty_i : Type * Int |
                   integerType? ty_i.1 && ty_i.2 memb? rangeOfIntegerType ty_i.1 }

(* We now define the values. The C spec defines a value as the contents of an
object when interpreted at a specific type [ISO 3.19], where an object is a
region of data storage [ISO 3.15]. To reflect this, we define values to also
contain (enough information to reconstruct) the type at which they are being
viewed.

A structure (value) consists of a list of members, each with a name and a value.
(We disallow unnamed members, to simplify structs.) It also consists a
StructType for the struct.

A pointer (value) is an element of the Pointer type defined above, along with a
type tag, identifying the element type at which this pointer is being viewed.
Note that this element type could actually be different from the actual type
of the object designated by the pointer in the heap.

An array value consists of a list of values, which give the elements of the
array, along with the element type of those values.

Null pointers [ISO 6.3.2.3/3] are represented separately from pointers,
and also contain the type at which they are being viewed.

Finally, our values contain trap representations [ISO 3.19.4], which are
represented with the V_undefined constructor. These are objects that do not
denote an actual value of a specified type, and are used for, e.g., the initial
values of objects with automatic storage (i.e., stack variables). *)

type Value =
  | V_int         TypedInt
  | V_struct      StructType * List (Identifier * Value)
  | V_pointer     Type * Pointer
  | V_array       Type * List Value
  | V_nullpointer Type
  | V_undefined   Type


(* We can extract from a value the type at which we are viewing it *)
op typeOfValue (val:Value) : Type =
  case val of
  | V_int (ty, _)            -> ty
  | V_struct (tag, _)        -> T_struct tag
  | V_pointer (ty, _)        -> T_pointer ty
  | V_array (ty, vals)       -> T_array (ty, length vals)
  | V_nullpointer ty         -> T_pointer ty
  | V_undefined ty           -> ty


(* We lift some of the predicates that classify types to predicates that
classify values. Note that undefined values of the correct types are
included. *)

op integerValue? (val:Value) : Bool =
  integerType? (typeOfValue val)

op arithmeticValue? (val:Value) : Bool =
  arithmeticType? (typeOfValue val)

op pointerValue? (val:Value) : Bool =
  embed? T_pointer (typeOfValue val)

op structValue? (val:Value) : Bool =
  embed? T_struct (typeOfValue val)

op arrayValue? (val:Value) : Bool =
  embed? T_array (typeOfValue val)

op scalarValue? (val:Value) : Bool =
  scalarType? (typeOfValue val)


(* FIXME HERE: write a version of this that includes a heap typing, and
checks pointer types *)

(* Return true iff the given value "has" the given type (FIXME: find the ISO
section for this...) *)
op valueHasType (v:Value, tp:Type) : Bool =
  compatibleTypes? (typeOfValue v, tp)

(* Return true iff the given list of values "have" the given types (FIXME: find
the ISO section for this...) *)
op valuesHaveTypes (vs:List Value, tps:List Type) : Bool =
  case (vs, tps) of
    | ([], []) -> true
    | (v::vs', tp::tps') ->
      valueHasType (v, tp) && valuesHaveTypes (vs', tps')
    | _ -> false

(* Return true iff the given function return value (or None for a function that
does not return a value) is compatible with the given type *)
op optValueHasType (opt_v:Option Value, tp:Type) : Bool =
  case opt_v of
    | Some v -> valueHasType (v,tp)
    | None -> compatibleTypes? (T_void, tp)


%subsection (* Storage *)

(* An object is a region of storage [ISO 3.15]. When the object has a name, that
name identifies that region of storage. We introduce the notion of named storage
as a mapping from names of objects to the values stored in those objects. Recall
that values in C are object contents viewed at a specific type [ISO 3.19]; the
type at which an object is being viewed in a named storage is the effective type
of the object [ISO 6.5/6], which is the same as the type at which the object was
declared. *)

type NamedStorage = IMap (Identifier, Value)

(* A "local scope" is a runtime instance of a block scope [ISO 6.2.1]. Each time
a function is executed, a new local scope is created for the function itself,
and, every time a sub-block is entered in that function, a new local scope is
created for that sub-block scope. Local scopes have a nesting, mirroring that of
the block scopes they are instances of; i.e., the local scope created for a
particular block always has a local scope for the block containing it. The top
local scope of a function always has the global scope as its parent. This is
captured by using a ScopeDesignator to designate the parent scope of a given
local scope. *)

type LocalScope = {scope_bindings : NamedStorage,
                   scope_parent   : ScopeDesignator }

(* As mentioned in the comments for type 'ObjectDesignator', our model of
storage includes allocated objects, which are identified by the AllocatedID type
introduced earlier. The allocated storage is modeled as a list, where
AllocatedIDs, which are just natural numbers, are used to index into this
list. In order to model deallocation of objects, the allocated storage list
contains optional values, where "None" indicates a deallocated object. This is
to prevent another allocation from re-using an AllocatedID. Allocated objects
also do not have a declared type, and so can change type when they are assigned
to [ISO 6.5/6]; the only restriction is the size of the allocated object, which
does not change, and so this size is included with the allocated object. *)
type AllocatedStorage = List (Option (Value * Nat))

(* We model the global, dynamic storage of a program as containing three fields
corresponding to the three storage durations [ISO 6.2.4] of objects (excluding
thread-local storage, which we do not model here). The static storage, for
global variables and function definitions, is modeled as a named storage. The
automatic storage, for local variables inside function bodies and nested blocks,
is modeled as a list of local scopes, where ScopeID N refers to the Nth element
of this list. To model the fact that automatic scopes are destroyed /
deallocated when the block they belong to is exited, elements of the automatic
storage list are actually of Option type, where "None" indicates a scope
that has been deallocated. The storage for allocated objects is modeled
with the AllocatedStorage type introduced above.
*)

type Storage =
  {static    : NamedStorage,
   automatic : List (Option LocalScope),
   allocated : AllocatedStorage}


%subsection (* Outcomes *)

(* FIXME HERE: update this documentation! *)

(* [ISO] prescribes the outcomes of certain computations, while leaving the
outcomes of other computations undefined [ISO 3.4.3] or implementation-defined
[ISO 3.4.1]. In our formalization, we collectively regard undefined and
implementation-defined outcomes as errors, since we cannot prove anything
about these outcomes.

The syntactic constraints checked at compile time guarantee that certain
situations will never occur at run time. An example of this kind of situation is
referencing a variable that is not in scope. Thus, execution needs not deal with
such situations, i.e. the semantics of the C constructs in [ISO] is only defined
for those instances of the constructs that satisfy the compile-time checks.
Correspondingly, our formalization could restrict the specification of execution
to only the situations allowed by the compile-time checks. However, it seems
simpler to specify execution in all situations, and have the Specware functions
return a special error result to indicate that the situation should not arise if
all the compile-time checks are satisfied. We can then prove that no error ever
arises when all the compile-time checks (formalized earlier) are satisfied.

emw4: We defer the low-level semantic definitions of C computations to a monad,
which is defined externally to this spec. This monad must of course satisfy the
monad laws, as specified by the monad spec /Library/Structures/Data/Monad, but
must additionally provide features for error-reporting, for mutating some global
state, for reading lexically-scoped information, and for representing
non-terminating computations. These features are all specified in the following
extensions of the monad spec. Note that, by leaving the Monad type abstract, we
can instantiate it with different actual monads depending on the "computational
features" we want to model; e.g., concurrency, file operations, etc. *)

import /Library/Structures/Data/Monad/MonadError
import /Library/Structures/Data/Monad/MonadState
import /Library/Structures/Data/Monad/MonadReader
import /Library/Structures/Data/Monad/MonadNonTerm

(* The map function for monads; FIXME: should be in a standard library spec
   somewhere... *)
op [a,b] mapM (f : a -> Monad b) (xs : List a) : Monad (List b) =
   case xs of
     | [] -> return []
     | x :: xs' ->
       {new_x <- f x;
        new_xs <- mapM f xs';
        return (new_x :: new_xs)}

(* Compose two monadic functions *)
op [a,b,c] composeM (f : a -> Monad b) (g : b -> Monad c) (a:a) : Monad c =
   monadBind (f a, g)

(* The map function for Option; FIXME: should be in a standard library spec
   somewhere... *)
op [a,b] mapM_opt (f : a -> Option b) (xs : List a) : Option (List b) =
   case xs of
     | [] -> Some []
     | x :: xs' ->
       {new_x <- f x;
        new_xs <- mapM_opt f xs';
        Some (new_x :: new_xs)}


%subsubsection (* Non-Local Exits *)

(* These are all the non-local exits in Monad, i.e., the "ways" in which a
computation in Monad can bypass the normal return mechanism, and return control
back to the most recent enclosing catchErrs construct.

The first three represent, respectively, undefined behavior [ISO 3.4.3],
unspecified as well as implementation-defined behavior [ISO 3.4.1, ISO 3.4.4],
and behaviors that are not implemented by this formalization. These are not ever
meant to be caught by catchErrs, because they represent situations that it is
not generally possible to even detect in a C program, and any use of catchErrs
below always immediately re-raises any of these non-local exits. The reason we
model these sorts of behaviors as non-local exits is because, in any situation
where the standard prescribes such a behavior, our formalism can no longer say
anything about the remainder of the computation.

Note that there is a subtle difference between "error", which represents
undefined behavior, and "nonstd", which represents unspecified and/or
implementation-defined behavior: in the former case, the standard does allow a
program to immediately terminate execution, or basically do anything, so our
formalization in a sense agrees with the standard; while in the latter case, the
standard gives a set of choices of possible behaviors, none of which is
terminating the program, and so in a sense our formalization disagrees with the
standard, but in a way where it detects and represents this disagreement.
Behaviors that are not implemented by our formalization are similar to "nonstd"
in this respect.

The final non-local exit is used to model a return statement, which immediately
transfers control to the caller of a function. A return also passes an optional
result value to the caller, which is captured by having Err_return take an
optional value. Note that this is not really an "error", even though it is
captured by the "Err" type here. *)

type Monad.Err =
    | Err_error
    | Err_nonstd
    | Err_unimplemented
    | Err_return (Option Value)

(* Helper functions for performing non-local exits *)
op [a] error : Monad a = raiseErr Err_error
op [a] nonstd : Monad a = raiseErr Err_nonstd
op [a] unimplemented : Monad a = raiseErr Err_unimplemented
op [a] returnFromFun (retVal : Option Value) : Monad a =
   raiseErr (Err_return retVal)

(* Conditionally raise an error *)
op errorIf (condition:Bool) : Monad () =
  if condition then error else return ()

(* Conditionally flag a non-standard computation *)
op nonstdIf (condition:Bool) : Monad () =
  if condition then raiseErr Err_nonstd else return ()

(* Lift an Option a to a Monad a, mapping None to error *)
op [a] liftOption (opt: Option a) : Monad a =
  case opt of
    | Some x -> return x
    | None -> error

(* Catch any returnFromFuns called in body, returning None if there were none *)
op catchReturns (body : Monad ()) : Monad (Option Value) =
   catchErrs ({ body; return None },
              (fn err ->
                 case err of
                   | Err_return retVal -> return retVal
                   | _ -> raiseErr err))


% subsection (* Operations on storages *)

(* The state type of the monad is the Storage type defined above *)
type Monad.St = Storage

(* To operate on storages in a general and elegant way, we map each object
   designator to a "monadic lens", i.e., to a pair of mondic getter and setter
   functions for that particular designator. These are built up by composing
   monadic lenses for the different storage components. *)
import /Library/Structures/Data/MLens

(* type MLens.Monad a = Monad a *)

(* The "easy" monadic lens, corresponding to the getState and putState
   non-proper morphisms in our state monad *)
op storageLens : MLens ((), Storage) =
   {mlens_get = fn () -> getState,
    mlens_set = fn () -> putState }

(* Lenses for the fields of a Storage *)
op storageStaticFieldLens : MLens (Storage,NamedStorage) =
   {mlens_get = fn s -> return s.static,
    mlens_set = fn s -> fn v -> return (s << {static=v})}
op storageAutomaticFieldLens : MLens (Storage,List (Option LocalScope)) =
   {mlens_get = fn s -> return s.automatic,
    mlens_set = fn s -> fn v -> return (s << {automatic=v})}
op storageAllocatedFieldLens : MLens (Storage,AllocatedStorage) =
   {mlens_get = fn s -> return s.allocated,
    mlens_set = fn s -> fn v -> return (s << {allocated=v})}

(* Composing the above with storageLens gives us monadic lenses for the three
   "current" storage classes *)
op staticStorageLens : MLens ((),NamedStorage) =
   mlens_compose (storageLens, storageStaticFieldLens)
op automaticStorageLens : MLens ((),List (Option LocalScope)) =
   mlens_compose (storageLens, storageAutomaticFieldLens)
op allocatedStorageLens : MLens ((),AllocatedStorage) =
   mlens_compose (storageLens, storageAllocatedFieldLens)

(* Build a lens for the optional LocalScope with the given ScopeID, where
   "optional" means it is allowed to be in a deallocated state *)
op localScopeOptLens (scope_id : ScopeID) : MLens ((),Option LocalScope) =
  case scope_id of
    | ScopeID n ->
      mlens_compose (automaticStorageLens,
                     mlens_of_list_index (n, error, error))

(* Build a lens for the LocalScope with the given ScopeID, raising an error if
   that scope has been deallocated *)
op localScopeLens (scope_id : ScopeID) : MLens ((),LocalScope) =
   mlens_compose (localScopeOptLens scope_id, mlens_for_option (error, error))

(* Build a lens for the bindings in a LocalScope *)
op localScopeBindingsLens : MLens (LocalScope,NamedStorage) =
   {mlens_get = fn lscope -> return lscope.scope_bindings,
    mlens_set = fn lscope -> fn nstorage ->
      return (lscope << {scope_bindings = nstorage})}

(* Build a lens for the scope corrersponding to a ScopeDesignator *)
op scopeDesignatorLens (d:ScopeDesignator) : MLens ((),NamedStorage) =
   case d of
     | GlobalScope -> staticStorageLens
     | LocalScope (scope_id) ->
       mlens_compose (localScopeLens scope_id, localScopeBindingsLens)

(* Get the parent of a given local scope *)
op getScopeParent (scope_id: ScopeID) : Monad ScopeDesignator =
   {scope <- (localScopeLens scope_id).mlens_get ();
    return scope.scope_parent}

(* Build a lens for the optional Value + size associated with the given
   AllocatedID in allocated storage, where "optional" means the AllocatedID is
   allowed to be in a deallocated state *)
op allocatedObjOptLens (alloc_id : AllocatedID) : MLens ((),Option (Value * Nat)) =
  case alloc_id of
    | AllocatedID n ->
      mlens_compose (allocatedStorageLens,
                     mlens_of_list_index (n, error, error))

(* Build a lens for the Value + size associated with the given AllocatedID in
   allocated storage, raising an error if the object has been deallocated. *)
op allocatedObjLens (alloc_id : AllocatedID) : MLens ((), Value * Nat) =
   mlens_compose (allocatedObjOptLens alloc_id,
                  mlens_for_option (error, error))

(* Build a lens for the struct fields of a Value.

   NOTE: structFieldsLens does *not* do auto-vivification for the structure
   fields of uninitialized structs; i.e., if the "get" function is applied to an
   undefined object, it is an error, and "get" does *not* return a mapping that
   assigns undefined objects to all the fields. (The "Deep" semantics this file
   was derived from did do auto-vivification.) In order to support
   auto-vivification, structFieldsLens would need not only the field typing
   information associated with a named structure type, but it would also need
   the "get" function to actually modify the undefined struct object into a
   defined object where all its fields are undefined objects, otherwise it
   violates the monadic lens laws (specifically, the get-put law). It is
   possible to modify structFieldsLens to do this auto-vivification by giving it
   the "upstream" lens, so that the "get" function can modify the given struct
   value, but it is much easier to just never allow undefined struct objects to
   begin with. *)
op structFieldsLens : MLens (Value, List (Identifier * Value)) =
   {mlens_get = fn v -> case v of
                          | V_struct (_, fields) -> return fields
                          | _ -> error,
    mlens_set =
      fn v -> fn fields -> case v of
                             | V_struct (ident,_) ->
                               return (V_struct (ident, fields))
                             | _ -> error}

(* Build a lens for the array elements of a Value. Does not do auto-vivification
   for undefined objects. (See the comments for structFieldsLens, above.) *)
op arrayElementsLens : MLens (Value, List Value) =
   {mlens_get = fn v -> case v of
                          | V_array (_, fields) -> return fields
                          | _ -> error,
    mlens_set =
      fn v -> fn fields -> case v of
                             | V_array (tp,_) ->
                               return (V_array (tp, fields))
                             | _ -> error}

(* Build a lens for the object corrersponding to an ObjectDesignator. Note that
   reading from or writing to an array index out of bounds of an array is not an
   error, but is instead leads to unspecified behavior *)
op objectDesignatorLens (d:ObjectDesignator) : MLens ((),Value) =
   case d of
     | OD_Top (scope_d, ident) ->
       mlens_compose (scopeDesignatorLens scope_d,
                      mlens_of_key (ident, error, error))
     | OD_Allocated a_id ->
       mlens_compose (allocatedObjLens a_id, mlens_for_proj1)
     | OD_Member (d', ident) ->
       mlens_compose (objectDesignatorLens d',
                      mlens_compose (structFieldsLens,
                                     mlens_of_alist_key (ident, error, error)))
     | OD_Subscript (d', i) ->
       mlens_compose (objectDesignatorLens d',
                      mlens_compose
                        (arrayElementsLens,
                         mlens_of_list_index (i, nonstd, nonstd)))

(* Helper predicate for saying an object has a value in a given Storage *)
op objectHasValue storage d v : Bool =
  {putState storage; (objectDesignatorLens d).mlens_get ()} = {putState storage; return v}

(* Helper functions for reading from and writing to designated objects *)
op readObject (d:ObjectDesignator) : Monad Value =
   (objectDesignatorLens d).mlens_get ()
op writeObject (d:ObjectDesignator, v:Value) : Monad () =
   (objectDesignatorLens d).mlens_set () v

(* Helper functions for reading from and writing to pointer values *)
op readPtrValue (v:Value) : Monad Value =
   case v of
     | V_pointer (_, ObjPointer obj) -> readObject obj
     | _ -> error
op writePtrValue (v1:Value, v2:Value) : Monad () =
   case v1 of
     | V_pointer (_, ObjPointer obj) -> writeObject (obj, v2)
     | _ -> error

(* FIXME: it would be nice to develop a pattern for "allocatable" monadic
lenses, such as the LocalScopes and allocated objects, below *)

(* Add a new static binding in the global scope *)
op addStaticBinding (id:Identifier, val:Value) : Monad () =
  {static <- staticStorageLens.mlens_get ();
   if some? (static id) then
     (* Raise an error if id already has a static binding *)
     error
   else
     staticStorageLens.mlens_set () (update static id val)}

(* Allocate a new ScopeID to point to a given LocalScope *)
op allocateLocalScope (scope:LocalScope) : Monad ScopeID =
  {storage <- getState;
   putState (storage << {automatic = storage.automatic ++ [Some scope]});
   return (ScopeID (length storage.automatic))}

(* Deallocate a LocalScope *)
op deallocateLocalScope (scope_id:ScopeID) : Monad () =
   (localScopeOptLens scope_id).mlens_set () None

(* Allocate storage for an object in the AllocatedStorage *)
op allocateObject (val: Value, size : Nat) : Monad AllocatedID =
  {storage <- getState;
   putState (storage << {allocated = storage.allocated ++ [Some (val, size)]});
   return (AllocatedID (length storage.automatic))}

(* Deallocate an object in the AllocatedStorage *)
op deallocateObject (alloc_id: AllocatedID) : Monad () =
   (allocatedObjOptLens alloc_id).mlens_set () None


%subsubsection (* Translation Environment *)

(* C programs are translated in a "translation environment" [ISO 5.1.1], though
not much is specified about translation environments. In our formalization, the
translation environment contains information about the typedefs and struct tags
that the compiler has processed so far, as well as a global lookup table for
named function definitions. We separate this information from the global state
of the program, which was defined above as a Storage, because intuitively this
information is static and lexical, not dynamic; i.e., different functions
compiled in different translation units, although they share the same storage,
can use different typedefs and structure tags. To model the availability of this
information, we use a reader monad with type "TranslationEnv", defined below. *)

(* To define the TranslationEnv type, we start by defining a symbol table for
type definitions, i.e. an association of types to typedef names. *)

type TypedefTable = IMap (Identifier, Type)

(* A structure type, introduced by a structure specifier, consists of
an ordered list of typed members, each of which is modeled as a pair
of a member name and its type. A symbol table for structure specifiers
associates typed members to structure tags (which are identifiers). *)

type StructTable = IMap (Identifier, StructMemberTypes)

(* A function table is a mapping from identifiers to monadic functions on zero
or more values. These monadic functions are restricted so that they cannot
depend on the translation environment, a condition which is specified by
requiring the monadic computations to be insensitive to the localR monadic
operation. This condition is necessary when we actually try to build a concrete
Monad type, in order to break the circularity between the Monad and
FunctionTable types: the Monad type must contain (a type isomorphic to) the
FunctionTable type, which in turn contains the Monad type. In fact, the Monad
type must contain (a type isomorphic to) the FunctionTable type in a negative
position, since Monad is a MonadReader for a type containing FunctionTable.

The reason this condition breaks the circularity is that it allows Monad to be
define as something like the following (using Haskell's ReaderT transformer):

type Monad a = ReaderT (TypedefTable * StructTable * UnderFunctionTable) UnderMonad a
type UnderFunctionTable =
   List (Identifier * (List Value -> MonadUnder Value))

for some underlying monad UnderMonad. With this definition of Monad, we have
that UnderMonad a is isomorphic to { m:Monad a | fa (f) localR f m = m }, where
lifting through the ReaderT transformer does one direction of the isomorphism
and applying a Monad computation m to any TranslationEnv (an operation also know
as "runReaderT" in Haskell) is the other direction of the isomorphism. *)

(* FIXME HERE: update documentation with the new FunctionTable and
FunctionTypes types! *)

type FunctionTypeTable = IMap (Identifier, FunType)

type CFunction = List Value -> Monad (Option Value)

op top_function? (cfun: CFunction) : Bool =
   fa (l,f) localR f (cfun l) = cfun l
type TopFunction = { f:CFunction | top_function? f }

type RawFunctionTable = (Identifier * List Value) -> Monad (Option Value)
type FunctionTable = { tab : RawFunctionTable |
                        fa (id) top_function? (fn vals -> tab (id,vals)) }

(* We now define TranslationEnv as containing tables for typedefs, structs, and
top-level function definitions.

FIXME: in the future, this could also contain information about staitc
identifiers with internal linkage, i.e., global variables, as well as static
variables inside functions, that are not visible outside the current file and/or
function body. *)

(* FIXME HERE: update above documentation to reflect that the FunctionTable
is no longer in TranslationEnv *)

type TranslationEnv =
   {xenv_typedefs   : TypedefTable,
    xenv_structures : StructTable,
    xenv_funtypes   : FunctionTypeTable }

op emptyTranslationEnv : TranslationEnv =
   {xenv_typedefs   = empty,
    xenv_structures = empty,
    xenv_funtypes   = empty}


(* The reader type of the monad is the TranslationEnv type, along with the
   function table and a designator for the current lexical scope *)
type Monad.R =
   {r_xenv      : TranslationEnv,
    r_curScope  : ScopeDesignator,
    r_functions : FunctionTable }

(* Build an element of the R type using a global scope *)
op makeGlobalR (env : TranslationEnv, funs : FunctionTable) : R =
   {r_xenv = env, r_curScope = GlobalScope, r_functions = funs}

(* Test if a typedef name is currently defined *)
op testTypeDef (name : Identifier) : Monad Bool =
  {r <- askR;
   return (some? (r.r_xenv.xenv_typedefs name))}

(* Look up a typedef name *)
op lookupTypeDef (name : Identifier) : Monad Type =
  {r <- askR;
   liftOption (r.r_xenv.xenv_typedefs name)}

(* Look up the members of a named struct, expanding recursive occurrences of the
struct name *)
op lookupStructMemberTypes (tag : Identifier) : Monad StructMemberTypes =
  {r <- askR;
   membs <- liftOption (r.r_xenv.xenv_structures tag);
   return (expandStructMemberTypes (Some tag, membs))}

(* Look up a function *)
op lookupFunction (f_desig : FunctionDesignator) : Monad CFunction =
  case f_desig of
    | FunctionDesignator id ->
      {r <- askR;
       return (fn args -> r.r_functions (id, args))}

(* Look up a function's type *)
op lookupFunctionType (f_desig : FunctionDesignator) : Monad FunType =
  case f_desig of
    | FunctionDesignator id ->
      {r <- askR;
       liftOption (r.r_xenv.xenv_funtypes id)}

(* Get the current ScopeDesignator *)
op getCurrentScopeDesignator : Monad ScopeDesignator =
  {r <- askR; return r.r_curScope }

(* Run a computation with a different current scope *)
op [a] withCurrentScopeDesignator (d:ScopeDesignator) (m:Monad a) : Monad a =
  localR (fn r -> r << {r_curScope = d}) m

(* Monadic lens for (just the bindings of) the current scope *)
op currentBindingsLens : MLens ((), NamedStorage) =
  mlens_of_computation {d <- getCurrentScopeDesignator;
                        return (scopeDesignatorLens d)}

(* Add a binding to the current scope, raising an error if a binding with that
   name already exists in the current scope or the current typedef table *)
op addLocalBinding (id:Identifier, val:Value) : Monad () =
  {bindings <- currentBindingsLens.mlens_get ();
   is_type_def <- testTypeDef id;
   if some? (bindings id) || is_type_def then
     error
   else
     currentBindingsLens.mlens_set () (update bindings id val)}

op addLocalBindings (bindings: List (Identifier * Value)) : Monad () =
   {_ <- mapM addLocalBinding bindings; return ()}

(* Perform a computation with a freshly allocated LocalScope, setting that
   LocalScope to be the current scope for the duration of the computation and
   deallocating the scope upon exit *)
op [a] inFreshLocalScope (scope:LocalScope) (m:Monad a) : Monad a =
  {scope_id <- allocateLocalScope scope;
   ret <- withCurrentScopeDesignator (LocalScope scope_id) m;
   deallocateLocalScope scope_id;
   return ret}

(* Perform m in a fresh LocalScope with the given bindings, using the current
   scope as the parent scope *)
op [a] withFreshLocalBindings (bindings:NamedStorage) (m : Monad a) : Monad a =
  {cur_scope <- getCurrentScopeDesignator;
   inFreshLocalScope {scope_bindings = bindings, scope_parent = cur_scope} m}

(* Perform m in a fresh LocalScope with the given bindings, using the top-level
   static scope as the parent scope *)
op [a] withFreshTopBindings (bindings:NamedStorage) (m : Monad a) : Monad a =
  inFreshLocalScope {scope_bindings = bindings, scope_parent = GlobalScope} m

(* Look up an identifier, starting in the designated scope and proceeding to its
   parents, and then falling back on the global function table if necessary. The
   result is either an object or function designator, i.e., a Pointer. Also return
   the type of the identifier as well. *)
op lookupIdentifierInScope (id:Identifier, scope:ScopeDesignator) : Monad (Type * Pointer) =
  {bindings <- (scopeDesignatorLens scope).mlens_get ();
   case (bindings id) of
     | Some v ->
       (* If id is in the current scope, return the corresponding pointer *)
       return (typeOfValue v, ObjPointer (OD_Top (scope, id)))
     | None ->
       (case scope of
          | LocalScope scope_id ->
            (* If id is not in the current scope, proceed to the parent scope *)
            {parent_scope <- getScopeParent scope_id;
             lookupIdentifierInScope (id, parent_scope)}
          | GlobalScope ->
            (* If no parent scope, check in the function table; we do a lookup and
               discard the value as a way of ensuring id is in the table *)
            {fun_tp <- lookupFunctionType (FunctionDesignator id);
             return (T_function fun_tp, FunPointer (FunctionDesignator id)) })}

(* Look up an identifier starting in the current scope *)
op lookupIdentifier (id:Identifier) : Monad (Type * Pointer) =
  {d <- getCurrentScopeDesignator;
   lookupIdentifierInScope (id, d)}

(* Look up an identifier for an object and get its value *)
(* FIXME HERE: handle function designators *)
op lookupIdentifierValue (id:Identifier) : Monad Value =
  {(_, ptr) <- lookupIdentifier id;
   case ptr of
     | ObjPointer obj_ptr -> readObject obj_ptr
     | _ -> error}

(* Look up an identifier for an object and get its value as an integer *)
op lookupIdentifierInt (id:Identifier) : Monad Int =
  {val <- lookupIdentifierValue id;
   case val of
     | V_int (_, i) -> return i
     | _ -> error}

(* Look up the address of an identifier *)
op lookupIdentifierAddr (id:Identifier) : Monad Value =
  {ptr_and_tp <- lookupIdentifier id;
   return (V_pointer ptr_and_tp)}


%subsection (* Computations on integers *)

(* We can remove the constructors of integer values, and retrieve their integer
values. It is an error to do that on non-integer values. If the value is an
undefined integer, a non-standard outcome is produced. *)

op intOfValue (val:Value) : Monad Int =
  case val of
  | V_int (_, i) -> return i
  | V_undefined ty -> if integerType? ty then raiseErr Err_nonstd else error
  | _ -> error

(* Create an integer value of a given type. It is an error if the given type is
   not an integer type, or if the integer does not fit in the given type. *)
op valueOfInt (i : TypedInt) : Value =
   V_int i

(* Create a list of bits from an integer, given a type *)
op bitsOfInt (ty:Type, i:Int |
                integerType? ty && i memb? rangeOfIntegerType ty) : List Bit =
  tcNumber (i, typeBits ty)

(* Create a value from a list of bits, given a type *)
op valueOfBits (bits:List Bit, ty:Type |
                  integerType? ty && length bits <= typeBits ty) : Value =
   let i =
     if length bits = 0 then 0
     else if signedIntegerType? ty then toNat bits
     else toInt bits
   in
   V_int (ty, i)

(* Each scalar type has a "zero" value. For integers, it is the representation
of the mathematical 0. For pointers, it is the null pointer. *)

op zeroOfScalarType (ty:Type | scalarType? ty) : Value =
  if integerType? ty then valueOfInt (ty, 0) else V_nullpointer ty

(* The following predicate tests whether a scalar value is 0 or not. The result
is an error if the value is not scalar, and non-standard if it is undefined. *)

op zeroScalarValue? (val:Value) : Monad Bool =
  if scalarValue? val then
    if embed? V_undefined val then raiseErr Err_nonstd
    else return (val = zeroOfScalarType (typeOfValue val))
  else
    error

(* It is useful to introduce Specware constants for the signed ints 0 and 1,
because they are returned by some operators, as formalized later. *)

op int0 : Value = valueOfInt (T_sint, 0)
op int1 : Value = valueOfInt (T_sint, 1)


%subsection (* Conversions *)

%subsubsection (* Integer conversions *)

(* An integer value can be converted into (a value of) an(other) integer type
[ISO 6.3.1.3].

The conversion is described in terms of the mathematical value of the integer.
If the new type can represent it, the (mathematical) value is unchanged [ISO
6.3.1.3/1].

Otherwise, the outcome depends on whether the new type is unsigned or not. Note
that the new type could be 'char', which is classified as neither a signed nor
an unsigned integer type [ISO 6.2.5/4, 6.2.5/6] (cf. ops 'signedIntegerType?'
and 'unsignedIntegerType?'). But according to [ISO 6.2.5/15] the 'char' type has
the same behavior as either signed or unsigned 'char', and this choice is
captured by ops 'plainCharsAreSigned' and 'plainCharsAreUnsigned', introduced
earlier.

If the type is unsigned, we find the (unique) mathematical integer i' that is
representable in the type and differs from the original mathematical integer i
by k times the maximum representable integer in the type plus 1, where k can be
negative or positive, capturing the repeated subtraction or addition mentioned
in [ISO 6.3.1.3/2].

If the new type is signed, the outcome is non-standard [ISO 6.3.1.3/3]. *)

op convertInteger (val:Value, ty:Type | integerType? ty) : Monad Value =
  {i <- intOfValue val;
   if i memb? rangeOfIntegerType ty then
     return (valueOfInt (ty, i))
   else if unsignedIntegerType? ty || (plainCharsAreUnsigned && ty = T_char) then
     let max1:Nat = maxOfIntegerType ty + 1 in
     let i':Int = the(i':Int) i' memb? rangeOfIntegerType ty &&
                              (ex(k:Int) i' = i + k * max1) in
     return (valueOfInt (ty, i'))
   else
     raiseErr Err_nonstd}

(* In terms of the bits that comprise the integer values, integer conversions
correspond to zero-extension, sign-extension, truncation, or no change.

Zero-extension occurs when the original value is unsigned and the new type has
more bits than the original value, regardless of whether the new type is signed
or unsigned.

Sign-extension occurs when the original value is signed and the new type has
more bits than the original value, regardless of whether the new type is signed
or unsigned.

Truncation occurs when the new type has fewer bits than the original value,
regardless of whether the new type is signed or unsigned and whether the
original value is signed or unsigned.

No change occurs when the new type has the same number of bits as the original
value, regardless of whether the new type is signed or unsigned and whether the
original value is signed or unsigned. *)

(*
theorem convertInteger_zero_extension is
  fa (val:Value, ty:Type, bits:Bits, newval:Value, newty:Type)
    typeOfValue val = ty &&
    (unsignedIntegerType? ty || ty = char && plainCharsAreUnsigned) &&
    bitsOfIntegerValue val = ok bits &&
    integerType? newty &&
    typeBits newty > typeBits ty &&
    convertInteger (val, newty) = ok newval =>
    bitsOfIntegerValue newval = ok (extendLeft (bits, B0, typeBits newty))

theorem convertInteger_sign_extension is
  fa (val:Value, ty:Type, bits:Bits, newval:Value, newty:Type)
    typeOfValue val = ty &&
    (signedIntegerType? ty || ty = char && plainCharsAreSigned) &&
    bitsOfIntegerValue val = ok bits &&
    integerType? newty &&
    typeBits newty > typeBits ty &&
    convertInteger (val, newty) = ok newval =>
    bitsOfIntegerValue newval = ok (signExtend (bits, typeBits newty))

theorem convertInteger_truncation is
  fa (val:Value, ty:Type, bits:Bits, newval:Value, newty:Type)
    typeOfValue val = ty &&
    integerType? ty &&
    bitsOfIntegerValue val = ok bits &&
    integerType? newty &&
    typeBits newty < typeBits ty &&
    convertInteger (val, newty) = ok newval =>
    bitsOfIntegerValue newval = ok (suffix (bits, typeBits newty))

theorem convertInteger_no_change is
  fa (val:Value, ty:Type, bits:Bits, newval:Value, newty:Type)
    typeOfValue val = ty &&
    bitsOfIntegerValue val = ok bits &&
    integerType? newty &&
    typeBits newty = typeBits ty &&
    convertInteger (val, newty) = ok newval =>
    bitsOfIntegerValue newval = ok bits
*)


%subsubsection (* Integer promotions *)

(* At run time, integer promotion [ISO 6.3.1.1/2] can be expressed as a mapping
from values to values: the value is converted to the type returned by op
'promoteType'. *)

op promoteValue (val:Value) : Monad Value =
  if integerValue? val then
    convertInteger (val, promoteType (typeOfValue val))
  else
    error


%subsubsection (* Usual arithmetic conversions *)

(* At run time, the 'usual arithmetic conversions' [ISO 6.3.1.8] can be
expressed, in our formalization, as a mapping from pairs of values to the
required result type for arithmetic operations on those two values; we also
bundle this with getting the integer values of the two values *)

op arithConvertValues (val1:Value, val2:Value) : Monad (Type * Int * Int) =
  if arithmeticValue? val1 && arithmeticValue? val2 then
    let ty = arithConvertTypes (typeOfValue val1, typeOfValue val2) in
    {i1 <- intOfValue val1;
     i2 <- intOfValue val2;
     return (ty, i1, i2)}
  else
    error


%subsubsection (* Casts *)

(* Casts convert an expression from one scalar type to another [ISO 6.5.4].
Recall that the scalar types are the integer types, the floating-point types
(which we do not include here), and the pointer types.

The case of casting between two integer types was already covered above by
convertInteger.

Converting an integer to a pointer yields an implementation-defined result [ISO
6.3.2.3/5], and could yield a trap representation (i.e., an undefined pointer),
so this is what we do here. This means that integers can never be converted to
pointers. The exception is that converting an expression with value 0 to a
pointer yields a null pointer [ISO 6.3.2.3/3].

Converting a pointer to an integer is implementation-defined, and need not in
fact ever yield an integer in the range of any integer type, in which case the
result is undefined [ISO 6.3.2.3/6]. This is what we do here, meaning that
pointers can never be converted to integers.

Otherwise, we allow any pointer type to be converted to any other pointer type,
as long as they are both object pointer types or both function pointer types.
The only requirement is that, when a pointer is converted to another pointer
type and then back again, the result should be equal to the original value of
the pointer [ISO 6.3.2.3/1, ISO 6.3.2.3/7, ISO 6.3.2.3/8]. We deviate from the
standard slightly, however, in that we ignore alignment [ISO 6.2.8]; in fact,
our formalization acts as if all types had alignment 1. *)
op castValue (tp:Type, val:Value | scalarType? tp) : Monad Value =
  let val_tp = typeOfValue val in
  if (integerType? val_tp && integerType? tp) then
    convertInteger (val, tp)
  else if (integerType? val_tp && pointerType? tp) then
    (case (val, tp) of
       | (V_int (_, 0), T_pointer ptr_tp) -> return (V_nullpointer ptr_tp)
       | _ -> return (V_undefined tp))
  else if (pointerType? val_tp && integerType? tp) then
    (case val of
       | V_nullpointer _ -> return (V_int (tp, 0))
       | _ -> return (V_undefined tp))
  else if (functionPointerType? val_tp && functionPointerType? tp) ||
    (~(functionPointerType? val_tp) && ~(functionPointerType? tp)) then
    case (val, tp) of
      | (V_pointer (_, ptr), T_pointer ptr_tp) ->
        return (V_pointer (ptr_tp, ptr))
      | (V_nullpointer _, T_pointer ptr_tp) ->
        return (V_nullpointer ptr_tp)
      | (V_undefined _, _) -> return (V_undefined tp)
  else
    error


%subsubsection (* Assignment conversions *)

(* In a simple assignment [ISO 6.5.16.1], which is the only form of assignment
we allow in our C subset, the value of the right operand (the one being
assigned) is converted to the type of the left operand (the one being
overwritten) before storing it. In our C subset, with no atomic or qualified
types and no '_Bool' type, this conversion requires the two operands to be [ISO
6.5.16.1/1]: (i) two arithmetic operands; (ii) two compatible structures; (iii)
two pointers to compatible types; (iv) a pointer to a non-void type and a
pointer to void; or (v) a pointer (left) and a null pointer constant (right).

In case (i), the right operand is converted into the type of the left operand
and stored into it. In case (ii), the right operand structure is stored into the
left operand, unchanged, and similarly with case (iii). Case (iv) and (v) are
handled by casting the right-hand side to the left-hand side.

Note that the same conversions apply to conditional expressions [ISO 6.5.15]. *)
op convertForAssignment (val:Value, ty:Type) : Monad Value =
  if arithmeticType? ty then
    convertInteger (val, ty)
  else if compatibleTypes? (typeOfValue val, ty) then
    return val
  else if
    (typeOfValue val = T_pointer T_void && embed? T_pointer ty) ||
    (ty = T_pointer T_void && embed? T_pointer (typeOfValue val)) then
    castValue (ty, val)
  else
    error


%subsection (* Integer constants *)

(* An integer constant evaluates to an integer value of the type returned by op
'checkIntegerConstant', if any. Op 'integerConstantValue' returns the
mathematical integer of the value of an integer constant. Thus, we can define
the evaluation of integer constants in terms of the value of the inferred type
whose mathematical integer value is the one returned by op 'integerConstValue'.
If the constant is too large to fit in a value, error is returned. *)

op evaluateIntegerConstant (c:IntegerConstant) : Monad Value =
  {tp <- liftOption (integerConstantType c);
   return (valueOfInt (tp, integerConstantValue c))}


%subsection (* Unary and binary operators *)

(* The unary '+' operator requires an arithmetic operand [ISO 6.5.3.3/1] and
just returns the promoted operand [ISO 6.5.3.3/2]. Note that op 'promoteValue'
returns an error if the value is not arithmetic. *)

op operator_PLUS (val:Value) : Monad Value =
  promoteValue val

(* The unary '-' operator requires an arithmetic operand [ISO 6.5.3.3/1] and
returns the negative of its promoted operand [ISO 6.5.3.3/3].

If the operand is unsigned, we follow the laws of arithmetic modulo MAX + 1
(where MAX is maximum integer representable in the operand's type) [ISO
6.2.5/9].

If the operand is signed and its negative cannot be represented in the operand's
type, the behavior is undefined [ISO 6.5/5]. *)

op operator_MINUS (val:Value) : Monad Value =
  {val' <- promoteValue val;
   ty <- return (typeOfValue val');
   x <- intOfValue val';
   let y = - x in
   if unsignedIntegerType? ty then
     return (valueOfInt (ty, y modF (maxOfIntegerType ty + 1)))
   else
     if y memb? rangeOfIntegerType ty then
       return (valueOfInt (ty, y))
     else
       raiseErr Err_nonstd}

(* The '~' operator requires an integer operand [ISO 6.5.3.3/1] and returns the
bitwise complement of the promoted operand [ISO 6.5.3.3/4]. *)

op operator_NOT (val:Value) : Monad Value =
  {val' <- promoteValue val;
   x <- intOfValue val';
   bits <- return (bitsOfInt (typeOfValue val', x));
   return (valueOfBits (map not bits, typeOfValue val'))}

(* The '!' operator requires a scalar operand [ISO 6.5.3.3/1] and returns the
signed int 1 or 0 depending on whether the operator compares equal or unequal to
0 [ISO 6.5.3.3/5]. *)

op operator_NEG (val:Value) : Monad Value =
  {isZero <- zeroScalarValue? val;
   if isZero then return int1 else return int0}

(* The binary '*' operator requires arithmetic operands [ISO 6.5.5/2], performs
the usual arithmetic conversions [ISO 6.5.5/3], and returns the product [ISO
6.5.5/4]. Note that op arithConvertValues returns an error if any of the values
is not arithmetic.

If the operands are unsigned, we follow the laws of arithmetic modulo MAX+1
(where MAX is maximum integer representable in the operand's type) [ISO
6.2.5/9].

If the operands are signed and their product cannot be represented in the
operand's type, the behavior is undefined [ISO 6.5/5]. *)

op operator_MUL (val1:Value, val2:Value) : Monad Value =
  {(ty, x1, x2) <- arithConvertValues (val1, val2);
   let y = x1 * x2 in
   if unsignedIntegerType? ty then
     return (valueOfInt (ty, y modF (maxOfIntegerType ty + 1)))
   else
     if y memb? rangeOfIntegerType ty then
       return (valueOfInt (ty, y))
     else
       nonstd}

(* The '/' operator requires arithmetic operands [ISO 6.5.5/2], performs the
usual arithmetic conversions [ISO 6.5.5/3], and returns the quotient [ISO
6.5.5/5], truncated towards 0 [ISO 6.5.5/6]. If the divisor is 0, the behavior
is undefined [ISO 6.5.5/5].

If the operands are unsigned, we follow the laws of arithmetic modulo MAX+1
(where MAX is maximum integer representable in the operand's type) [ISO
6.2.5/9].

If the operands are signed and their quotient cannot be represented in the
operand's type, the behavior is undefined [ISO 6.5/5]. *)

op operator_DIV (val1:Value, val2:Value) : Monad Value =
  {(ty, x1, x2) <- arithConvertValues (val1, val2);
   if x2 = 0 then raiseErr Err_nonstd else
   let y = x1 divT x2 in
   if unsignedIntegerType? ty then
     return (valueOfInt (ty, y modF (maxOfIntegerType ty + 1)))
   else
     if y memb? rangeOfIntegerType ty then
       return (valueOfInt (ty, y))
     else
       nonstd}

(* The '%' operator requires arithmetic operands [ISO 6.5.5/2], performs the
usual arithmetic conversions [ISO 6.5.5/3], and returns the remainder [ISO
6.5.5/5], i.e. the difference between the first operands and the product of the
second operand by the quotient [ISO 6.5.5/6]. If the divisor is 0, the behavior
is undefined [ISO 6.5.5/5].

If the operands are unsigned, we follow the laws of arithmetic modulo MAX+1
(where MAX is maximum integer representable in the operand's type) [ISO
6.2.5/9].

If the operands are signed and their remainder cannot be represented in the
operand's type, the behavior is undefined [ISO 6.5/5]. *)

op operator_REM (val1:Value, val2:Value) : Monad Value =
  {(ty, x1, x2) <- arithConvertValues (val1, val2);
   if x2 = 0 then nonstd else
   let y = x1 modT x2 in
   if unsignedIntegerType? ty then
     return (valueOfInt (ty, y modF (maxOfIntegerType ty + 1)))
   else
     if y memb? rangeOfIntegerType ty then
       return (valueOfInt (ty, y))
     else
       nonstd}

(* The binary '+' operator requires either that both operands are arithmetic or
that one is a pointer and the other is an integer [ISO 6.5.6/2]. In the first
case, the usual arithmetic conversions are applied [ISO 6.5.6/4], and the result
is the sum of the operands [ISO 6.5.6/5].  If the operands are unsigned, we
follow the laws of arithmetic modulo MAX+1 (where MAX is maximum integer
representable in the operand's type) [ISO 6.2.5/9]. If the operands are signed
and their sum cannot be represented in the operand's type, the behavior is
implementation-defined. (Note that [ISO 6.5/5] says this is undefined, but [ISO
J.3.5 says that this is implementation-defined]).

If one of the operands is a pointer to the ith element of an array object of
type T, then adding integer j turns this into a pointer to the i+j-th element
(starting at 0) of the same array object, provided the array has at least i+j
elements (meaning that the result can point to one past the last element of the
array) [ISO 6.5.6/8]. If the array does not have i+j elements, or i+j is
negative, the result is undefined. *)

op operator_ADD (val1:Value, val2:Value) : Monad Value =
  if arithmeticValue? val1 && arithmeticValue? val2 then
    {(ty, x1, x2) <- arithConvertValues (val1, val2);
     let y = x1 + x2 in
     if unsignedIntegerType? ty then
       return (valueOfInt (ty, y modF (maxOfIntegerType ty + 1)))
     else
       if y memb? rangeOfIntegerType ty then
         return (valueOfInt (ty, y))
       else
         nonstd}
  else if integerValue? val1 && pointerValue? val2 then
    operator_ADD (val2, val1)
  else if pointerValue? val1 && integerValue? val2 then
    case val1 of
      | V_pointer (tp, ObjPointer (OD_Subscript (obj, i))) ->
        {j <- intOfValue val2;
         arr <- readObject obj;
         case arr of
           | V_array (_, elems) ->
             if i+j >= 0 && i+j <= length elems then
               return (V_pointer (tp, ObjPointer (OD_Subscript (obj, i+j))))
             else error}
      | _ -> error
  else error


(* The binary '-' operator requires that either: both operands are arithmetic;
both operands are pointers to objects of the same type; or the left operand is a
pointer to an object and the right operand is an integer [ISO 6.5.6/3]. In the
first case, subtraction performs the usual arithmetic conversions [ISO 6.5.6/4],
and returns the difference [ISO 6.5.6/6]. If the operands are unsigned, we
follow the laws of arithmetic modulo MAX+1 (where MAX is maximum integer
representable in the operand's type) [ISO 6.2.5/9]. If the operands are signed
and their difference cannot be represented in the operand's type, the behavior is
undefined [ISO 6.5/5].

FIXME HERE: we have not yet implemented pointer difference
*)

op operator_SUB (val1:Value, val2:Value) : Monad Value =
  if arithmeticValue? val1 && arithmeticValue? val2 then
    {(ty, x1, x2) <- arithConvertValues (val1, val2);
     let y = x1 - x2 in
     if unsignedIntegerType? ty then
       return (valueOfInt (ty, y modF (maxOfIntegerType ty + 1)))
     else if y memb? rangeOfIntegerType ty then
       return (valueOfInt (ty, y))
     else
       error}
  else if pointerValue? val1 && arithmeticValue? val2 then
    unimplemented
  else if pointerValue? val1 && pointerValue? val2 then
    unimplemented
  else error


(* The '<<' operator requires integer operands [ISO 6.5.7/2], promotes them, and
left-shifts the first operand E1 by the number of positions E2 indicated by the
second operand, filling the vacated bits with 0 [ISO 6.5.7/4]. If E2 is negative
or greater than or equal to the size of E1, the behavior is undefined [ISO
6.5.7/3].

If E1 is unsigned, the result of the left-shift is E1 * 2^E2 modulo MAX+1 (where
MAX is the maximum integer representable in E1's type) [ISO 6.5.7/4].

If E1 is signed, there are two cases: (i) if E1 is non-negative and E1 * 2^E2 is
representable in E1's type, that is the resulting value; (ii) otherwise (i.e. E1
is negative or E1 * 2^E2 is not representable), the behavior is undefined [ISO
6.5.7/4]. *)

op operator_SHL (val1:Value, val2:Value) : Monad Value =
  {val1' <- promoteValue val1;
   val2' <- promoteValue val2;
   ty <- return (typeOfValue val1');
   x1 <- intOfValue val1';
   x2 <- intOfValue val2';
   if x2 < 0 || x2 >= typeBits ty then nonstd else
   let y = x1 * 2**x2 in
   if unsignedIntegerType? ty then
     return (valueOfInt (ty, y modF (maxOfIntegerType ty + 1)))
   else
     if x1 >= 0 && y memb? rangeOfIntegerType ty then
       return (valueOfInt (ty, y))
     else
       nonstd}

(*
theorem operator_SHL is
  fa (val1:Value, bits1:Bits, val2:Value, d:Nat, val:Value, bits:Bits)
    operator_SHL (val1, val2) = ok val &&
    bitsOfIntegerValue val1 = ok bits1 &&
    mathIntOfValue val2 = ok d &&
    bitsOfIntegerValue val = ok bits =>
    (ex (val1':Value, bits1':Bits)
       promoteValue val1 = ok val1' &&
       bitsOfIntegerValue val1' = ok bits1' &&
       bits = shiftLeft (bits1', d))
*)

(* The '>>' operator requires integer operands [ISO 6.5.7/2], promotes them, and
right-shifts the first operand E1 by the number of positions E2 indicated by the
second operand [ISO 6.5.7/5]. If E2 is negative or greater than or equal to the
size of E1, the behavior is undefined [ISO 6.5.7/3].

If E1 is unsigned, or if it signed and non-negative, the result is the integral
part of the quotient E1 / 2^E2 [ISO 6.5.7/5]. Otherwise, the result is
implementation-dependent [ISO 6.5.7/5]. *)

op operator_SHR (val1:Value, val2:Value) : Monad Value =
  {val1' <- promoteValue val1;
   val2' <- promoteValue val2;
   ty <- return (typeOfValue val1');
   x1 <- intOfValue val1';
   x2 <- intOfValue val2';
   if x2 < 0 || x2 >= typeBits ty then nonstd else
   let y = x1 divT 2**x2 in
   if unsignedIntegerType? ty ||
      signedIntegerType? ty && x1 >= 0 then
     return (valueOfInt (ty, y))
   else
     nonstd}

(*
theorem operator_SHR is
  fa (val1:Value, bits1:Bits, val2:Value, d:Nat, val:Value, bits:Bits)
    operator_SHL (val1, val2) = ok val &&
    bitsOfIntegerValue val1 = ok bits1 &&
    mathIntOfValue val2 = ok d &&
    bitsOfIntegerValue val = ok bits =>
    (ex (val1':Value, bits1':Bits)
       promoteValue val1 = ok val1' &&
       bitsOfIntegerValue val1' = ok bits1' &&
       bits = shiftRightUnsigned (bits1', d))
*)

(* The '<', '>', '<=', and '>=' operators require real operands (our C subset
excludes pointer comparisons) [ISO 6.5.8/2], perform the usual arithmetic
conversions [ISO 6.5.8/3], and return the signed int 1 or 0 depending on whether
the comparison is true or false [ISO 6.5.8/6]. *)

op operator_LT (val1:Value, val2:Value) : Monad Value =
  {(_, x1, x2) <- arithConvertValues (val1, val2);
   if x1 < x2 then return int1 else return int0}

op operator_GT (val1:Value, val2:Value) : Monad Value =
  {(_, x1, x2) <- arithConvertValues (val1, val2);
   if x1 > x2 then return int1 else return int0}

op operator_LE (val1:Value, val2:Value) : Monad Value =
  {(_, x1, x2) <- arithConvertValues (val1, val2);
   if x1 <= x2 then return int1 else return int0}

op operator_GE (val1:Value, val2:Value) : Monad Value =
  {(_, x1, x2) <- arithConvertValues (val1, val2);
   if x1 >= x2 then return int1 else return int0}

(* The '==' and '!=' operators require (i) two arithmetic operands, or (ii) two
pointers to compatible types, or (iii) a pointer to a non-void type and a
pointer to void [ISO 6.5.9/2]. (The case of a null pointer constant, mentioned
in [ISO 6.5.9/2] applies to expressions, but with values, a null pointer
constant just evaluates to a null pointer of some type.)

If the two operands are arithmetic, the usual arithmetic conversions are
performed and the results are compared [ISO 6.5.9/4].

If the two operands are pointers, they are compared for equality. If both are
non-null, they are equal iff they reference the same object. If both are null,
they are considered equal [ISO 6.3.2.3/4]. If one is null and the other
non-null, they are considered not equal [ISO 6.3.2.3/3]. If any pointer is
undefined, the outcome is non-standard.

In either case, the signed int 1 or 0 is returned depending on whether the
comparison is true or false [ISO 6.5.9/3].

Note that if any value is undefined, the outcome is non-standard because we do
not know the exact values and therefore we do not know the true result of
comparing them.

Note that the '!=' operator returns the "opposite" of the == operator, i.e. '!='
returns 0 if '==' returns 1, and 1 if '==' returns 0. *)

op operator_EQ (val1:Value, val2:Value) : Monad Value =
  if arithmeticValue? val1 && arithmeticValue? val2 then
    {(_, x1, x2) <- arithConvertValues (val1, val2);
     if x1 = x2 then return int1 else return int0}
  else if pointerValue? val1 && pointerValue? val2 &&
          (compatibleTypes? (typeOfValue val1, typeOfValue val2) ||
           typeOfValue val1 = T_pointer T_void ||
           typeOfValue val2 = T_pointer T_void) then
    if embed? V_undefined val1 || embed? V_undefined val2 then
      raiseErr Err_nonstd
    else if embed? V_nullpointer val1 && embed? V_nullpointer val2
            || val1 = val2 then
      return int1
    else
      return int0
  else
    error

op operator_NE (val1:Value, val2:Value) : Monad Value =
  {eq_result <- operator_EQ (val1, val2);
   if eq_result = int0 then return int1 else return int0}

(* The binary '&' operator, the '^' operator, and the '|' operator require
integer operands [ISO 6.5.10/2, 6.5.11/2, 6.5.12/2], perform the usual
arithmetic conversions [ISO 6.5.10/3, 6.5.11/3, 6.5.12/3], and return the
bitwise AND [ISO 6.5.10/4], exclusive OR [ISO 6.5.11/4], and inclusive OR [ISO
6.5.12/4] of their operands. *)

op operator_AND (val1:Value, val2:Value) : Monad Value =
  {(ty, x1, x2) <- arithConvertValues (val1, val2);
   let bits1 = bitsOfInt (ty, x1) in
   let bits2 = bitsOfInt (ty, x2) in
   return (valueOfBits (map2 (and) (bits1, bits2), ty))}

op operator_XOR (val1:Value, val2:Value) : Monad Value =
  {(ty, x1, x2) <- arithConvertValues (val1, val2);
   let bits1 = bitsOfInt (ty, x1) in
   let bits2 = bitsOfInt (ty, x2) in
   return (valueOfBits (map2 (xor) (bits1, bits2), ty))}

op operator_IOR (val1:Value, val2:Value) : Monad Value =
  {(ty, x1, x2) <- arithConvertValues (val1, val2);
   let bits1 = bitsOfInt (ty, x1) in
   let bits2 = bitsOfInt (ty, x2) in
   return (valueOfBits (map2 (ior) (bits1, bits2), ty))}

(* The logical 'and' and 'or' operators are different from the above operators
because the second operand is only evaluated depending on the value of the
first. This is represented by having the functions implementing them take in
computations instead of values, in order to give them control of when and
whether the computations are executed. *)

op operator_LAND (m1:Monad Value, m2:Monad Value) : Monad Value =
   {val1 <- m1;
    isZero1 <- zeroScalarValue? val1;
    if isZero1 then return int0
    else
      {val2 <- m2;
       isZero2 <- zeroScalarValue? val2;
       if isZero2 then return int0 else return int1}}

op operator_LOR (m1:Monad Value, m2:Monad Value) : Monad Value =
   {val1 <- m1;
    isZero1 <- zeroScalarValue? val1;
    if ~isZero1 then return int1
    else
      {val2 <- m2;
       isZero2 <- zeroScalarValue? val2;
       if isZero2 then return int0 else return int1}}


%subsection (* Type names *)

(* A type name denotes a type. The following op returns the type denoted by a
type name w.r.t. a TypedefTable, by expanding all the typedef names in the type
name. Note that this is not done in the Monad, so that it can be called by
evalTranslationUnit. *)
(* FIXME HERE: update docs above for new type... *)
op expandTypeName (xenv:TranslationEnv, tyn:TypeName) : Option Type =
  case tyn of
  | TN_typedef tdn -> xenv.xenv_typedefs tdn
  | TN_pointer tyn ->
    {ty <- expandTypeName (xenv, tyn);
     Some (T_pointer ty)}
  | TN_array (tyn, n) ->
    {ty <- expandTypeName (xenv, tyn);
     Some (T_array (ty, n))}
  | TN_struct tag ->
    {membs <- xenv.xenv_structures tag;
     Some (T_struct (Some tag, membs))}
  | TN_char  ->  Some T_char
  | TN_uchar  -> Some T_uchar
  | TN_schar  -> Some T_schar
  | TN_ushort -> Some T_ushort
  | TN_sshort -> Some T_sshort
  | TN_uint   -> Some T_uint
  | TN_sint   -> Some T_sint
  | TN_ulong  -> Some T_ulong
  | TN_slong  -> Some T_slong
  | TN_ullong -> Some T_ullong
  | TN_sllong -> Some T_sllong
  | TN_void   -> Some T_void

(* Monadic version of the above, that looks up the current TypedefTable *)
op expandTypeNameM (tyn:TypeName) : Monad Type =
  {r <- askR;
   liftOption (expandTypeName (r.r_xenv, tyn))}


%subsection (* Expressions *)

(* Except for a few special cases, array expression values are converted to
pointers [ISO 6.3.2.1], so we define the type ExpressionValue as the type of
values other than array values. *)
type ExpressionValue = {v:Value | ~(arrayValue? v)}

(* LValues evaluate to a pair of a Type and a Pointer, so we define the type
LValueResult as that type here *)
type LValueResult = Type * Pointer

(* In all but a handfull of special cases, the result of an expression is
   converted to a value that is not an array or a function [ISO 6.3.2.1].
   Lvalues are converted to the values of the objects designated by them, array
   values are converted to pointers to their first element, and function values
   are converted to pointers to those function values. We capture all of these
   conversions as a process called lvalue conversion; although the C spec
   defines lvalue conversion as only the first of these three conversions [ISO
   6.3.2.1/2], the only way to get an array value is through an lvalue, and we
   are lumping together function designators with lvalues (see the discussion
   above type Expression), so this view is consistent with the C spec. It is
   implemented as a function from a pair of a pointer and a type, which is the
   result of evaluating an lvalue, to an ExpressionValue.

   The C spec is rather complex and hard to understand in relation to how the
   types of lvalues and the types of the values read from them relate during
   lvalue conversion. The value resulting from lvalue conversion is required to
   have the type of the lvalue [ISO 6.3.2.1/2], but also the lvalue used to
   access an object is required to either have the effective type of the object,
   if any, or character type [ISO 6.5/7]; the effective type of an object is its
   declared type for automatic and static objects and the last type used to
   assign to it, if any, for allocated objects [ISO 6.5/6]. The only way the
   type of an lvalue can differ from the effective type of the object referenced
   by it, however, is through an indirection operator acting on a pointer with
   the "wrong" type, either directly or as the left-hand side of one ore more
   array subscript and/or struct member operations; the only other lvalues are
   identifiers (on the left of zero or more array subscripts and/or struct
   member operations), which always refer to automatic or static objects of the
   same type as that of the identifier. It is still unclear what happens when a
   pointer is dereferenced at the "wrong" type, however; thus, we simply mark
   this behavior as "unimplemented" in our formalization.

   Note, however, that lvalue conversion is actually doing the work of the
   address indirection operator, whose behavior is undefined (i.e., an error) if
   the pointer is "invalid" [ISO 6.5.3.2/4]. This check is implemented by
   reading the value / function referenced by the pointer, and is done before
   the types are compared. Also, for function pointers, the type-check is not
   needed, since the spec seems to indicate [ISO 6.3.2.3/8] that changing the
   type of a function pointer only leads to undefined behavior when the wrong
   function type is called.

   FIXME HERE: still trying to understand the spec on these points; e.g., what
   if we dereference a pointer to a struct at a struct type that is a prefix of
   the struct pointer to? This seems like it must be supported by the
   standard...  *)
op lvalueConversion (tp: Type, ptr: Pointer) : Monad ExpressionValue =
  case (tp, ptr) of
    | (expr_tp, ObjPointer obj) ->
      {v <- readObject obj;
       if compatibleTypes? (expr_tp, typeOfValue v) then
         case v of
           | V_array (obj_tp, _) ->
             return (V_pointer (obj_tp, ObjPointer (OD_Subscript (obj, 0))))
           | _ -> return v
       else unimplemented }
    | (T_function fun_tp, FunPointer f_desig) ->
      {_ <- lookupFunction f_desig;
       return (V_pointer (T_function fun_tp, FunPointer f_desig))}
    | (_, FunPointer _) -> nonstd

(* Lift a unary monadic function on expression values to a function on
   ExpressionValue computations *)
op liftValueFun1 (f:ExpressionValue -> Monad ExpressionValue) (res_m: Monad ExpressionValue) : Monad ExpressionValue =
   {v <- res_m; f v }

(* Lift a binary monadic function on values to a function on
   ExpressionValue computations *)
op liftValueFun2 (f:ExpressionValue * ExpressionValue -> Monad ExpressionValue)
   (res_m1: Monad ExpressionValue, res_m2: Monad ExpressionValue) : Monad ExpressionValue =
   {v1 <- res_m1;
    v2 <- res_m2;
    f (v1, v2) }

(* Dereference a pointer value, as in the address indirection ('*') operator.
The operand must be a pointer [ISO 6.5.3.2/2], which is returned as an lvalue
result [ISO 6.5.3.2/4]. Note that the actual "action" of address indirection,
including reading the value of the pointer and checking whether the object has
not yet been deallocated, is handled in lvalue conversion, though the operator
defined here does do the checking for null and undefined pointer values. *)
op dereferencePointer (val:Value) : Monad LValueResult =
   case val of
     | V_pointer tp_and_ptr -> return tp_and_ptr
     | _ -> error

(* Access the struct member of an ExpressionValue as in the "." operator. *)
op accessStructValueMember (v:ExpressionValue, mem:Identifier) : Monad ExpressionValue =
   case v of
     | V_struct (_, members) ->
       (case assoc members mem of
          | Some val ->
            (* If the LHS is a struct value with the mem struct member,
               return the value of the mem struct member *)
            (* FIXME: what if the struct type disagrees with the type of
               the member value? *)
            return val
          | None ->
            (* If LHS is a struct without member mem, it is an error *)
            error)
     | _ ->
       (* Error if the LHS is a non-struct value *)
       error

(* Access the struct member of (the result of evaluating) an lvalue, returning
another lvalue result *)
op accessStructLValueMember (res: LValueResult, mem:Identifier) : Monad LValueResult =
   case res of
     | (T_struct struct_tp, ObjPointer obj) ->
       (* If the LHS is an object designator with struct type, then form the
          lvalue result for the mem member of that struct *)
       let memb_tps = expandStructMemberTypes struct_tp in
       (case assoc memb_tps mem of
          | Some tp ->
            return (tp, ObjPointer (OD_Member (obj, mem)))
          | None -> error)
     | _ ->
       (* Error if the LHS is a function designator or an object designator with
          non-struct type *)
       error


(* The following maps unary operations to functions on ExpressionValue
computations, where the input ExpressionValue computation is the result of
evaluating the operand of the operation. *)
op evaluatorForUnaryOp (uop:UnaryOp) : Monad ExpressionValue -> Monad ExpressionValue =
   case uop of
     | UOp_PLUS  -> liftValueFun1 operator_PLUS
     | UOp_MINUS -> liftValueFun1 operator_MINUS
     | UOp_NOT   -> liftValueFun1 operator_NOT
     | UOp_NEG   -> liftValueFun1 operator_NEG

(* The following maps binary operations to binary functions on ExpressionValue
computations. In a binary expression with any operator but '&&' and '||', first
the operands are evaluated, then the operator is applied. Since expressions in
our C subset have no side-effects, and since they both must be evaluated (in
some order), it makes no difference which one is evaluated first. For '&&' and
'||', the second expression is only evaluated if necessary. This could make a
difference for, e.g., multi-threaded code. *)
op evaluatorForBinaryOp (bop:BinaryOp) :
   Monad ExpressionValue * Monad ExpressionValue -> Monad ExpressionValue =
   case bop of
     | BinOp_MUL -> liftValueFun2 operator_MUL
     | BinOp_DIV -> liftValueFun2 operator_DIV
     | BinOp_REM -> liftValueFun2 operator_REM
     | BinOp_ADD -> liftValueFun2 operator_ADD
     | BinOp_SUB -> liftValueFun2 operator_SUB
     | BinOp_SHL -> liftValueFun2 operator_SHL
     | BinOp_SHR -> liftValueFun2 operator_SHR
     | BinOp_LT -> liftValueFun2 operator_LT
     | BinOp_GT -> liftValueFun2 operator_GT
     | BinOp_LE -> liftValueFun2 operator_LE
     | BinOp_GE -> liftValueFun2 operator_GE
     | BinOp_EQ -> liftValueFun2 operator_EQ
     | BinOp_NE -> liftValueFun2 operator_NE
     | BinOp_AND -> liftValueFun2 operator_AND
     | BinOp_XOR -> liftValueFun2 operator_XOR
     | BinOp_IOR -> liftValueFun2 operator_IOR
     | BinOp_LAND -> operator_LAND
     | BinOp_LOR -> operator_LOR


(* We now formalize all of expression evaluation, as follows.

FIXME HERE: update this documentation.

FIXME HERE: make sure the types are always correct during evaluation

A identifier (i.e., a variable) [ISO 6.5.1/2] evaluates to the object designator
that the variable references. Note that, in the official C semantics, an
undeclared identifier is an error, and is in fact a violation of syntax; in our
formalization, however, not only is an undeclared identifier valid
syntactically, it can also have a non-erroneous value, specifically in the case
of a global variable from another translation unit that was not declared in the
current translation unit using "extern". However, an undeclared identifier that
does not lead to an error in our formalization will not typecheck in our
formalization, and so in that sense it is "a violation of the syntax".

An integer constant [ISO 6.5.1/3] evaluates to the integer value formalized by
op 'evaluateIntegerConstant'. A unary or binary expression is evaluated using
evaluatorForUnaryOp or evaluatorForBinaryOp, respectively, defined above.

There are two special cases for evaluating the address '&' operator. The first
is that an expression of the form '&*E' evaluates to the same as E, i.e. '&' and
'*' are not applied [ISO 6.5.3.2/3]. The difference between the normal
evaluation procedure and this exception is visible, for instance, when 'E' is
null, or an 'undefined' value, as in this case *E would be undefined (i.e., an
error). The second special case for unary expressions is for an expression of
the form '&E[I]', which yields the same result as E+I [ISO 6.5.3.2/3].

A conditional expression requires a scalar first operand [ISO 6.5.15/2], which
it evaluates and compares with 0 [ISO 6.5.15/4]. Based on the result of the
comparison, the second or third operand is evaluated and returned [ISO
6.5.15/4], converted to the type that is the fourth argument of the 'cond'
constructor. This explains the reason for this fourth argument: without this
fourth argument, since only one of the second and third operands are evaluated,
we would not have enough information to calculate the type of the result, which
depends on the types of both second and third operands.

A structure member expression requires a structure as left operand [ISO
6.5.2.3/1]. The right operand must be a member of the structure [ISO 6.5.2.3/1].
If the left operand results in an object designator, the result is an object
designator extended with the right operand; if the left operand results in a
value, the result is the value of the member [ISO 6.5.2.3/3].

A structure pointer member expression requires a pointer to a structure as left
operand [ISO 6.5.2.3/2]. Even though [ISO 6.3.2.1/3] allows an array (of
structures) to be used as left operand because it is converted to a pointer, in
our formalization we are more strict and regard that behavior as an error. The
right operand must be a member of the structure [ISO 6.5.2.3/2]. The result is
an object designator, obtained by appending the member to the object designator
carried by the pointer [ISO 6.5.2.3/4].

An array subscripting expression requires a first operand that evaluates to an
object designator of an element i of an array, and a second operand that
evaluates to an integer j [ISO 6.5.2.1/1]. In order for the result to be well
defined, j must be non-negative and i + j must be less than the array's length
[ISO 6.5.6/8]. If well defined, the result is an object designator, obtained by
replacing the index i of the object designator with i+j. Note that if the first
operand is an array, it is converted to a pointer to an array's initial element,
i.e. i is 0 and thus the result is element j of the array, as expected.

As explained earlier, the null pointer constant has type 'void*', and therefore
it returns a null pointer to void. *)

op evaluateStrictExpr (expr:StrictExpression) : Monad ExpressionValue =
  case expr of
    | E_const c -> evaluateIntegerConstant c
    | E_addr (LV_star expr1) ->
      % Special treatment for exprs of the form '&(*E), which equal E
      evaluate expr1
    | E_addr (LV_subscript (expr1, expr2)) ->
      % Special treatment for exprs of the form '&(E1[E2]), which equal E1+E2
      evaluatorForBinaryOp BinOp_ADD (evaluate expr1, evaluate expr2)
    | E_addr lv ->
      {res <- evaluateLValue lv;
       return (V_pointer res)}
    | E_unary (uop, expr1) ->
      evaluatorForUnaryOp uop (evaluate expr1)
    | E_binary (expr1, bop, expr2) ->
      evaluatorForBinaryOp bop (evaluate expr1, evaluate expr2)
    | E_cond (expr1, expr2, expr3, tp_name) ->
      {val1 <- evaluate expr1;
       isZero <- zeroScalarValue? val1;
       ret_val <- if ~ isZero then evaluate expr2 else evaluate expr3;
       ty <- expandTypeNameM tp_name;
       convertForAssignment (ret_val, ty)}
    | E_member (expr1, mem) ->
      {v <- evaluateStrictExpr expr1;
       accessStructValueMember (v, mem)}
    | E_cast (tp_name, expr1) ->
      {tp <- expandTypeNameM tp_name;
       val1 <- evaluate expr1;
       castValue (tp, val1)}

op evaluateLValue (lv: LValue) : Monad LValueResult =
  case lv of
    | LV_ident var -> lookupIdentifier var
    | LV_star expr ->
      {v <- evaluate expr;
       dereferencePointer v}
    | LV_member (lv1, mem) ->
      {res <- evaluateLValue lv1;
       accessStructLValueMember (res, mem)}
    | LV_memberp (expr, mem) ->
      {v <- evaluate expr;
       res <- dereferencePointer v;
       accessStructLValueMember (res, mem)}
    | LV_subscript (expr1, expr2) ->
      (* Array subscripts E1[E2] are equivalent to *(E1+E2) [ISO 6.5.2.1/2]. *)
      {v1 <- evaluate expr1;
       v2 <- evaluate expr2;
       v_plus <- operator_ADD (v1, v2);
       dereferencePointer v_plus}

op evaluate (expr: Expression) : Monad ExpressionValue =
  case expr of
    | E_strict strict_expr -> evaluateStrictExpr strict_expr
    | E_lvalue lv -> {res <- evaluateLValue lv; lvalueConversion res}


(* FIXME: figure out how to state and prove this type safety theorem *)

(* Evaluating, in a state that satisfies the invariants, an expression that
satisfies the compile-time constraints w.r.t. the symbol table of the state,
does not yield an error. Furthermore, if a normal outcome occurs, the expression
result has the expression type inferred by the compile-time constraints. *)

(*
theorem expression_evaluation is
  fa (state:State, expr:Expression, ety:ExpressionType)
    invariants? state &&
    checkExpression (symbolTableOfState state, expr) = Some ety =>
    (case evaluate (state, expr) of
    | ok res -> typeOfExpressionResult (state, res) = ok ety
    | error -> false
    | nonstd -> true
    | nonterm -> true)
*)

(* It is useful to introduce an op to evaluate a sequence of expressions, one
after the other. *)

op evaluateAll (exprs:List Expression) : Monad (List ExpressionValue) =
  mapM evaluate exprs


%subsection (* Zero values *)

(* As formalized later, all the objects declared in our C subset are initialized
to 0. For structures and arrays, 0 means that all the members and elements are
recursively initialized to 0 [ISO 6.7.9/10]. To this end, the following op
returns the 0 value of the given type. When the type is a structure, the op
looks up its structure information in the state in order to recursively
calculate 0 values for all the members of the structure. The recursive call on
the members is achieved via the auxiliary op that returns a list of 0 values for
a list of types: the members are ordered according to their names, and a list of
0 values is generated in that order.

It is an error if the type to calculate a 0 value of, is 'void' or a structure
type not present in the state. It is also an error if there is some circularity
in the structures, which could cause the op not to terminate. Recall that the
non-circularity of the structures is part of the state invariants.

Note that zeroOfType itself is not defined in the Monad, but instead represents
errors using the Option type; this is so that TranslationUnits can be evaluated
outside the Monad as well. *)

(* FIXME HERE: rename typeHasSize? to capture it being a value type...? *)
op zeroOfType (tp:Type | objectType? tp) : Value =
  case tp of
    | T_struct (struct_tp) ->
      V_struct (struct_tp,
                map (fn (f,f_tp) -> (f, zeroOfType f_tp)) struct_tp.2)
    | T_array (elem_tp, n) ->
      V_array (elem_tp, repeat (zeroOfType elem_tp) n)
    | ty -> zeroOfScalarType ty

(* This just maps zeroOfType over tys *)
op zerosOfTypes (tys:List Type | forall? objectType? tys) : List Value =
   map zeroOfType tys


%subsection (* Statements *)

(* Perform a simple assignment of val to the result represented by res, which
must be an lvalue [ISO 6.5.6/2]. *)
op assignValue (res:LValueResult, val:Value) : Monad () =
  case res of
    | (ptr_tp, ObjPointer (OD_Allocated alloc_id)) ->
      (* Assignments to allocated objects can change their types [ISO 6.5/6], so
         we do not need to check the current type of allocated objects. However,
         we do need to ensure that the size of the new value is small enough to
         fit in the allocated object. *)
      {val' <- convertForAssignment (val, ptr_tp);
       (_, obj_size) <- (allocatedObjLens alloc_id).mlens_get ();
       if objectType? ptr_tp && obj_size >= sizeof ptr_tp then
         writeObject (OD_Allocated alloc_id, val')
       else
         error}
    | (ptr_tp, ObjPointer obj) ->
      (* Objects with a declared type (i.e., those in automatic or static
         storage) can only be accessed by an lvalue whose type is compatible
         with that declared type or char [ISO 6.5/6, ISO 6.5/7]. The declared
         type of an object can be found in our formalism by looking up the
         current value of the object. We do not implement modification of an
         object representation directly, i.e., via the char type. *)
      {val' <- convertForAssignment (val, ptr_tp);
       oldval <- readObject obj;
       if compatibleTypes? (ptr_tp, typeOfValue oldval) then
         writeObject (obj, val')
       else if characterType? ptr_tp then
         unimplemented
       else error}
    | _ -> error


(* We now formalize the execution of statements.

FIXME HERE: update this documentation!

The left operand of an assignment must denote an object [ISO 6.5.16/2,
6.5.16/3]. The left and right operands must be (i) two arithmetic operands, or
(ii) two compatible structures, or (iii) two pointers to compatible types, or
(iv) a pointer to a non-void type and a pointer to void, or (v) a pointer (left)
and a null pointer constant (right) [ISO 6.5.16.1/1]. Our C subset has no notion
of atomic, qualified, and unqualified types. The case of a left '_Bool' operand
does not apply to our C subset. In case (i), the right operand is converted into
the type of the left operand and stored into it. In case (ii), the right operand
structure is stored into the left operand, unchanged. We consolidate cases
(iii), (iv), and (v), which all involve pointers, by converting the right
operand pointer into the left operand's pointer type -- recall that op
'convertPointer' preserves the type safety of our C subset by disallowing
conversions between non-null pointers of incompatible types. We use op
'convertToPointerIfArray' on the right operand -- see discussion in comments for
op 'checkStatement'.

The condition of an 'if' statement is evaluated first, and a branch is executed
depending on whether the condition is 0 or not.

A 'return' statement removes the top frame of automatic storage, because the
function is exited. As explained above, we undefine all the pointers to objects
that existed in that frame.

When a block is entered, a new scope is added to the automatic storage. This new
scope is retracted when the block is exited. As explained above, when the scope
is retracted, we undefine all the pointers to objects that existed in that
scope.

The execution of a 'while' loop [ISO 6.8.5] yields 'nonterm' if there is a
stream (i.e. infinite sequence) of states that starts with the initial state and
such that for each state i in the stream (i) the controlling expression of the
loop always yields a non-0 value (i.e. the test is true) and (ii) executing the
loop body in the state i yields state i + 1 with the 'next' completion.
Otherwise, we repeatedly execute the loop until either the condition is false or
the body yields a 'return' statement completion: this is achieved by first
testing the condition, then (if true) executing a block consisting of the body
followed by a copy of the 'while' loop itself (if the body yields a 'return'
statement completion, the copy of the 'while' loop is not executed).

The execution of a 'do' loop [ISO 6.8.5] is equivalent to the execution of the
body of the loop followed by a 'while' loop that has the same controlling
expression and the same body as the 'do' loop.

The execution of a 'for' loop [ISO 6.8.5] is equivalent to the execution of the
statement used as first expression (if present), followed by a 'while' loop
whose test is the test of the 'for' and whose body consists of the body of the
'for' followed by the statement used as third expression (if present) [ISO
6.8.5.3/1]. If the test is absent from the 'for' loop, the execution is
equivalent to having the non-0 constant 1 as the test [ISO 6.8.5.3/2].

The argument expressions of a function call are evaluated, and the values passed
as arguments. Arrays are converted to pointers [ISO 6.3.2.1/3]. The arguments
are stored into a new scope in a new frame in automatic storage. The body of the
function must be a block, whose block items are extracted and executed (as
opposed to executing the whole block, which would otherwise create another
scope, which would be incorrect). If the function has a non-void return type but
fails to return a value, or returns a value that is not assignable to its return
type, it is an error. If the returned value is undefined, the behavior is
undefined.  Otherwise, the returned value is converted, as if by assignment,
into the return type [ISO 6.8.6.4/3]. If the function returns 'void', but a
value is returned, it is an error. In the absence of errors, function execution
results in a new state and an optional value (present iff the function has a
non-'void' return type). *)

op evalStatement (stmt:Statement) : Monad () =
  case stmt of
  | S_assign (lv, expr) ->
    {res <- evaluateLValue lv;
     val <- evaluate expr;
     assignValue (res, val)}
  | S_call (lhs_lv_opt, fun_expr, arg_exprs) ->
    (* For a function call, first evaluate the arguments and the function *)
    {arg_values <- evaluateAll arg_exprs;
     fun_value <- evaluate fun_expr;
     (* Next, look up the function and apply it to the args *)
     val_opt <-
       case fun_value of
         | V_pointer (_, FunPointer f_desig) ->
           {f <- lookupFunction f_desig; f arg_values}
         | _ -> error;
     (* Finally, assign the result to the LHS, if there is one *)
     case (lhs_lv_opt, val_opt) of
       | (None, _) -> return ()
       | (Some lv, Some val) ->
         {lhs_res <- evaluateLValue lv; assignValue (lhs_res, val)}
       | (Some _, None) -> error}
  | S_if (cond_expr, then_branch, else_branch_opt) ->
    (* For an if-statement, evaluate the condition, test if it is zero, and
       then, execute the then or else branch as appropriate *)
    {condition <- evaluate cond_expr;
     isZero <- zeroScalarValue? condition;
     if ~ isZero then
       evalStatement then_branch
     else
       case else_branch_opt of
         | Some else_branch -> evalStatement else_branch
         | None -> return ()}
  | S_return (Some expr) ->
    (* For a return statement with an expression, evaluate the expression and
       then return it from the current function. *)
    {val <- evaluate expr; returnFromFun (Some val)}
  | S_return None ->
    (* For a return with no expression, return None from the current function *)
    returnFromFun None
  | S_while (cond_expr, body) ->
    (* while loops use mfix (FIXME: document this...?) *)
    mfix (fn recurse -> fn unit ->
            {condition <- evaluate cond_expr;
             isZero <- zeroScalarValue? condition;
             if isZero then return () else
               {_ <- evalStatement body; recurse ()}}) ()
  | S_do (body, cond_expr) ->
    (* For do loops, execute the body once and then do a while loop *)
    {_ <- evalStatement body;
     evalStatement (S_while (cond_expr, body))}
  | S_for (stmt1, cond_expr, stmt3, body) ->
    (* For loops use mfix (FIXME: document this...?) *)
    {_ <- evalStatement stmt1;
     evalStatement (S_while (cond_expr,
                             S_block [BlockItem_statement body,
                                      BlockItem_statement stmt3]))}
  | S_block items ->
    withFreshLocalBindings empty (evalBlockItems items)

op evalBlockItems (items:List BlockItem) : Monad () =
  case items of
  | [] -> return ()
  | item::items' ->
    {_ <- evalBlockItem item;
     evalBlockItems items'}

op evalBlockItem (item:BlockItem) : Monad () =
  case item of
  | BlockItem_declaration (tp_name, id) ->
    {tp <- expandTypeNameM tp_name;
     addLocalBinding (id, V_undefined tp)}
  | BlockItem_statement stmt -> evalStatement stmt


%subsection (* Translation Units *)

(* Translation units are translated individually into "translated translation
units". In a standard UNIX environment, this is usually called "file
compilation", and the results are "object files", so we use these phrases
instead of the more cumbersome "translation of translation units" and
"translated translation units".

FIXME HERE: finish the following documentation!

compilation uses translation environments during the compilation,
but the results are just the top-level functions and the static objects with
their initial values. Note that a function in an object file need not be a
TopFunction, meaning that it can still depend on the function table, because we
have not yet "tied the knot"; this is done when we compile a whole program,
below.  *)

type ObjectFileElem =
  | ObjFile_Object Value
  | ObjFile_Function (TopFunction * FunType)
type ObjectFileBinding = Identifier * ObjectFileElem
type ObjectFileBindings = List ObjectFileBinding

type ObjectFile = {l:ObjectFileBindings | noRepetitions? (unzip l).1 }

(* FIXME HERE: make a type of association lists with no repetitions; or at least
make such a type for Identifier keys *)

op [a,b] filterMap (f : a -> Option b) (l : List a) : List b =
  case l of
    | [] -> []
    | x::l' ->
      (case f x of
         | Some y -> y :: filterMap f l'
         | None -> filterMap f l')

(* Get the object bindings in an object file *)
op objFileObjectBindings (ofile : ObjectFile) : {l:List (Identifier * Value) | noRepetitions? (unzip l).1 } =
  filterMap (fn (id, elem) ->
               case elem of
                 | ObjFile_Object val -> Some (id, val)
                 | _ -> None) ofile

(* Get the function bindings in an object file *)
op objFileFunBindings (ofile : ObjectFile) : {l:List (Identifier * (TopFunction * FunType)) |
                                                noRepetitions? (unzip l).1 } =
  filterMap (fn (id, elem) ->
               case elem of
                 | ObjFile_Function (f, ftp) -> Some (id, (f, ftp))
                 | _ -> None) ofile

op objFileFunTable (ofile : ObjectFile) : FunctionTable =
  fn (id,args) ->
    case assoc (objFileFunBindings ofile) id of
      | Some (f, _) -> f args
      | None -> error

op objFileFunTypes (ofile : ObjectFile) : FunctionTypeTable =
  foldr (fn ((id,(_,ftp)),tab) -> update tab id ftp)
    empty (objFileFunBindings ofile)

(* Combine two optional lists of object file bindings; this function will form
the monoid operation for the writer transformer of XUMonad, below *)
op objFileOptCombine (opt_obj1: Option ObjectFile,
                      opt_obj2: Option ObjectFile) : Option ObjectFile =
  {obj1 <- opt_obj1; obj2 <- opt_obj2;
   let obj_out = obj1 ++ obj2 in
   if noRepetitions? (unzip obj_out).1 then Some obj_out else None}

(* objFileOptCombine forms a commutative monoid, with Some [] as unit *)
theorem objFileOptCombine_id_l is
  fa (opt_obj) objFileOptCombine (opt_obj, Some []) = opt_obj
theorem objFileOptCombine_id_r is
  fa (opt_obj) objFileOptCombine (Some [], opt_obj) = opt_obj
theorem objFileOptCombine_assoc is
  fa (opt_obj1, opt_obj2, opt_obj3)
    objFileOptCombine (objFileOptCombine (opt_obj1, opt_obj2), opt_obj3) =
    objFileOptCombine (opt_obj1, objFileOptCombine (opt_obj2, opt_obj3))
theorem objFileOptCombine_comm is
  fa (opt_obj1, opt_obj2)
    objFileOptCombine (opt_obj1, opt_obj2) =
    objFileOptCombine (opt_obj2, opt_obj1)

(* The monad for evaluating translation units. This is a reader monad
transformer, applied to the state transformer for TranslationEnv, applied to the
option monad. The latter is for representing errors, and the state transformer
is to represent modifications of the translation environment. The reader monad
adds an input that is a map from include files (where the Boolean flag is true
for files included with the "<" and ">" delimiters and false for files included
using double quotes) to the effects they have on the current translation
environment if they are included. These latter effects are in the XUSubMonad
monad, which is just the state transformer applied to the option monad, since
having them be in XUMonad itself would lead to a circular definition of
XUMonad. *)
(* FIXME HERE: document the new XUSubMonad, which has an additional reader
transformer for FunctionTable and writer transformer for ObjectFileBindings *)
type XUSubMonad a =
   FunctionTable -> TranslationEnv ->
   Option (TranslationEnv * (Option ObjectFile * a))
type IncludeFileMap = IMap (String * Bool, XUSubMonad ())
type XUMonad a = IncludeFileMap -> XUSubMonad a

(* XUMonad's return *)
op [a] return (x:a) : XUMonad a =
   fn incls -> fn tab -> fn xenv -> Some (xenv, (Some [], x))

(* XUMonad's bind *)
op [a,b] monadBind (m : XUMonad a, f : a -> XUMonad b) : XUMonad b =
  fn incls -> fn tab -> fn xenv1 ->
   case m incls tab xenv1 of
     | Some (xenv2, (opt_obj1, a)) ->
       (case f a incls tab xenv2 of
          | Some (xenv3, (opt_obj2, b)) ->
            Some (xenv3, (objFileOptCombine (opt_obj1, opt_obj2), b))
          | None -> None)
     | None -> None

(* Run an XUMonad computation, given an IncludeFileMap and a FunctionTable *)
op [a] runXUMonad (m: XUMonad a) (incls: IncludeFileMap) (tab: FunctionTable)
    : Option (ObjectFileBindings * a) =
  {(_, (opt_obj, a)) <- m incls tab emptyTranslationEnv; obj <- opt_obj;
   Some (obj, a)}

(* Lift an XUMonad computation to a Monad computation, given an IncludeFileMap *)
(*
op [a] liftXU (incls: IncludeFileMap) (m: XUMonad a) : Monad a =
  liftOption (runXUMonad incls m)
*)

(* Get the current TranslationEnv *)
op xu_get : XUMonad TranslationEnv =
  fn incls -> fn tab -> fn xenv -> Some (xenv, (Some [], xenv))

(* Modify the current TranslationEnv *)
op xu_update (f: TranslationEnv -> TranslationEnv) : XUMonad () =
  fn incls -> fn tab -> fn xenv -> Some (f xenv, (Some [], ()))

(* Get the current list of include files and function table *)
op xu_ask : XUMonad (IncludeFileMap * FunctionTable) =
   fn incls -> fn tab -> fn xenv -> Some (xenv, (Some [], (incls,tab)))

(* Emit an object file binding *)
op xu_emit (obj: ObjectFileBinding) : XUMonad () =
   fn incls -> fn tab -> fn xenv -> Some (xenv, (Some [obj], ()))

(* An error in XUMonad *)
op [a] xu_error : XUMonad a = fn _ -> fn _ -> fn _ -> None

(* Test that a IMap in the current top-level does not have a binding for id *)
op [a] xu_errorIfBound (id : Identifier, f : TranslationEnv -> IMap (Identifier, a)) : XUMonad () =
  {xenv <- xu_get;
   if some? (f xenv id) then xu_error else return ()}

(* Lift an Option into XUMonad *)
op [a] liftOption_XU (opt_x : Option a) : XUMonad a =
  case opt_x of
    | Some x -> return x
    | None -> xu_error

(* Lift an XUSubMonad computation to an XUMonad computation *)
op [a] liftXUSubMonad (m: XUSubMonad a) : XUMonad a =
  fn _ -> m

(* The map function for XUMonad *)
op [a,b] mapM_XU (f : a -> XUMonad b) (xs : List a) : XUMonad (List b) =
   case xs of
     | [] -> return []
     | x :: xs' ->
       {new_x <- f x;
        new_xs <- mapM_XU f xs';
        return (new_x :: new_xs)}

(* Look up an include file and apply its corresponding computation *)
op includeFile (name: String, has_brackets: Bool) : XUMonad () =
  {(incls,_) <- xu_ask;
   case incls (name,has_brackets) of
     | Some m -> liftXUSubMonad m
     | None -> xu_error}

(* Expand a TypeName in XUMonad *)
op expandTypeNameXU (tp:TypeName) : XUMonad Type =
  {xenv <- xu_get;
   liftOption_XU (expandTypeName (xenv, tp))}

(* For typedefs, add it to the typedef table, checking first that the typedef
name is not already in the typedef table *)
(* FIXME HERE: typedefs are allowed to shadow each other, I think... *)
op evalTypedef (typedef:TypeDefinition) : XUMonad () =
  let id = typedef.Typedef_name in
  {xu_errorIfBound (id, fn xenv -> xenv.xenv_typedefs);
   tp <- expandTypeNameXU typedef.Typedef_type;
   xu_update (fn xenv ->
                xenv << {xenv_typedefs = update xenv.xenv_typedefs id tp})}

(* For object declarations, check that the name is not already in the object
table or the function table, get the zero value for the given type, and add the
result to the table. Extern declarations do not go in the current translation
unit; they are just there for type-checking. *)
op evalObjectDeclaration (odecl:ObjectDeclaration) : XUMonad () =
  if odecl.ObjDecl_isExtern then
    return ()
  else
    {tp <- expandTypeNameXU odecl.ObjDecl_type;
     if objectType? tp then
       xu_emit (odecl.ObjDecl_name, ObjFile_Object (zeroOfType tp))
     else
       xu_error}

(* For struct members, expand the type name and make sure it is not void *)
op evalMemberDeclaration (decl:MemberDeclaration) : XUMonad (Identifier * Type) =
  {ty <- expandTypeNameXU (decl.MemDecl_type);
   if (ty = T_void) then xu_error
   else return (decl.MemDecl_name, ty)}

(* For struct declarations, evaluate each struct member, check there are no
   duplicate field names, and check that the struct tag is not already in use *)
(* FIXME HERE: struct specifiers are allowed to shadow each other, I think... *)
op evalStructSpecifier (sspec:StructSpecifier) : XUMonad () =
  let id = sspec.StructSpec_tag in
  {members <- mapM_XU evalMemberDeclaration sspec.StructSpec_members;
   if members = [] || ~(noRepetitions? (unzip members).1)
     then xu_error else return ();
   xu_errorIfBound (id, fn xenv -> xenv.xenv_structures);
   xu_update (fn xenv ->
                xenv << {xenv_structures =
                            update xenv.xenv_structures id members})}

(* Expand all the type names in a ParameterDeclaration *)
op evalParameterDeclaration (param:ParameterDeclaration) : XUMonad (Identifier * Type) =
   {ty <- expandTypeNameXU (param.1);
    return (param.2, ty)}

(* Build a C function that quantifies over a list of argument values and then
   binds those argument values to params in a fresh, top-level scope. The
   resulting function ignores its current scope, since withFreshTopBindings
   creates a fresh scope. *)
(* FIXME HERE: move this to a short section above about C functions *)
op makeCFunction (retType : Type, params : List (Identifier * Type),
                  body : Monad ()) : CFunction =
  fn args ->
    if valuesHaveTypes (args, (unzip params).2) then
      {ret <- catchReturns (withFreshTopBindings
                              (fromAssocList (zip ((unzip params).1, args)))
                              body);
       if optValueHasType (ret, retType) then return ret else error
       }
    else error

(* Build a function by evaluating its return and parameter type names and then
calling makeCFunction. Note that this closes over the function table and
translation environment passed into the XUMonad when it is called, and this is
why its return type is TopFunction. *)
op evalCFunction (retTypeName : TypeName,
                  paramDecls : ParameterList,
                  body : Statement) : XUMonad TopFunction =
  {retType <- expandTypeNameXU retTypeName;
   params <- mapM_XU evalParameterDeclaration paramDecls;
   xenv <- xu_get;
   (_,tab) <- xu_ask;
   return (makeCFunction
             (retType, params,
              localR (fn r -> r << {r_functions=tab,r_xenv=xenv})
                (evalStatement body)))}

(* Get the type of a function *)
op evalCFunctionType (retTypeName : TypeName,
                      paramDecls : ParameterList) : XUMonad FunType =
  {retType <- expandTypeNameXU retTypeName;
   params <- mapM_XU evalParameterDeclaration paramDecls;
   return (retType, (unzip params).2)}

(* Set the function type for id to funtype; if id already has a function type,
make sure that type is compatible with funtype *)
op setFunType (id:Identifier, funtype: FunType) : XUMonad () =
  {xenv <- xu_get;
   case xenv.xenv_funtypes id of
     | None ->
       let funtypes = update xenv.xenv_funtypes id funtype in
       xu_update (fn xenv -> xenv << {xenv_funtypes = funtypes})
     | Some funtype' ->
       if compatibleTypes? (T_function funtype, T_function funtype') then
         return ()
       else
         xu_error}

(* Eval a function definition, by checking that the name is not already defined
in the object or function table and then calling evalCFunction *)
op evalFunctionDeclaration (fdef:FunctionDeclaration) : XUMonad () =
  {funtype <- evalCFunctionType (fdef.FDef_retType, fdef.FDef_params);
   setFunType (fdef.FDef_name, funtype);
   (case fdef.FDef_body of
      | None ->
       (* Ignore function prototypes in the semantics *)
       return ()
     | Some body ->
       if fdef.FDef_isExtern then xu_error else
         {f <- evalCFunction (fdef.FDef_retType, fdef.FDef_params, body);
          xu_emit (fdef.FDef_name, ObjFile_Function (f, funtype))})}

(* Translate a single external declaration *)
op evalTranslationUnitElem (decl:TranslationUnitElem) : XUMonad () =
  case decl of
    | XU_function fdef -> evalFunctionDeclaration fdef
    | XU_declaration (Decl_struct sspec) -> evalStructSpecifier sspec
    | XU_declaration (Decl_object odecl) -> evalObjectDeclaration odecl
    | XU_declaration (Decl_typedef typedef) -> evalTypedef typedef
    | XU_include nm_and_brackets -> includeFile nm_and_brackets

op evalTranslationUnit (tunit : TranslationUnit) : XUMonad () =
  {_ <- mapM_XU evalTranslationUnitElem tunit; return ()}


%subsection (* Programs *)

(* FIXME HERE: documentation! *)

type ObjFileFun = {f: FunctionTable -> Option ObjectFile |
                     fa (tab1,tab2)
                       monad_PCPO (=) (tab1,tab2) =>
                       (case (f tab1, f tab2) of
                          | (Some ofile1, Some ofile2) ->
                            monad_PCPO (=) (objFileFunTable ofile1,
                                            objFileFunTable ofile2)
                          | _ -> true)
                     }

type Program = {pgm_sources : List TranslationUnit,
                pgm_libs : List ObjFileFun }

(* FIXME HERE: document the "tying the knot" stuff *)

op linkObjFileFuns2 (ofile1 : ObjFileFun,
                     ofile2 : ObjFileFun) : ObjFileFun =
  fn tab -> objFileOptCombine (ofile1 tab, ofile2 tab)

op linkObjFileFuns (ofiles : List ObjFileFun) : ObjFileFun =
  foldr linkObjFileFuns2 (fn _ -> Some []) ofiles

op evalXUToObjFileFun (incls: IncludeFileMap) (tunit: TranslationUnit) : ObjFileFun =
  fn tab -> {(bindings,_) <- runXUMonad (evalTranslationUnit tunit) incls tab; Some bindings}

op linkProgram (incls: IncludeFileMap) (pgm: Program) : ObjFileFun =
  linkObjFileFuns (pgm.pgm_libs ++ map (evalXUToObjFileFun incls) pgm.pgm_sources)

op errorFunctionTable : FunctionTable =
  fn _ -> error

(* Tie the knot *)
op makeFunctionTable (ofile: ObjFileFun) : FunctionTable =
  mfix (fn table ->
          case ofile table of
            | Some obj -> objFileFunTable obj
            | None -> errorFunctionTable)

op evalObjFileFun (ofile: ObjFileFun) : Option ObjectFile =
  ofile (makeFunctionTable ofile)

(* Get the initial storage for an object file *)
op initialStorage (ofile : ObjectFile) : Storage =
  {static = fromAssocList (objFileObjectBindings ofile),
   automatic = [], allocated = []}

(* Run a program, given a set of include files, with argc=0 and argv=NULL *)
op evalProgram (incls: IncludeFileMap) (pgm : Program) : Monad (Option Value) =
   {ofile <- liftOption (evalObjFileFun (linkProgram incls pgm));
    putState (initialStorage ofile);
    let funTable = objFileFunTable ofile in
    let funtypes = objFileFunTypes ofile in
    let xenv = emptyTranslationEnv << {xenv_funtypes = funtypes} in
    localR (fn _ -> makeGlobalR (xenv, funTable))
      (funTable ("main", [int0,V_nullpointer (T_pointer (T_pointer T_char))]))}

end-spec
