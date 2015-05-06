C qualifying spec

import /Library/General/TwosComplementNumber
import /Library/General/OptionExt
import /Library/General/Stream

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
  forall? (identifierNonDigit? \/ digit?) chars &&
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

(* Our C subset features the following types [ISO 6.2.5]: the standard
signed and unsigned integer types, the (plain) char type, structure
types, pointer types, array types, and the void type. Each of the
signed/unsigned short/int/long/longlong types can be denoted via
multiple, equivalent combinations of type specifiers [ISO 6.7.2]; even
though some of these types may have identical representations in an
implementation, they are nevertheless different types [ISO 6.2.5/14].
A structure type is denoted by its name [ISO 6.2.3], which is an
identifier (we preclude anonymous structure types in this
formalization). An array type includes the number of elements [ISO
6.2.5/20]; our C subset only includes array types with known size. *)

(* emw4: added function pointer types *)

type FunType = Type * List Type

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
  | T_struct Identifier           % structure
  | T_pointer Type                % pointer (to type)
  | T_array   Type * Nat          % array (of type of size)
  | T_void                        % void
  | T_function FunType            % function (with return type and argument types)

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

(* Each integer type has a size in bits. *)

op typeBits (ty:Type | integerType? ty) : Nat =
  if characterType? ty then CHAR_BIT
  else if shortType? ty then short_bits
  else if intType? ty then int_bits
  else if longType? ty then long_bits
  else llong_bits

(* In our C subset, two types are compatible [ISO 6.2.7] iff they are the same
type. *)

op compatibleTypes? (ty1:Type, ty2:Type) : Bool =
  ty1 = ty2

(* Given the above definition, the composite type of two compatible types [ISO
6.2.7] is the same type. *)

op compositeType (ty1:Type, ty2:Type | compatibleTypes? (ty1, ty2)) : Type =
  ty1


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

op rangeOfIntegerType (ty:Type | integerType? ty) : FiniteSet Int =
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
    if rangeOfIntegerType ty <= rangeOfIntegerType T_sint then T_sint else T_uint
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
    else if rangeOfIntegerType sty >= rangeOfIntegerType uty then sty
    else correspondingUnsignedOf sty


%subsection (* Constants *)

(* Our C subset only includes integer constants [ISO 6.4.4.1]. It has no
floating [ISO 6.4.4.2], enumeration [ISO 6.4.4.3], or character [ISO 6.4.4.4]
constants.

Rather than formalizing the string representation of a constant, we
assume that conversion to and from strings is handled by the parser
and/or pretty-printer, and so, in the abstract sytax formalized here,
integer constants are just represented as Specware natural numbers.
(Negative integer constants are written in C using the unary negation
operator applied to positive integer constants.) How the constant is
written, however, also affects the particular integer type that is
selected for it [ISO 6.4.4.1], so we make the type explicit in integer
constants as well. *)

type IntegerConstant = { n_t : Type * Nat |
                          integerType? n_t.1 && n_t.2 in? rangeOfIntegerType n_t.1 }

op integerConstantValue (c:IntegerConstant) : Nat = c.2

op integerConstantType (c:IntegerConstant) : Type = c.1


%subsection (* Unary operators *)

(* Of the unary operators in [ISO 6.5.3], our C subset includes the address and
indirection operators [ISO 6.5.3.2] and the unary arithmetic operators [ISO
6.5.3.3]. *)

type UnaryOp =
  | ADDR   % address &
  | STAR   % indirection *
  | PLUS   % unary +
  | MINUS  % unary -
  | NOT    % bitwise complement ~
  | NEG    % logical negation !


%subsection (* Binary operators *)

(* Even though the grammar in [ISO] has no explicit non-terminal for binary
operators (unlike unary operators [ISO 6.5.3/1]), in our formalization we
introduce a notion of binary operator to enable a more compact definition of
expressions later. Our C subset includes all the operators in [ISO
6.5.5-6.5.14]. *)

type BinaryOp =
  | MUL   % multiplication *
  | DIV   % division       /
  | REM   % remainder      %
  | ADD   % addition       +
  | SUB   % subtraction    -
  | SHL   % bitwise shift left  <<
  | SHR   % bitwise shirt right >>
  | LT    %    less-than             relation <
  | GT    % greater-than             relation >
  | LE    %    less-than-or-equal-to relation <=
  | GE    % greater-than-or-equal-to relation >=
  | EQ    %     equal-to relation ==
  | NE    % not-equal-to relation !=
  | AND   % bitwise           AND &
  | XOR   % bitwise exclusive OR  ^
  | IOR   % bitwise inclusive OR  |
  | LAND  % logical AND &&
  | LOR   % logical OR ||


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
6.5.2.1], and the null pointer constant [ISO 6.3.2.3/3] '(void* ) 0' (we leave
one space between the '*' and the ')' because comments in Specware do not nest).
The fourth argument (a type) of the 'cond' constructor is the type of the result
of the conditional expression, inferred by the compiler; this is needed because
the evaluation of conditional expressions depends on this type [ISO 6.5.15]. We
use a dedicated constructor for the null pointer constant '(void* ) 0' to avoid
introducing casts in our C subset just for the purpose of modeling this null
pointer constant. *)

type Expression =
  | E_ident     Identifier
  | E_const     IntegerConstant
  | E_unary     UnaryOp * Expression
  | E_binary    Expression * BinaryOp * Expression
  | E_cond      Expression * Expression * Expression * Type
  | E_member    Expression * Identifier
  | E_memberp   Expression * Identifier
  | E_subscript Expression * Expression
  | E_nullconst

(* In our C subset, the only null pointer constant [ISO 6.3.2.3/3] is '(void* )
0', captured by constructor 'nullconst' above. *)

op nullPointerConst? (expr:Expression) : Bool =
  embed? E_nullconst expr


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

Besides statements, we only allow object declarations as block items [ISO
6.8.2], not other kinds of declarations. *)

type Statement =
  | S_assign Expression * Expression
  | S_call   Option Expression * Expression * List Expression
  | S_if     Expression * Statement * Option Statement
  | S_return Option Expression
  | S_while  Expression * Statement
  | S_do     Statement * Expression
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

type ParameterDeclaration =
  {PDecl_type : TypeName,
   PDecl_name : Identifier}

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

(* Our C subset has no preprocessing directives [ISO 6.10], so a preprocessing
translation unit [ISO 5.1.1.1/1] is the same as a translation unit [ISO 6.9] --
essentially, a file.

A translation unit consists of zero or more external declarations, where an
external declaration is either a function definition or a declaration as defined
earlier [ISO 6.9/1]. *)

type ExternalDeclaration =
  | EDecl_function    FunctionDeclaration
  | EDecl_declaration Declaration

type TranslationUnit = List ExternalDeclaration


%subsection (* Programs *)

(* A C program consists of a set of source files [ISO 5.1.1.1/1]. Since our C
subset has no '#include' directives [ISO 6.10], a source file coincides with a
preprocessing translation unit, which, as explained above, coincides with a
translation unit. Thus, in our C subset a program consists of translation units.
*)

type Program = List TranslationUnit


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

(* We represent integers in values with a tagged integer type *)
type TypedInt = { ty_i : Type * Int |
                   integerType? ty_i.1 && ty_i.2 in? rangeOfIntegerType ty_i.1 }

(* We now define the values. The C spec defines the values as the contents of an
object when interpreted at a specific type [ISO 3.19], where an object is a
region of data storage [ISO 3.15]. This wording suggests that, conceptually, a
value "includes" a type. Typical implementations only store "raw" bits inside
objects, without explicit type information, but use the declared type of the
object to interpret the object's content [ISO 6.5/6].

In our formal model of values, it is convenient to include type information. The
values in our C subset are those of the integer types, of structure types, of
pointer types, and of array types; those are all the non-'void' types in our C
subset.

A structure (value) consists of a value assigned to each member, so we use a
finite map from identifiers (denoting members) to values. We also include the
tag of the structure, so that we have complete type information.

A pointer (value) is an element of the Pointer type defined above. There is also
a separate null pointer [ISO 6.3.2.3/3] value for each type [ISO 6.3.2.3/4].

An array value consists of a list of values -- the elements of the array. We
also include the type of the elements in our model of an array value.

When an object declared in automatic storage has no initializer, its initial
value is indeterminate [ISO 6.7.9/10]. Unlike Java, C does not enforce that such
objects are assigned a value before first use. Thus, at run time, we may be
accessing object with indeterminate value. Since we are interested in
well-behaved C programs, we introduce, as part of our model of values, special
'undefined' values, which represent those indeterminate values. These special
values include their type, but no other information is predictably known.

Even though some types may represent values in the same way, they are still
separate types [ISO 6.2.5/14] and thus we use a different constructor for each
different type. *)

type Value =
  | V_int         TypedInt
  | V_struct      Identifier * FiniteMap (Identifier, Value)
  | V_pointer     Type * Pointer
  | V_array       Type * List Value
  | V_nullpointer Type
  | V_undefined   Type

(* There is an obvious mapping from values to types. Note that this includes
undefined values, because at run time they are still C values -- we just do not
know what they are exactly. *)

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
as a mapping from names (of objects) to values (stored in the objects).

As explained earlier, the value of an object arises from interpreting the
object's content according to the type of the object, i.e. we could model named
storage by associating raw bit lists to names, and then use the named objects'
types to construct the values. But we prefer to associate typed values to names,
so that the value of an object can be retrieved from a named storage without
reference to a symbol table or similar information. We could, of course, define
named storage to also associate a type to each name, but that is really the same
as associating a typed value to each name, as we do here. We can prove that,
when all the syntactic constraints formalized earlier are satisfied, the type of
the value stored into an object always coincides with the type of the object. *)

type NamedStorage = FiniteMap (Identifier, Value)

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
introduced earlier. The allocated storage is modeled as a list, where the
AllocatedID type, which is just natural numbers, is used to index into this
list. In order to model deallocation of objects, each AllocatedID is mapped to
an optional value, where "None" indicates a deallocated object. This is to
prevent another allocation from re-using an AllocatedID. *)

type AllocatedStorage = List (Option Value)

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

(* These are all the non-local exits (FIXME: document them!) *)
type Monad.Err =
    | Err_error
    | Err_nonstd
    | Err_return (Option Value)
    | Err_unimplemented

(* The error and "non-standard" computations *)
op [a] error : Monad a = raiseErr Err_error
op [a] nonstd : Monad a = raiseErr Err_nonstd

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

(* Return from the current function. This uses "raiseErr", even though it is not
   technically an "error", since raiseErr is really just a non-local exit *)
op [a] returnFromFun (retVal : Option Value) : Monad a =
   raiseErr (Err_return retVal)

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

(* Build a lens for the optional Value associated with the given AllocatedID in
   allocated storage, where "optional" means the AllocatedID is allowed to be in
   a deallocated state *)
op allocatedObjOptLens (alloc_id : AllocatedID) : MLens ((),Option Value) =
  case alloc_id of
    | AllocatedID n ->
      mlens_compose (allocatedStorageLens,
                     mlens_of_list_index (n, error, error))

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
op structFieldsLens : MLens (Value,FiniteMap (Identifier, Value)) =
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
       mlens_compose (allocatedObjOptLens a_id, mlens_for_option (error, error))
     | OD_Member (d', ident) ->
       mlens_compose (objectDesignatorLens d',
                      mlens_compose (structFieldsLens,
                                     mlens_of_key (ident, error, error)))
     | OD_Subscript (d', i) ->
       mlens_compose (objectDesignatorLens d',
                      mlens_compose
                        (arrayElementsLens,
                         mlens_of_list_index (i, nonstd, nonstd)))

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
op allocateObject (val: Value) : Monad AllocatedID =
  {storage <- getState;
   putState (storage << {allocated = storage.allocated ++ [Some val]});
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

type TypedefTable = FiniteMap (Identifier, Type)

(* A structure type, introduced by a structure specifier, consists of
an ordered list of typed members, each of which is modeled as a pair
of a member name and its type. A symbol table for structure specifiers
associates typed members to structure tags (which are identifiers). *)

type StructMembers = {l:List (Identifier * Type) | noRepetitions? (unzip l).1}
type StructTable = FiniteMap (Identifier, StructMembers)

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

type CFunction = List Value -> Monad (Option Value)
type TopFunction = { m:CFunction | fa (l,f) localR f (m l) = m l }
type FunctionTable = FiniteMap (Identifier, TopFunction * FunType)

(* We now define TranslationEnv as containing tables for typedefs, structs, and
top-level function definitions.

FIXME: in the future, this could also contain information about staitc
identifiers with internal linkage, i.e., global variables, as well as static
variables inside functions, that are not visible outside the current file and/or
function body. *)

(* FIXME HERE: maybe call this TopEnv? *)

type TranslationEnv =
   {xenv_typedefs   : TypedefTable,
    xenv_structures : StructTable,
    xenv_functions  : FunctionTable }

op emptyTranslationEnv : TranslationEnv =
   {xenv_typedefs   = empty,
    xenv_structures = empty,
    xenv_functions  = empty}


(* The reader type of the monad is the TranslationEnv type, along with a
   designator for the current lexical scope *)
type Monad.R =
   {r_xenv     : TranslationEnv,
    r_curScope : ScopeDesignator }

op globalRFromEnv (env : TranslationEnv) : R =
   {r_xenv = env, r_curScope = GlobalScope}

(* Test if a typedef name is currently defined *)
op testTypeDef (name : Identifier) : Monad Bool =
  {r <- askR;
   return (some? (r.r_xenv.xenv_typedefs name))}

(* Look up a typedef name *)
op lookupTypeDef (name : Identifier) : Monad Type =
  {r <- askR;
   liftOption (r.r_xenv.xenv_typedefs name)}

(* Look up a struct tag *)
op lookupStructMembers (tag : Identifier) : Monad StructMembers =
  {r <- askR;
   liftOption (r.r_xenv.xenv_structures tag)}

(* Look up a function *)
op lookupFunction (f_desig : FunctionDesignator) : Monad (TopFunction * FunType) =
  case f_desig of
    | FunctionDesignator id ->
      {r <- askR;
       liftOption (r.r_xenv.xenv_functions id)}

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
   result is either an object or function designator, i.e., a Pointer. *)
op lookupIdentifierInScope (id:Identifier, scope:ScopeDesignator) : Monad Pointer =
  {bindings <- (scopeDesignatorLens scope).mlens_get ();
   if some? (bindings id) then
     (* If id is in the current scope, return the corresponding pointer *)
     return (ObjPointer (OD_Top (scope, id)))
   else
     case scope of
       | LocalScope scope_id ->
         (* If id is not in the current scope, proceed to the parent scope *)
         {parent_scope <- getScopeParent scope_id;
          lookupIdentifierInScope (id, parent_scope)}
       | GlobalScope ->
         (* If no parent scope, check in the function table; we do a lookup and
            discard the value as a way of ensuring id is in the table *)
         {_ <- lookupFunction (FunctionDesignator id);
          return (FunPointer (FunctionDesignator id)) }}

(* Look up an identifier starting in the current scope *)
op lookupIdentifier (id:Identifier) : Monad Pointer =
  {d <- getCurrentScopeDesignator;
   lookupIdentifierInScope (id, d)}


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
                integerType? ty && i in? rangeOfIntegerType ty) : List Bit
(* FIXME: write bitsOfInt! *)

(* Create a value from a list of bits, given a type *)
op valueOfBits (b:List Bit, ty:Type |
                  integerType? ty && length b <= typeBits ty) : Value =
   V_int (ty, TwosComplement.toInt b)

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
   if i in? rangeOfIntegerType ty then
     return (valueOfInt (ty, i))
   else if unsignedIntegerType? ty || (plainCharsAreUnsigned && ty = T_char) then
     let max1:Nat = maxOfIntegerType ty + 1 in
     let i':Int = the(i':Int) i' in? rangeOfIntegerType ty &&
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


%subsubsection (* Pointer conversions *)

(* The compile-time checks formalized earlier allow conversions (i) between
compatible pointer types (which in our C subset means identical pointer types,
see op 'compatibleTypes?') and (ii) between pointers to 'void' and pointers to
non-'void' types. Since our C subset is type-safe, we only allow conversion (ii)
on null pointers; we disallow conversion (ii) between pointers that reference
objects, because each object has a well-defined type and it should not be
"changed" by converting to 'void*' and then to an incompatible pointer type.

The following op returns an error outcome if neither (i) nor (ii) apply, because
the compile-time checks prevent that from happening. In conversion (ii), unless
the pointer is null, the following op returns a non-standard outcome. *)

op convertPointer (val:Value, ty:Type | embed? T_pointer ty) : Monad Value =
  let ty0 = typeOfValue val in
  if compatibleTypes? (ty0, ty) then
    return val
  else if embed? T_pointer ty0 && (ty0 = T_pointer T_void
                                     || ty = T_pointer T_void) then
    if embed? V_nullpointer val then
      return (V_nullpointer ty)
    else
      raiseErr Err_nonstd
  else
    error


%subsubsection (* Assignment conversions *)

(* In an assignment [ISO 6.5.16.1], the left and right operands must be (i) two
arithmetic operands, or (ii) two compatible structures, or (iii) two pointers to
compatible types, or (iv) a pointer to a non-void type and a pointer to void, or
(v) a pointer (left) and a null pointer constant (right) [ISO 6.5.16.1/1]. Our C
subset has no notion of atomic, qualified, and unqualified types. The case of a
left '_Bool' operand does not apply to our C subset. In case (i), the right
operand is converted into the type of the left operand and stored into it. In
case (ii), the right operand structure is stored into the left operand,
unchanged. We consolidate cases (iii), (iv), and (v), which all involve
pointers, by converting the right operand pointer into the left operand's
pointer type -- recall that op 'convertPointer' preserves the type safety of our
C subset by disallowing conversions between non-null pointers of incompatible
types.

The following op captures the process of converting the value of the right
operand of an assignment to the type of the left operand. An error occurs if
none of the cases (i)-(v) above holds. *)

op convertForAssignment (val:Value, ty:Type) : Monad Value =
  if arithmeticType? ty then
    convertInteger (val, ty)
  else if embed? T_struct ty && compatibleTypes? (typeOfValue val, ty) then
    return val
  else if embed? T_pointer ty then
    convertPointer (val, ty)
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
  return (valueOfInt (integerConstantType c, integerConstantValue c))


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
     if y in? rangeOfIntegerType ty then
       return (valueOfInt (ty, y))
     else
       raiseErr Err_nonstd}

(* The '~' operator requires an integer operand [ISO 6.5.3.3/1] and returns the
bitwise complement of the promoted operand [ISO 6.5.3.3/4]. *)

op operator_NOT (val:Value) : Monad Value =
  {val' <- promoteValue val;
   x <- intOfValue val';
   bits <- return (bitsOfInt (typeOfValue val', x));
   return (valueOfBits (Bits.not bits, typeOfValue val'))}

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
     if y in? rangeOfIntegerType ty then
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
     if y in? rangeOfIntegerType ty then
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
     if y in? rangeOfIntegerType ty then
       return (valueOfInt (ty, y))
     else
       nonstd}

(* The binary '+' operator requires arithmetic operands (our C subset excludes
pointer arithmetic) [ISO 6.5.6/2], performs the usual arithmetic conversions
[ISO 6.5.6/4], and returns the sum [ISO 6.5.6/5].

If the operands are unsigned, we follow the laws of arithmetic modulo MAX+1
(where MAX is maximum integer representable in the operand's type) [ISO
6.2.5/9].

If the operands are signed and their product cannot be represented in the
operand's type, the behavior is undefined [ISO 6.5/5]. *)

op operator_ADD (val1:Value, val2:Value) : Monad Value =
  {(ty, x1, x2) <- arithConvertValues (val1, val2);
   let y = x1 + x2 in
   if unsignedIntegerType? ty then
     return (valueOfInt (ty, y modF (maxOfIntegerType ty + 1)))
   else
     if y in? rangeOfIntegerType ty then
       return (valueOfInt (ty, y))
     else
       raiseErr Err_nonstd}

(* The binary '-' operator requires arithmetic operands (our C subset excludes
pointer arithmetic) [ISO 6.5.6/3], performs the usual arithmetic conversions
[ISO 6.5.6/4], and returns the difference [ISO 6.5.6/6].

If the operands are unsigned, we follow the laws of arithmetic modulo MAX+1
(where MAX is maximum integer representable in the operand's type) [ISO
6.2.5/9].

If the operands are signed and their product cannot be represented in the
operand's type, the behavior is undefined [ISO 6.5/5]. *)

op operator_SUB (val1:Value, val2:Value) : Monad Value =
  {(ty, x1, x2) <- arithConvertValues (val1, val2);
   let y = x1 - x2 in
   if unsignedIntegerType? ty then
     return (valueOfInt (ty, y modF (maxOfIntegerType ty + 1)))
   else
     if y in? rangeOfIntegerType ty then
       return (valueOfInt (ty, y))
     else
       raiseErr Err_nonstd}

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
     if x1 >= 0 && y in? rangeOfIntegerType ty then
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
   return (valueOfBits (bits1 Bits.and bits2, ty))}

op operator_XOR (val1:Value, val2:Value) : Monad Value =
  {(ty, x1, x2) <- arithConvertValues (val1, val2);
   let bits1 = bitsOfInt (ty, x1) in
   let bits2 = bitsOfInt (ty, x2) in
   return (valueOfBits (bits1 Bits.xor bits2, ty))}

op operator_IOR (val1:Value, val2:Value) : Monad Value =
  {(ty, x1, x2) <- arithConvertValues (val1, val2);
   let bits1 = bitsOfInt (ty, x1) in
   let bits2 = bitsOfInt (ty, x2) in
   return (valueOfBits (bits1 Bits.ior bits2, ty))}

(* We do not define ops 'operator_LAND' and 'operator_LOR' for the '&&' and '||'
operators because they are non-strict, i.e. the second value is calculated only
if the first value does not already determine the result, as formalized below.
We do not define ops 'operator_ADDR' and 'operator_STAR' because they do not
quite operate on values, as formalized below. *)


%subsection (* Expressions *)

(* An C expression designates a possibly side-effecting computation of a value,
an object designator (i.e., an lvalue), or a function designator [ISO 6.5/1].
(Note that we do not in fact allow side-effects in our expressions, as discussed
above.) We smoosh the latter two into the single case of returning a Pointer,
yielding the following type for the result of evaluating an expression. Further,
array expression values are converted to pointers [ISO 6.3.2.1], except for a
few special cases, and this is also captured in the following type. *)
type ExpressionValue = {v:Value | ~(arrayValue? v)}
type ExpressionResult =
  | Res_pointer Pointer
  | Res_value   ExpressionValue

(* Convert a FunctionDesignator to a pointer value. This requires looking up the
   type information of the pointer in the function table. *)
op pointerValueForFunction (f_desig : FunctionDesignator) : Monad ExpressionValue =
  {(_, (ret_ty, param_tys)) <- lookupFunction f_desig;
   return (V_pointer (T_function (ret_ty, param_tys), FunPointer f_desig))}

(* Convert a FunctionDesignator to an ExpressionResult *)
op pointerResultForFunction (f_desig : FunctionDesignator) : Monad ExpressionResult =
  {v <- pointerValueForFunction f_desig;
   return (Res_value v)}

(* In all but a handfull of special cases, the result of an expression is
   converted to a value that is not an array or a function [ISO 6.3.2.1].
   Lvalues are converted to the values of the objects designated by them, array
   values are converted to pointers to their first element, and function values
   are converted to pointers to those function values. These conversions are
   intuitively part of converting an ExpressionResult to a Value. *)
op expressionValue (res:ExpressionResult) : Monad ExpressionValue =
  case res of
    | Res_pointer (ptr as (ObjPointer obj)) ->
      {v <- readObject obj;
       case v of
         | V_array (ty, _) -> return (V_pointer (ty, ptr))
         | _ -> return (V_pointer (typeOfValue v, ptr)) }
    | Res_pointer (FunPointer f_desig) ->
      pointerValueForFunction f_desig
    | Res_value val ->
      return val

(* It is convenient to lift the previous op to lists. *)
op expressionValues (ress:List ExpressionResult) : Monad (List ExpressionValue) =
   mapM expressionValue ress

(* expressionValue lifted to an operator on computations *)
op expressionValueM (res_m:Monad ExpressionResult) : Monad ExpressionValue =
   {res <- res_m;
    expressionValue res}

(* Lift a unary monadic function on values to a function on
   ExpressionResult computations *)
op liftValueFun1 (f:ExpressionValue -> Monad ExpressionValue) (res_m: Monad ExpressionResult) : Monad ExpressionResult =
   {v <- expressionValueM res_m;
    v_out <- f v;
    return (Res_value v_out)}

(* Lift a binary monadic function on values to a function on
   ExpressionResult computations *)
op liftValueFun2 (f:ExpressionValue * ExpressionValue -> Monad ExpressionValue)
   (res_m1: Monad ExpressionResult, res_m2: Monad ExpressionResult) : Monad ExpressionResult =
   {v1 <- expressionValueM res_m1;
    v2 <- expressionValueM res_m2;
    v_out <- f (v1, v2);
    return (Res_value v_out)}

(* The following maps unary operations to functions on ExpressionResult, where
the input ExpressionResult is the result of evaluating the operand of the
operation. For the unary '&' operator, the operand must result in an object
designator [ISO 6.5.3.2/1], which is returned as a pointer value [ISO
6.5.3.2/3]. For the unary '*' operator, the operand must be a pointer [ISO
6.5.3.2/2], which is returned as an object designator [ISO 6.5.3.2/4].
Dereferencing an undefined pointer value yields undefined behavior. There are
two exceptions to this, which are covered by the evaluate op defined below. *)
op evaluatorForUnaryOp (uop:UnaryOp) : Monad ExpressionResult -> Monad ExpressionResult =
   case uop of
     | ADDR -> (fn res_m ->
                  {res <- res_m;
                   case res of
                     | Res_value _ -> error
                     | Res_pointer (FunPointer f_desig) ->
                       pointerResultForFunction f_desig
                     | Res_pointer obj ->
                       {val <- expressionValue res;
                        return (Res_value (V_pointer (typeOfValue val, obj)))}})
     | STAR -> (fn res_m ->
                  {val <- expressionValueM res_m;
                   case val of
                     | V_pointer (_, ptr)        -> return (Res_pointer ptr)
                     | V_nullpointer _           -> raiseErr Err_nonstd
                     | V_undefined (T_pointer _) -> raiseErr Err_nonstd
                     | _                         -> error})
     | PLUS  -> liftValueFun1 operator_PLUS
     | MINUS -> liftValueFun1 operator_MINUS
     | NOT   -> liftValueFun1 operator_NOT
     | NEG   -> liftValueFun1 operator_NEG

(* The following maps binary operations to binary functions on ExpressionResult.
In a binary expression with any operator but '&&' and '||', first the operands
are evaluated, then the operator is applied. Since expressions in our C subset
have no side-effects, and since they both must be evaluated (in some order), it
makes no difference which one is evaluated first. For '&&' and '||', the second
expression is only evaluated if necessary. This could make a difference for,
e.g., multi-threaded code. *)
op evaluatorForBinaryOp (bop:BinaryOp) :
   Monad ExpressionResult * Monad ExpressionResult -> Monad ExpressionResult =
   case bop of
     | MUL -> liftValueFun2 operator_MUL
     | DIV -> liftValueFun2 operator_DIV
     | REM -> liftValueFun2 operator_REM
     | ADD -> liftValueFun2 operator_ADD
     | SUB -> liftValueFun2 operator_SUB
     | SHL -> liftValueFun2 operator_SHL
     | SHR -> liftValueFun2 operator_SHR
     | LT -> liftValueFun2 operator_LT
     | GT -> liftValueFun2 operator_GT
     | LE -> liftValueFun2 operator_LE
     | GE -> liftValueFun2 operator_GE
     | EQ -> liftValueFun2 operator_EQ
     | NE -> liftValueFun2 operator_NE
     | AND -> liftValueFun2 operator_AND
     | XOR -> liftValueFun2 operator_XOR
     | IOR -> liftValueFun2 operator_IOR
     | LAND -> (fn (res_m1, res_m2) ->
                  {val1 <- expressionValueM res_m1;
                   isZero1 <- zeroScalarValue? val1;
                   if isZero1 then return (Res_value int0)
                   else
                     {val2 <- expressionValueM res_m2;
                      isZero2 <- zeroScalarValue? val2;
                      if isZero2 then return (Res_value int0)
                      else return (Res_value int1)}})
     | LOR -> (fn (res_m1, res_m2) ->
                  {val1 <- expressionValueM res_m1;
                   isZero1 <- zeroScalarValue? val1;
                   if ~ isZero1 then return (Res_value int1)
                   else
                     {val2 <- expressionValueM res_m2;
                      isZero2 <- zeroScalarValue? val2;
                      if isZero2 then return (Res_value int0)
                      else return (Res_value int1)}})


(* We now formalize all of expression evaluation, as follows.

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

There are two special cases for evaluating unary expressions. The first is that
an expression of the form '&*E' evaluates to the same as E, i.e. '&' and '*' are
not applied [ISO 6.5.3.2/3]. The difference between the normal evaluation
procedure and this exception is visible when 'E' is null: dereferencing null
yields undefined behavior [ISO 6.5.3.2/4].

The second special case for unary expressions is for an expression of the form
'&E[I]' when I evaluates to 0, which yields just E [ISO 6.5.3.2/3]. Normally,
this would evaluate to the same as 'E + I', but the distinction makes a
difference in our C subset if 'E' is null, because in that case the result is
null instead of being non-standard. If 'E' is null and 'I' is not 0, then 'E +
I' is undefined according to [ISO 6.5.6/8], just like '&E[I]' is undefined. If
'E' is not null, then there is no difference between the result of '&E[I]' and
'E + I'.

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

op evaluate (expr:Expression) : Monad ExpressionResult =
  case expr of
    | E_ident var -> 
      {ptr <- lookupIdentifier var;
       return (Res_pointer ptr)}
    | E_const c ->
      {val <- evaluateIntegerConstant c;
       return (Res_value val)}
    | E_unary (ADDR, E_unary (STAR, expr0)) ->
      % special treatment for expr of the form '& * expr0':
      evaluate expr0
    | E_unary (ADDR, e_arg as E_subscript (expr1, expr2)) ->
      % special treatment for expr of the form '& expr1 [ expr2 ]',
      % if 'expr2' yields 0:
      {val2 <- expressionValueM (evaluate expr2);
       i <- intOfValue val2;
       if i = 0 then
         evaluate expr1
       else
         evaluatorForUnaryOp ADDR (evaluate e_arg)}
    | E_unary (uop, expr1) ->
      evaluatorForUnaryOp uop (evaluate expr1)
    | E_binary (expr1, bop, expr2) ->
      evaluatorForBinaryOp bop (evaluate expr1, evaluate expr2)
    | E_cond (expr1, expr2, expr3, ty) ->
      {val1 <- expressionValueM (evaluate expr1);
       isZero <- zeroScalarValue? val1;
       ret_val <-
         if ~ isZero then expressionValueM (evaluate expr2)
         else expressionValueM (evaluate expr3);
       ret_val_converted <-
         if integerType? ty then
           convertInteger (ret_val, ty)
         else if embed? T_pointer ty then
           convertPointer (ret_val, ty)
         else if typeOfValue ret_val = ty then
           return ret_val
          else
            error;
       return (Res_value ret_val_converted)}
  | E_member (expr, mem) ->
    {res <- evaluate expr;
     case res of
       | Res_value (V_struct (_, members)) ->
         (case members mem of
            | Some val ->
              (* If the LHS is a struct value, with the mem struct member,
                 return the value of the mem struct member *)
              return (Res_value val)
            | None ->
              (* If LHS is a struct without member mem, it is an error *)
              error)
       | Res_value _ ->
         (* Error if the LHS is a non-struct value *)
         error
       | Res_pointer (ObjPointer obj) ->
         (* If the LHS is an object designator (i.e., an lvalue), make sure it
            points to a struct, and then form the lvalue for the mem struct
            member of that struct *)
         {val_lhs <- readObject obj;
          case val_lhs of
            | V_struct (_, members) ->
              (case members mem of
                 | Some _ -> return (Res_pointer (ObjPointer (OD_Member (obj, mem))))
                 | None -> error)
            | _ -> error}
       | Res_pointer (FunPointer _) ->
         (* Error if the LHS is a function designator *)
         error}
  | E_memberp (expr0, mem) ->
    (* FIXME: make some op(s) for simplifying all of this *)
    {val <- expressionValueM (evaluate expr0);
     case val of
       | V_pointer (_, ObjPointer obj) ->
         {val_star <- readObject obj;
          case val_star of
            | V_struct (_, members) ->
              (case members mem of
                 | Some _ ->
                   (* If expr0 yields a pointer to a struct containing mem,
                      return the designator of mem in that struct *)
                   return (Res_pointer (ObjPointer (OD_Member (obj, mem))))
                 | None ->
                 (* Error if we get a pointer to a struct not containing mem *)
                 error)
            | _ ->
              (* Error if expr0 is a pointer to a non-struct *)
              error}
       | _ ->
         (* Error if expr0 does not evaluate to a pointer *)
         error}
  | E_subscript (expr1, expr2) ->
    {val1 <- expressionValueM (evaluate expr1);
     val2 <- expressionValueM (evaluate expr2);
     j <- intOfValue val2;
     nonstdIf (j < 0); (* Undefined for negative array subscripts *)
     obj <-
       (case val1 of
          | V_pointer (_, ObjPointer (OD_Subscript (obj, i))) ->
            (* If the LHS is a pointer to an array element, add the RHS to it *)
            return (OD_Subscript (obj, i+j))
          | V_pointer (_, ObjPointer obj) ->
            (* If the LHS is non-array pointer, subscript it *)
            return (OD_Subscript (obj, j))
          | _ ->
            (* Error if the LHS does not evaluate to an object pointer *)
            error);
     (* We read the returned pointer to ensure it is good (i.e., it raises an
        error if val1 is a pointer to a non-array, and it raises Err_nonstd if
        the new index is out of bounds) *)
     readObject obj;
     return (Res_pointer (ObjPointer obj))}
  | E_nullconst ->
    return (Res_value (V_nullpointer (T_pointer T_void)))


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

op evaluateAll (exprs:List Expression) : Monad (List ExpressionResult) =
  mapM evaluate exprs

op evaluateAllToValues (exprs:List Expression) : Monad (List Value) =
  {ress <- mapM evaluate exprs;
   mapM expressionValue ress}


%subsection (* Type names *)

(* A type name denotes a type. The following op returns the type denoted by a
type name w.r.t. a TypedefTable, by expanding all the typedef names in the type
name. Note that this is not done in the Monad, so that it can be called by
evalTranslationUnit. *)

op expandTypeName (table:TypedefTable, tyn:TypeName) : Option Type =
  case tyn of
  | TN_typedef tdn -> table tdn
  | TN_pointer tyn ->
    {ty <- expandTypeName (table, tyn);
     Some (T_pointer ty)}
  | TN_array (tyn, n) ->
    {ty <- expandTypeName (table, tyn);
     Some (T_array (ty, n))}
  | TN_struct tag -> Some (T_struct tag)
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
   liftOption (expandTypeName (r.r_xenv.xenv_typedefs, tyn))}

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

op zeroOfType (table:StructTable) (ty:Type) : Option Value =
  case ty of
  | T_void -> None
  | T_struct tag ->
    {membs <- table tag;
     (mems, tys) <- Some (unzip membs);
     vals <- zerosOfTypes table tys;
     Some (V_struct (tag, fromAssocList (zip (mems, vals))))}
  | T_array (ty0, n) ->
    {val0 <- zeroOfType table ty0;
     Some (V_array (ty0, repeat val0 n))}
  | ty -> Some (zeroOfScalarType ty)

(* This just maps zeroOfType over tys *)
op zerosOfTypes (table:StructTable) (tys:List Type) : Option (List Value) =
   mapM_opt (zeroOfType table) tys

(* This lifts zeroOfType into Monad *)
op zeroOfTypeM (ty:Type) : Monad Value =
  {r <- askR;
   liftOption (zeroOfType r.r_xenv.xenv_structures ty)}


%subsection (* Statements *)

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
  | S_assign (expr1, expr2) ->
    {res1 <- evaluate expr1;
     oldval <- expressionValue res1;
     case res1 of
     | Res_pointer (ObjPointer obj) ->
       {newval <- expressionValueM (evaluate expr2);
        newval' <- convertForAssignment (newval, typeOfValue oldval);
        writeObject (obj, newval') }
     | _ -> error}
  | S_call (lhs_expr_opt, fun_expr, arg_exprs) ->
    (* For a function call, first evaluate the arguments and the function *)
    {arg_values <- evaluateAllToValues arg_exprs;
     fun_value <- expressionValueM (evaluate fun_expr);
     (* Next, look up the function and apply it to the args *)
     res_opt <-
       case fun_value of
         | V_pointer (_, FunPointer f_desig) ->
           {(f, _) <- lookupFunction f_desig;
            f arg_values}
         | _ -> error ;
     (* Finally, assign the result to the LHS, if there is one *)
     case (lhs_expr_opt, res_opt) of
       | (None, _) -> return ()
       | (Some lhs_expr, Some res) ->
         {lhs_res <- evaluate lhs_expr;
          case lhs_res of
            | Res_pointer (ObjPointer obj) ->
              writeObject (obj, res)
            | _ -> error}
       | (Some _, None) -> error}
  | S_if (cond_expr, then_branch, else_branch_opt) ->
    (* For an if-statement, evaluate the condition, test if it is zero, and
       then, finally, execute the then or else branch, as appropriate *)
    {condition <- expressionValueM (evaluate cond_expr);
     isZero <- zeroScalarValue? condition;
     if ~ isZero then
       evalStatement then_branch
     else
       case else_branch_opt of
         | Some else_branch -> evalStatement else_branch
         | None -> return ()}
  | S_return (Some expr) ->
    (* For a return statement with an expression, evaluate the expression and
       then do a non-local exit with Err_return (which is not really an error,
       see type Monad.Err above) applied to the value of the expression *)
    {val <- expressionValueM (evaluate expr);
     raiseErr (Err_return (Some val))}
  | S_return None ->
    (* For a return statement with no expression, raise Err_return None *)
    raiseErr (Err_return None)
  | S_while (cond_expr, body) ->
    (* For loops use mfix (FIXME: document this...?) *)
    mfix ((=),
          fn recurse -> fn unit ->
            {condition <- expressionValueM (evaluate cond_expr);
             isZero <- zeroScalarValue? condition;
             if isZero then return () else
               {_ <- evalStatement body;
                recurse ()}}) ()
  | S_do (body, cond_expr) ->
    (* For do loops, execute the body once and then do a while loop *)
    {_ <- evalStatement body;
     evalStatement (S_while (cond_expr, body))}
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
     zero_val <- zeroOfTypeM tp;
     addLocalBinding (id, zero_val)}
  | BlockItem_statement stmt -> evalStatement stmt


%subsection (* Translation Units *)

(* Translation units are evaluated by building up a semantic object containing
all the top-level external declarations in that translation unit. This semantic
object is defined by the type TopLevel, and contains the struct and typedef
tables along with the top-level identifiers and their object or function values.
Note that a function in a TopLevel need not be a TopFunction, meaning that it
can still depend on the function table, because we have not yet "tied the knot";
this is done when we compile a whole program, below.

Note also that translation units are not evaluated inside the Monad.

FIXME HERE: explain why, and explain the basic pattern of evaluating translation
units basically inside the state-error monad. *)

type TopLevel =
   {top_structs   : StructTable,
    top_typedefs  : TypedefTable,
    top_objects   : FiniteMap (Identifier, Value),
    top_functions : FiniteMap (Identifier, CFunction * FunType)}

op emptyTopLevel : TopLevel =
   {top_structs   = empty,
    top_typedefs  = empty,
    top_objects   = empty,
    top_functions = empty}

(* The monad for evaluating translation units *)
type XUMonad a = TopLevel -> Option (TopLevel * a)

(* XUMonad's return and bind *)
op [a] return (x:a) : XUMonad a = fn top -> Some (top, x)
op [a,b] monadBind (m : XUMonad a, f : a -> XUMonad b) : XUMonad b =
  fn top1 -> case m top1 of
             | Some (top2, b) -> f b top2
             | None -> None

(* Run an XUMonad *)
op [a] runXU (m : XUMonad a) : Option (TopLevel * a) =
  m emptyTopLevel

(* The map function for XUMonad *)
op [a,b] mapM_XU (f : a -> XUMonad b) (xs : List a) : XUMonad (List b) =
   case xs of
     | [] -> return []
     | x :: xs' ->
       {new_x <- f x;
        new_xs <- mapM_XU f xs';
        return (new_x :: new_xs)}

(* Get the current TopLevel *)
op xu_get : XUMonad TopLevel =
  fn top -> Some (top, top)

(* An error in XUMonad *)
op [a] xu_error : XUMonad a = fn _ -> None

(* Test that a FiniteMap in the current top-level does not have a binding for id *)
op [a] xu_errorIfBound (id : Identifier, f : TopLevel -> FiniteMap (Identifier, a)) : XUMonad () =
  {top <- xu_get;
   if some? (f top id) then xu_error else return ()}

(* Update the TopLevel *)
op xu_update (f : TopLevel -> TopLevel) : XUMonad () =
  fn top -> Some (f top, ())

(* Lift an Option into XUMonad *)
op [a] liftOption_XU (opt_x : Option a) : XUMonad a =
  case opt_x of
    | Some x -> return x
    | None -> xu_error

(* Expand a TypeName in XUMonad *)
op expandTypeNameXU (tp:TypeName) : XUMonad Type =
  {top <- xu_get;
   liftOption_XU (expandTypeName (top.top_typedefs, tp))}

(* Call zeroOfType in XUMonad *)
op zeroOfTypeXU (tpName:TypeName) : XUMonad Value =
  {top <- xu_get;
   tp <- liftOption_XU (expandTypeName (top.top_typedefs, tpName));
   liftOption_XU (zeroOfType top.top_structs tp)}

(* Look up a value in an alist *)
(* FIXME HERE: this should be in a library somewhere... *)
op [a,b] assoc (l:List (a * b)) (key : a) : Option b =
  case l of
    | [] -> None
    | (x,y)::l' -> if key = x then Some y else assoc l' key

(* Add a key-value pair to an alist in a unique way, returning None if the key
is already in l *)
op [a,b] acons_uniq (l:List (a * b)) (key : a) (val : b) : Option (List (a * b)) =
  case assoc l key of
    | None -> Some (l ++ [(key,val)])
    | Some _ -> None


(* For typedefs, add it to the typedef table, checking first that the typedef
name is not already in the typedef table *)
op evalTypedef (typedef:TypeDefinition) : XUMonad () =
  let id = typedef.Typedef_name in
  {xu_errorIfBound (id, fn top -> top.top_typedefs);
   tp <- expandTypeNameXU typedef.Typedef_type;
   xu_update (fn top ->
                top << {top_typedefs = update top.top_typedefs id tp})}

(* For object declarations, check that the name is not already in the object
table or the function table, get the zero value for the given type, and add the
result to the table. Extern declarations do not go in the current translation
unit; they are just there for type-checking. *)
op evalObjectDeclaration (odecl:ObjectDeclaration) : XUMonad () =
  let id = odecl.ObjDecl_name in
  if odecl.ObjDecl_isExtern then
    return ()
  else
    {xu_errorIfBound (id, fn top -> top.top_objects);
     xu_errorIfBound (id, fn top -> top.top_functions);
     zeroVal <- zeroOfTypeXU (odecl.ObjDecl_type);
     xu_update (fn top ->
                  top << {top_objects =
                              update top.top_objects id zeroVal})}

(* For struct members, expand the type name and make sure it is not void *)
op evalMemberDeclaration (decl:MemberDeclaration) : XUMonad (Identifier * Type) =
  {ty <- expandTypeNameXU (decl.MemDecl_type);
   if (ty = T_void) then xu_error
   else return (decl.MemDecl_name, ty)}

(* For struct declarations, evaluate each struct member, check there are no
   duplicate field names, and check that the struct tag is not already in use *)
op evalStructSpecifier (sspec:StructSpecifier) : XUMonad () =
  let id = sspec.StructSpec_tag in
  {members <- mapM_XU evalMemberDeclaration sspec.StructSpec_members;
   if members = [] || ~(noRepetitions? (unzip members).1)
     then xu_error else return ();
   xu_errorIfBound (id, fn top -> top.top_structs);
   xu_update (fn top ->
                top << {top_structs =
                            update top.top_structs id members})}

(* Expand all the type name in a ParameterDeclaration *)
op evalParameterDeclaration (param:ParameterDeclaration) : XUMonad (Identifier * Type) =
   {ty <- expandTypeNameXU (param.PDecl_type);
    return (param.PDecl_name, ty)}

(* Build a C function that quantifies over a list of argument values and then
   binds those argument values to params in a fresh, top-level scope *)
(* FIXME HERE: move this to a short section above about C functions *)
op makeCFunction (retType : Type, params : List (Identifier * Type), body : Statement) : CFunction =
  fn args ->
    if valuesHaveTypes (args, (unzip params).2) then
      {ret <- catchReturns (withFreshTopBindings
                              (fromAssocList (zip ((unzip params).1, args)))
                              (evalStatement body));
       if optValueHasType (ret, retType) then return ret else error
       }
    else error

(* Build a function by evaluating its return and parameter type names and then
calling makeCFunction *)
op evalCFunction (retTypeName : TypeName,
                  paramDecls : ParameterList, body : Statement) : XUMonad (CFunction * FunType) =
  {retType <- expandTypeNameXU retTypeName;
   params <- mapM_XU evalParameterDeclaration paramDecls;
   return (makeCFunction (retType, params, body),
           (retType, (unzip params).2))}

(* Eval a function definition, by checking that the name is not already defined
in the object or function table and then calling evalCFunction *)
op evalFunctionDeclaration (fdef:FunctionDeclaration) : XUMonad () =
  let id = fdef.FDef_name in
  case fdef.FDef_body of
    | None ->
      (* Ignore function prototypes in the semantics *)
      return ()
    | Some body ->
      {if fdef.FDef_isExtern then xu_error else return ();
       xu_errorIfBound (id, fn top -> top.top_objects);
       xu_errorIfBound (id, fn top -> top.top_functions);
       f_res <- evalCFunction (fdef.FDef_retType, fdef.FDef_params, body);
       xu_update (fn top ->
                    top << {top_functions =
                                update top.top_functions id f_res})}

(* Evaluate any external declaration *)
op evalExternalDeclaration (decl:ExternalDeclaration) : XUMonad () =
  case decl of
    | EDecl_function fdef -> evalFunctionDeclaration fdef
    | EDecl_declaration (Decl_struct sspec) -> evalStructSpecifier sspec
    | EDecl_declaration (Decl_object odecl) -> evalObjectDeclaration odecl
    | EDecl_declaration (Decl_typedef typedef) -> evalTypedef typedef

(* Evaluate a translation unit *)
op evalTranslationUnit (unit:TranslationUnit) : Option TopLevel =
  case runXU (mapM_XU evalExternalDeclaration unit) of
    | Some (top, _) -> Some top
    | None -> None


%subsection (* Programs *)

(* FIXME HERE: document the "tying the knot" stuff here *)

(* FIXME HERE: write this! *)
op combineTopLevels2 (top1 : TopLevel, top2 : TopLevel) : Option TopLevel

(* FIXME HERE: use fold to write this *)
op combineTopLevels (tops : List TopLevel) : Option TopLevel

op initialStorage (top : TopLevel) : Storage =
  {static = top.top_objects, automatic = [], allocated = []}

type MultiFunction = { mf : (Identifier * List Value) -> Monad (Option Value) |
                        fa (tup,f) localR f (mf tup) = mf tup }

op multiFunFromTopLevel (top : TopLevel) (env : TranslationEnv) : MultiFunction =
  fn (id, args) -> case top.top_functions id of
                     | None -> error
                     | Some (cf, _) -> localR (fn _ -> globalRFromEnv env) (cf args)

op envForMultiFunction (top : TopLevel) (mf : MultiFunction) : TranslationEnv =
  {xenv_typedefs   = top.top_typedefs,
   xenv_structures = top.top_structs,
   xenv_functions  =
     fn id -> case top.top_functions id of
                | None -> None
                | Some (_, f_tp) -> Some ((fn args -> mf (id, args)), f_tp)}

op initialEnv (top : TopLevel) : TranslationEnv =
  envForMultiFunction top
   (mfix ((=),
          fn mf -> multiFunFromTopLevel top (envForMultiFunction top mf)))

(* Build the TopLevel for all the translation units,  *)
op evalProgram (pgm : Program) : Monad () =
   {top <- liftOption {tops <- mapM_opt evalTranslationUnit pgm;
                       combineTopLevels tops};
    initHeap <- return (initialStorage top);
    initEnv <- return (initialEnv top);
    putState initHeap;
    localR (fn _ -> globalRFromEnv initEnv)
      (evalStatement (S_call (None, E_ident "main",
                              [E_const (T_uint, 0), E_nullconst])))
    }

end-spec
