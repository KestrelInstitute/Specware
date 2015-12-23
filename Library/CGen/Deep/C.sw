(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

C qualifying spec

import /Library/General/TwosComplementNumber
import /Library/General/FunctionExt
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
  ex(digits:String)
    (str = "0x" ^ digits || str = "0X" ^ digits) &&  % prefix
    (let chars = explode digits in
    nonEmpty? chars &&
    forall? hexadecimalDigit? chars)

(* An integer constant has an optional suffix, which consists of an unsigned
suffix and/or a long or long long suffix. *)

op unsignedSuffix? (str:String) : Bool =
  str = "u" || str = "U"

op longSuffix? (str:String) : Bool =
  str = "l" || str = "L"

op longLongSuffix? (str:String) : Bool =
  str = "ll" || str = "LL"

(* The following op captures an optional unsigned suffix, i.e. either nothing
(the empty string) or an unsigned suffix. This op does not directly correspond
to any non-terminal symbol in the grammar in [ISO 6.4.4.1], but we introduce it
for convenience. *)

op signSuffix? (str:String) : Bool =
  str = "" || unsignedSuffix? str

(* Similarly, the following op captures an optional long or long suffix, i.e.
either nothing (the empty string) or a long suffix or a long long suffix. This
op does not directly correspond to any non-terminal symbol in the grammar in
[ISO 6.4.4.1], but we introduce it for convenience. *)

op lengthSuffix? (str:String) : Bool =
  str = "" || longSuffix? str || longLongSuffix? str

(* We can then say that an optional integer suffix consists of a sign suffix and
a length suffix, in any order. Note that they can be both empty. *)

op integerSuffix? (str:String) : Bool =
  ex (ssuffix:String, lsuffix:String)
    signSuffix? ssuffix &&
    lengthSuffix? lsuffix &&
    (str = ssuffix ^ lsuffix || str = lsuffix ^ ssuffix)

(* Finally, we define an integer constant as a decimal, octal, or hexadecimal
constant, followed by an optional integer suffix. *)

op integerConstant? (str:String) : Bool =
  ex (const:String, suffix:String)
    str = const ^ suffix
    &&
    (decimalConstant?     const ||
     octalConstant?       const ||
     hexadecimalConstant? const)
    &&
    integerSuffix? suffix

type IntegerConstant = (String | integerConstant?)

(* We can easily remove the suffix of an integer constant, if any. *)

op unsuffixedIntegerConstant (c:IntegerConstant) : String =
  the(str:String)
     (ex(suffix:String) c = str ^ suffix && integerSuffix? suffix)


%subsection (* Types *)

(* Our C subset features the following types [ISO 6.2.5]: the standard signed
and unsigned integer types, the (plain) char type, structure types, pointer
types, array types, and the void type. Each of the signed/unsigned
short/int/long/longlong types can be denoted via multiple, equivalent
combinations of type specifiers [ISO 6.7.2]. Even though certain types may have
identical representations in an implementation, they are nevertheless different
types [ISO 6.2.5/14]. A structure type is denoted by its tag, which is an
identifier [ISO 6.2.3]. An array type includes the number of elements [ISO
6.2.5/20]; our C subset only includes array types with known size. *)

type Type =
  | char                %          char
  | uchar               % unsigned char
  | schar               %   signed char
  | ushort              % unsigned short
  | sshort              %   signed short
  | uint                % unsigned int
  | sint                %   signed int
  | ulong               % unsigned long
  | slong               %   signed long
  | ullong              % unsigned long long
  | sllong              %   signed long long
  | struct  Identifier  % structure
  | pointer Type        % pointer (to type)
  | array   Type * Nat  % array (of type of size)
  | void                % void

(* The following are the standard signed integer types [ISO 6.2.5/4] *)

op standardSignedIntegerType? (ty:Type) : Bool =
  ty = schar || ty = sshort || ty = sint || ty = slong || ty = sllong

(* Our C subset has no extended signed integer types [ISO 6.2.5/4], so the
signed integer types [ISO 6.2.5/4] coincide with the standard signed integer
types. *)

op signedIntegerType? (ty:Type) : Bool = standardSignedIntegerType? ty

(* The following are the standard unsigned integer types [ISO 6.2.5/6]. *)

op standardUnsignedIntegerType? (ty:Type) : Bool =
  ty = uchar || ty = ushort || ty = uint || ty = ulong || ty = ullong

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
  ty = char || signedIntegerType? ty || unsignedIntegerType? ty

(* The following are the character types [ISO 6.2.5/15]. *)

op characterType? (ty:Type) : Bool =
  ty = char || ty = uchar || ty = schar

(* The following are the integer types [ISO 6.2.5/17]. Our C subset has no
enumerated types. *)

op integerType? (ty:Type) : Bool =
  ty = char || signedIntegerType? ty || unsignedIntegerType? ty

(* The following are the real types [ISO 6.2.5/17]. Our C subset has no floating
types. *)

op realType? (ty:Type) : Bool =
  integerType? ty

(* The following are the arithmetic types [ISO 6.2.5/18]. Our C subset has no
floating types. *)

op arithmeticType? (ty:Type) : Bool =
  integerType? ty

(* The following are the derived types [ISO 6.2.5/20]. Our C subset has no
union, no atomic, and no (explicit) function types. *)

op derivedType? (ty:Type) : Bool =
  embed? struct ty || embed? pointer ty || embed? array ty

(* The following are the scalar types [ISO 6.2.5/21]. *)

op scalarType? (ty:Type) : Bool =
  arithmeticType? ty || embed? pointer ty

(* The following are the aggregate types [ISO 6.2.5/21]. *)

op aggregateType? (ty:Type) : Bool =
  embed? struct ty || embed? array ty

(* In our C subset, all types are complete types [ISO 6.2.5/1] except void [ISO
6.2.5/19]. *)

op completeType? (ty:Type) : Bool =
  ty ~= void

(* The following predicates are not explicitly defined in [ISO 6.2.5] but are
useful in our formalization. *)

op shortType? (ty:Type) : Bool =
  ty = sshort || ty = ushort

op intType? (ty:Type) : Bool =
  ty = sint || ty = uint

op longType? (ty:Type) : Bool =
  ty = slong || ty = ulong

op llongType? (ty:Type) : Bool =
  ty = sllong || ty = ullong

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

(* Our C subset features the following kinds of expressions [ISO 6.5]:
identifiers [ISO 6.5.1/1], integer constants [ISO 6.5.1/1], unary expressions
using the unary operators introduced above, binary expressions using the binary
operators introduced above, conditional expressions [ISO 6.5.15], structure
member expressions (i.e. the '.' and '->' operators, respectively denoted by the
constructors 'member' and 'memberp', where 'p' suggests that the left operand
must be a pointer, as required for '->') [ISO 6.5.2.3], array subscripting [ISO
6.5.2.1], and the null pointer constant [ISO 6.3.2.3/3] '(void* ) 0' (we leave
one space between the '*' and the ')' because comments in Specware do not nest).
The fourth argument (a type) of the 'cond' constructor is the type of the result
of the conditional expression, inferred by the compiler -- the reason for this
is explained later. We use a dedicated constructor for the null pointer constant
'(void* ) 0' to avoid introducing casts in our C subset just for the purpose of
modeling this null pointer constants. *)

type Expression =
  | ident     Identifier
  | const     IntegerConstant
  | unary     UnaryOp * Expression
  | binary    Expression * BinaryOp * Expression
  | cond      Expression * Expression * Expression * Type
  | member    Expression * Identifier
  | memberp   Expression * Identifier
  | subscript Expression * Expression
  | nullconst

(* In our C subset, the only null pointer constant [ISO 6.3.2.3/3] is '(void* )
0', captured by constructor 'nullconst' above. *)

op nullPointerConst? (expr:Expression) : Bool =
  embed? nullconst expr


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
pointers and arrays of typedef names. *)

type TypeName =
  % same as type Type:
  | char
  | uchar
  | schar
  | ushort
  | sshort
  | uint
  | sint
  | ulong
  | slong
  | ullong
  | sllong
  | struct  Identifier
  | pointer TypeName
  | array   TypeName * Nat
  | void
  % typedef name:
  | typedef Identifier


%subsection (* Declarations *)

(* We model an object [ISO 3.15] declaration [ISO 6.7] as a pair consisting of a
type name and an identifier. Such a named object is commonly referred to as
'variable', even though [ISO] seems to carefully avoid this term.

Our model of object declarations excludes explicit storage class specifiers [ISO
6.7.1] and type qualifiers [ISO 6.7.3]. It also excludes any declarator other
than a simple identifier [ISO 6.7.6], as well as any explicit initializer [ISO
6.7.9]. *)

type ObjectDeclaration =
 {typE : TypeName,
  name : Identifier}

(* [ISO 6.7.2.1/1] uses the term 'struct-declaration' for the members of a
structure or union type specifier. This term seems unfortunate because it is a
declaration for a member of a structure, not for the whole structure, and it
also applies to unions, which are not structures. Thus, we prefer to deviate
from the [ISO 6.7.2.1/1] terminology and use the term 'member declaration',
which we model as a pair consisting of a type name and an identifier. *)

type MemberDeclaration =
  {typE : TypeName,
   name : Identifier}

(* We model a structure specifier [ISO 6.7.2.1] as a pair consisting of a tag
(which is an identifier) and a list of member declarations. Thus, we require the
tag and the members to be always present and we exclude bit fields. *)

type StructSpecifier =
  {tag     : Identifier,
   members : List MemberDeclaration}

(* We model a type definition [ISO 6.7.8] as a pair consisting of a type name
and an identifier. *)

type TypeDefinition =
  {typE : TypeName,
   name : Identifier}

(* The following are the declarations [ISO 6.7] that, as defined later, can
appear at the top level in a translation unit in our C subset. *)

type Declaration =
  | struct  StructSpecifier
  | object  ObjectDeclaration
  | typedef TypeDefinition


%subsection (* Statements *)

(* Our C subset features expression statements [ISO 6.8.3] that are (i) simple
assignment expressions [ISO 6.5.16.1] (whose left and right operands are
expressions in our C subset), or (ii) simple assignment expressions whose left
operand is an expression in our C subset but whose right operand is a function
call [ISO 6.5.2.2], or (iii) function calls [ISO 6.5.2.2]. Cases (ii) and (iii)
are consolidated in constructor 'call' below, where the left operand is an
optional expression (in our C subset) and the right operand consists of the name
of a function plus a list of argument expressions. By modeling assignments and
function calls as statements in our model (vs. expressions as in full C), we
limit such expressions to occur at the top level (or second level from the top,
in the case of a function call assigned to an expression), i.e. as expression
statements. In particular, we exclude multiple assignments like 'a = b = ...'
Note also that, by having function calls not be expressions in our subset, we
maintain expressions free of side effects.

Besides these expression statements, our C subset includes 'if' selection
statements [ISO 6.8.4.1], 'return' jump statements [ISO 6.8.6.4], 'while', 'do',
and 'for' iteration statements [ISO 6.8.5], and compound statements
(i.e. blocks) [ISO 6.8.2]. Our 'if' statement captures both the variant with
'else' and the variant without 'else', based on the presence of the second,
optional statement. A 'return' statement [ISO 6.8.6.4] includes an optional
expression.

Because of our treatment of assignments and function calls as statements, we use
statements as the first and third (optional) expressions of a 'for' statement.
Later in our model we restrict such statements to assignments and function
calls. Expressions in our model have no side effects, so allowing expressions in
(our model of) 'for' statements would not be very useful.

Besides statements, we only allow object declarations as block items [ISO
6.8.2], not other kinds of declarations. *)

type Statement =
  | assign Expression * Expression
  | call   Option Expression * Identifier * List Expression
  | iF     Expression * Statement * Option Statement
  | return Option Expression
  | while  Expression * Statement
  | do     Statement * Expression
  | for    Option Statement * Option Expression * Option Statement * Statement
  | block  List BlockItem

type BlockItem =
  | declaration ObjectDeclaration
  | statement   Statement


%subsection (* Function definitions *)

(* In our C subset, a (function) parameter declaration [ISO 6.7.6/1] consists of
a type name and a name. A parameter list [ISO 6.7.6/1] is a list of parameter
declarations. In our C subset, a parameter list is also a parameter type list
[ISO 6.7.6/1], because we disallow ellipsis in function definitions. *)

type ParameterDeclaration =
  {typE : TypeName,
   name : Identifier}

type ParameterList = List ParameterDeclaration

(* A function definition consists of a return type (name), a name, a parameter
list, and a body [ISO 6.7.6.3, 6.9.1]. *)

type FunctionDefinition =
 {return     : TypeName,
  name       : Identifier,
  parameters : ParameterList,
  body       : Statement}


%subsection (* Translation units *)

(* Our C subset has no preprocessing directives [ISO 6.10], so a preprocessing
translation unit [ISO 5.1.1.1/1] is the same as a translation unit [ISO 6.9] --
essentially, a file.

A translation unit consists of zero or more external declarations, where an
external declaration is either a function definition or a declaration as defined
earlier [ISO 6.9/1]. *)

type ExternalDeclaration =
  | function    FunctionDefinition
  | declaration Declaration

type TranslationUnit = List ExternalDeclaration


%subsection (* Programs *)

(* A C program consists of a set of source files [ISO 5.1.1.1/1]. Since our C
subset has no '#include' directives [ISO 6.10], a source file coincides with a
preprocessing translation unit, which, as explained above, coincides with a
translation unit. Thus, in our C subset a program consists of translation units.
We limit the number of translation units to one, i.e. a program is a single
translation unit. *)

type Program = TranslationUnit


%section (* Constraints *)

(* [ISO] states several constrains that the syntactic entities that comprise a
program must satisfy in order for the program to be accepted and translated [ISO
5.1.1] by an implementation, i.e. by a compiler. *)


%subsection (* Auxiliary concepts *)    

(* Before formalizing the actual constraints, we introduce some auxiliary
concepts used to express the constraints. *)


%subsubsection (* Minimum, maximum, and range of integer types *)

(* We introduce ops to map each integer type to its min and max value, as well
as range of values.*)

op minOfIntegerType (ty:Type | integerType? ty) : Int =
  case ty of
  |  char  ->  CHAR_MIN
  | uchar  ->         0
  | schar  -> SCHAR_MIN
  | ushort ->         0
  | sshort ->  SHRT_MIN
  | uint   ->         0
  | sint   ->   INT_MIN
  | ulong  ->         0
  | slong  ->  LONG_MIN
  | ullong ->         0
  | sllong -> LLONG_MIN

op maxOfIntegerType (ty:Type | integerType? ty) : Int =
  case ty of
  |  char  ->   CHAR_MAX
  | uchar  ->  UCHAR_MAX
  | schar  ->  SCHAR_MAX
  | ushort ->  USHRT_MAX
  | sshort ->   SHRT_MAX
  | uint   ->   UINT_MAX
  | sint   ->    INT_MAX
  | ulong  ->  ULONG_MAX
  | slong  ->   LONG_MAX
  | ullong -> ULLONG_MAX
  | sllong ->  LLONG_MAX

op rangeOfIntegerType (ty:Type | integerType? ty) : FiniteSet Int =
  fn x:Int -> minOfIntegerType ty <= x && x <= maxOfIntegerType ty


%subsubection (* Corresponding signed/unsigned integer types *)

(* The following ops associate each signed/unsigned integer type to the
corresponding unsigned/signed integer type. *)

op correspondingUnsignedOf (ty:Type | signedIntegerType? ty) : Type =
  case ty of
  | schar  -> uchar
  | sshort -> ushort
  | sint   -> uint
  | slong  -> ulong
  | sllong -> ullong

op correspondingSignedOf (ty:Type | unsignedIntegerType? ty) : Type =
  case ty of
  | uchar  -> schar
  | ushort -> sshort
  | uint   -> sint
  | ulong  -> slong
  | ullong -> sllong


%subsubsection (* Values of integer constants *)

(* The value of an integer constant [ISO 6.4.4.1/4] is known at compile time. It
is a natural number.

We start with the value of a digit, including hex(adecimal) digits. *)

op digitValue (ch:Char | digit? ch) : Nat =
  ord ch - ord #0

op hexDigitValue (ch:Char | hexadecimalDigit? ch) : Nat =
  if digit? ch then digitValue ch
  else if isUpperCase ch then ord ch - ord #A + 10
                         else ord ch - ord #a + 10

(* The digits of a decimal, octal, or hexadecimal constant are in big endian
format. So, we use the library op fromBigEndian with argument base 10, 8, and
16. For hexadecimal constant, we need to remove the 2-character 0x/0X prefix
first. *)

op decimalConstantValue (str:String | decimalConstant? str) : Nat =
  fromBigEndian (map digitValue (explode str), 10)

op octalConstantValue (str:String | octalConstant? str) : Nat =
  fromBigEndian (map digitValue (explode str), 8)

op hexadecimalConstantValue (str:String | hexadecimalConstant? str) : Nat =
  let digits = removePrefix (explode str, 2) in
  fromBigEndian (map hexDigitValue digits, 16)

(* To calculate the value of an integer constant, we remove the suffix (if any)
and then we use one of the three ops just defined. Note that the suffix does not
contribute to the value of the constant. *)

op integerConstantValue (c:IntegerConstant) : Nat =
  let unsuffixed:String = unsuffixedIntegerConstant c in
       if decimalConstant? unsuffixed then     decimalConstantValue unsuffixed
  else if   octalConstant? unsuffixed then       octalConstantValue unsuffixed
  else                                     hexadecimalConstantValue unsuffixed


%subsubsection (* Integer conversion ranks *)

(* The integer conversion ranks [ISO 6.3.1.1/1] can be expressed via a list of
lists of (integer) types, where the types in each inner list all have the same
rank, and where the inner lists are ordered, within the outer list, with
increasing ranks. *)

op rankedTypes : List (List Type) =
  [[char, uchar, schar],
   [sshort, ushort],
   [sint, uint],
   [slong, ulong],
   [sllong, ullong]]

(* From that structure, we can easily define binary relations for
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
  if ty rank_<= sint then
    if rangeOfIntegerType ty <= rangeOfIntegerType sint then sint else uint
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


%subsubsection (* Symbol tables *)

(* In a compiler, a symbol table associates information to the identifiers in a
program (e.g. a type is associated to each variable). A symbol table captures
the identifiers in scope [ISO 6.2.1], which is useful in order to check
constraints (e.g. that a referenced object is in scope).

We start by defining a symbol table for type definitions, i.e. an association of
types to typedef names. *)

type TypedefTable = FiniteMap (Identifier, Type)

(* A structure type, introduced by a structure specifier, consists of typed
members, modeled as a finite map from member names to their types. A symbol
table for structure specifiers associates typed members to structure tags (which
are identifiers). *)

type TypedMembers = FiniteMap (Identifier, Type)

type StructTable = FiniteMap (Identifier, TypedMembers)

(* A symbol table for objects is organized as a list that corresponds to the
nesting of scopes. The head of the list corresponds to the file scope [ISO
6.2.1/4], while the rest of the list corresponds to nested block scopes [ISO
6.2.1/4]. *)

type ObjectTable = List (FiniteMap (Identifier, Type))

(* A function has zero or more typed parameters, captured as follows. *)

type TypedParameter =
  {typE : Type,
   name : Identifier}

type TypedParameters = List TypedParameter

(* A symbol table for functions associates return types and typed parameters to
the function names. *)

type FunctionTable = FiniteMap (Identifier, Type * TypedParameters)

(* Note that in our C subset type definitions and structure specifiers always
have file scope, and so their respective symbol tables are "flat" maps, instead
of lists of maps like object declarations.

A symbol table consists of a symbol table for type definitions, structure
specifiers, objects, and functions. *)

type SymbolTable =
 {typedefs   : TypedefTable,
  structures : StructTable,
  objects    : ObjectTable,
  functions  : FunctionTable}

(* The following op looks up an object in a symbol table, starting with the last
map in the list (which corresponds to the innermost scope) and proceeding
leftward into the list (i.e. moving to outer and outer scopes). 'None' is
returned if the object is not found. If found, its type is returned. Note that
the first type found for the object is returned, consistently with the fact that
an identifier declared in an inner scope may hide a homonymous identifier
declared in an outer scope [ISO 6.2.1/4]. *)

op objectTypeInSymTab (symtab:SymbolTable, name:Identifier) : Option Type =
  let def aux (scopes: List (FiniteMap (Identifier, Type))) : Option Type =
    if empty? scopes then
      None
    else
      let (outer, innermost) = (butLast scopes, last scopes) in
      case innermost name of
      | Some ty -> Some ty
      | None -> aux outer
  in
  aux symtab.objects


%subsection (* Actual constraints *)

(* In our formalization, constraints on syntactic entities are expressed via ops
called 'check...' which either succeed, possibly returning some information
about the checked entity (e.g. the inferred type of an expression), or fail,
indicating that a compiler may reject the program. Compilers may differ in their
"permissiveness", but since we are interested in maximally portable programs, we
want our checking ops to succeed only when all (conforming [ISO 4]) compilers
do.

Failure is modeled using 'Option', which is applied to the (Specware) type of
information to be returned in case of success. When no success information needs
to be returned, the unit type () is used. The following op turns a boolean into
an 'Option ()' value -- its use will be clear in the ops below. *)

op check (b:Bool) : Option () =
  if b then Some () else None


%subsubsection (* Constants *)

(* Since u/U are not (hex) digits or the prefix 0x/0X, to test whether an
integer constant includes an unsigned suffix it suffices to check whether an
integer suffix occurs anywhere in the constant. Analogous reasoning applies to
ll/LL long long suffixes. For the l/L long suffixes, we use the same test, after
making sure that there are no long long suffixes, because l/L is a substring of
ll/LL. *)

op unsignedConstant? (c:IntegerConstant) : Bool =
  ex (str1:String, u:String, str2:String)
    c = str1 ^ u ^ str2 &&
    unsignedSuffix? u

op longLongConstant? (c:IntegerConstant) : Bool =
  ex (str1:String, ll:String, str2:String)
    c = str1 ^ ll ^ str2 &&
    longLongSuffix? ll

op longConstant? (c:IntegerConstant) : Bool =
  ~ (longLongConstant? c) &&
  (ex (str1:String, l:String, str2:String)
     c = str1 ^ l ^ str2 &&
     longSuffix? l)

(* An integer constant must have a type into which the value of the constant
fits [ISO 6.4.4.1/5]. The type is determined using the table in [ISO 6.4.4.1/5],
which associates to each integer constant a list of candidate types, based on
the suffixes and the base of the constant. The type of the constant is the first
in the associated list into which the constant's value fits. The checking op for
integer constants returns the type of the constant, or 'None' if the constant
cannot be assigned any type. *)

op integerConstantCandidateTypes (c:IntegerConstant) : List Type =
  let unsuffixed:String = unsuffixedIntegerConstant c in
  let decimal?:Bool = decimalConstant? unsuffixed in
  if ~ (unsignedConstant? c) &&
     ~ (longConstant? c) &&
     ~ (longLongConstant? c) then
    if decimal? then [sint, slong, sllong]
                else [sint, uint, slong, ulong, sllong, ullong]
  else if unsignedConstant? c &&
          ~ (longConstant? c) &&
          ~ (longLongConstant? c)
  then
    [uint, ulong, ullong]
  else if ~ (unsignedConstant? c) &&
          longConstant? c then
    if decimal? then [slong, sllong]
                else [slong, ulong, sllong, ullong]
  else if unsignedConstant? c &&
          longConstant? c then
    [ulong, ullong]
  else if ~ (unsignedConstant? c) &&
          longLongConstant? c then
    if decimal? then [sllong]
                else [sllong, ullong]
  else
    [ullong]

op checkIntegerConstant (c:IntegerConstant) : Option Type =
  let tys = integerConstantCandidateTypes c in
  let val:Nat = integerConstantValue c in
  if (ex(i:Nat) i < length tys && (val:Int) in? rangeOfIntegerType (tys @ i))
  then
    let firstFitIndex:Nat = the(firstFitIndex:Nat)
        firstFitIndex < length tys &&
        (val:Int) in? rangeOfIntegerType (tys @ firstFitIndex) &&
        (firstFitIndex = 0 ||  % first type in candidate list
         (val: Int) nin? rangeOfIntegerType (tys @ (firstFitIndex - 1))) in
    Some (tys @ firstFitIndex)
  else
    None


%subsubsection (* Types *)

(* The following op checks whether a type is a structure type, and in that case
it returns its tag. *)

op checkStructType (ty:Type) : Option Identifier =
  case ty of
  | struct tag -> Some tag
  | _ -> None

(* The following op checks whether a type is a pointer type, and in that case it
returns its referenced type. *)

op checkPointerType (ty:Type) : Option Type =
  case ty of
  | pointer ty0 -> Some ty0
  | _ -> None

(* The following op checks whether a type is an array type, and in that case it
returns its element type and its size. *)

op checkArrayType (ty:Type) : Option (Type * Nat) =
  case ty of
  | array (ty0, n) -> Some (ty0, n)
  | _ -> None

(* The following op checks whether a type is a pointer or array type, and in
that case it returns the referenced or array type. *)

op checkPointerOrArrayType (ty:Type) : Option Type =
  case ty of
  | pointer ty0 -> Some ty0
  | array (ty0, _) -> Some ty0
  | _ -> None


%subsubsection (* Expressions *)

(* Each expression has a compile-time type. Furthermore, some expressions denote
objects, while others denote values [ISO 6.5/1]; the former can be used as left
operand of an assignment (lvalues [ISO 6.3.2.1/1]), while the latter cannot. We
introduce the notion of an expression type as a type accompanied by a flag that
says whether the expression denotes an object (vs. just a value). *)

type ExpressionType =
  {typE   : Type,
   object : Bool}

op exprTypeObject (ty:Type) : ExpressionType =
  {typE = ty, object = true}

op exprTypeValue (ty:Type) : ExpressionType =
  {typE = ty, object = false}

(* The expression checking op returns an expression type. If checking fails,
'None' is returned. Most operators operate on values, but can accept operands
that denote objects because in that case the value stored in the object is used.

A variable denotes an object [ISO 6.5.1/2]. Its type is the declared type of the
variable, which is stored in the symbol table.

A constant denotes a value [ISO 6.5.1/3]. Its type is formalized above.

The unary '+' and '-' operators require an arithmetic operand [ISO 6.5.3.3/1]
and their result has the promoted type of the operand [ISO 6.5.3.3/2,
6.5.3.3/3].  The expression denotes a value.

The '~' operator requires an integer operand [ISO 6.5.3.3/1] and its result has
the promoted type of the operand [ISO 6.5.3.3/4]. The expression denotes a
value.

The '!' operator requires a scalar operand [ISO 6.5.3.3/1] and its result is a
signed int [ISO 6.5.3.3/5]. The expression denotes a value. Even though,
according to [ISO 6.3.2.1/3], an array could be used as operand (because it is
converted to a pointer), in our C subset we impose a more disciplined use of
arrays and so we do not automatically convert them to pointers.

The unary '&' operator requires an operand that denotes an object [ISO
6.5.3.2/1]: this covers the lvalue case as well as (i) the case of a result of
the unary '*' operator and (ii) the case of a result of the '[ ]' operator; both
'*' and '[ ]', as formalized below, denote objects. The result of the unary '&'
operator is a pointer to the type of the operand.

The unary '*' operator requires a pointer operand [ISO 6.5.3.2/2] and its result
is the referenced type [ISO 6.5.3.2/4]. The expression denotes an object [ISO
6.5.3.2/4]. Even though, according to [ISO 6.3.2.1/3], an array could be used as
operand (because it is converted to a pointer), in our C subset we impose a more
disciplined use of arrays and so we do not automatically convert them to
pointers for the '*' operator.

The binary '*' operator and the '/' operator require arithmetic operands [ISO
6.5.5/2] and their result has the type arising from the usual arithmetic
conversions [ISO 6.5.5/3, 6.5.5/4]. The expression denotes a value.

The '%' operator requires integer operands [ISO 6.5.5/2] and its result has the
type arising from the usual arithmetic conversions [ISO 6.5.5/3, 6.5.5/5]. The
expression denotes a value.

The binary '+' and '-' operators require arithmetic operands (our C subset
excludes pointer arithmetic) [ISO 6.5.6/2, 6.5.6/3] and their result has the
type arising from the usual arithmetic conversions [ISO 6.5.6/4, 6.5.6/5,
6.5.6/6]. The expression denotes a value.

The '<<' and '>>' operators require integer operands [ISO 6.5.7/2] and their
result has the promoted type of the left operand [ISO 6.5.7/3]. The expression
denotes a value.

The '<', '>', '<=', and '>=' operators require real operands (our C subset
excludes pointer comparisons) [ISO 6.5.8/2] and their result is a signed int
[ISO 6.5.8/6] value.

The '==' and '!=' operators require [ISO 6.5.9/2] (i) two arithmetic operands,
or (ii) two pointers to compatible types, or (iii) a pointer to a non-void type
and a pointer to void, or (iv) a pointer and a null pointer constant. Since, as
explained earlier, the null pointer constant has type 'void*', case (iv) is
covered by case (iii). The result of these operators is a signed int [ISO
6.5.9/3] value. Even though, according to [ISO 6.3.2.1/3], an array could be
used as operand (because it is converted to a pointer), in our C subset we
impose a more disciplined use of arrays and so we do not automatically convert
them to pointers.

The binary '&' operator, the '^' operator, and the '|' operator require integer
operands [ISO 6.5.10/2, 6.5.11/2, 6.5.12/2] and their result has the type
arising from the usual arithmetic conversions [ISO 6.5.10/3, 6.5.10/4, 6.5.11/3,
6.5.11/4, 6.5.12/3, 6.5.12/4]. The expression denotes a value.

The '&&' and '||' operators require scalar operands [ISO 6.5.13/2, 6.5.14/2] and
their result is a signed int [ISO 6.5.13/3, 6.5.14/3] value. Even though,
according to [ISO 6.3.2.1/3], an array could be used as operand (because it is
converted to a pointer), in our C subset we impose a more disciplined use of
arrays and so we do not automatically convert them to pointers.

The first operand of a conditional operator must be scalar [ISO 6.5.15/2]. The
second and third operands must be (i) two arithmetic operands, or (ii) two
structures of the same type, or (iii) two pointers to compatible types, or (iv)
a pointer and a null pointer constant, or (v) a pointer to a non-void type and a
pointer to void [ISO 6.5.15/3]. The case of both expressions having type void
does not apply to our C subset, because expressions in our C subset always have
non-void type. The type of the result depends on the types of the operands: in
case (i), the type of the result is the one arising from the usual arithmetic
conversions [ISO 6.5.15/5]; in case (ii), the type of the result is obviously
the common structure type; in case (iii), the result is a pointer to the
composite type [ISO 6.5.15/6]; in case (iv), the result has the type of the
operand that is not a null pointer constant [ISO 6.5.15/6]; in case (v), the
result is a pointer to void. The type of the result must be the fourth argument
of the 'cond' constructor -- the reason for it is explained later. A conditional
expression denotes a value. Even though, according to [ISO 6.3.2.1/3], an array
could be used as the first operand (because it is converted to a pointer), in
our C subset we impose a more disciplined use of arrays and so we do not
automatically convert them to pointers.

The '.' operator requires a structure type (in scope) as the left operand and a
member of that structure as the right operand [ISO 6.5.2.3/1]. The expression
has the type of the member [ISO 6.5.2.3/3]. The expression denotes an object if
the left operand does, otherwise a value [ISO 6.5.2.3/3].

The '->' operator requires a pointer to a structure type (in scope) as the left
operand and a member of that structure type as the right operand [ISO
6.5.2.3/2]. The expression has the type of the member and denotes an object [ISO
6.5.2.3/4]. Even though, according to [ISO 6.3.2.1/3], an array could be used as
operand (because it is converted to a pointer), in our C subset we impose a more
disciplined use of arrays and so we do not automatically convert them to
pointers when used as left operands of '->'.

The '[ ]' operator requires a pointer as the first operand and an integer as the
second operand, and its result has the referenced type of the pointer [ISO
6.5.2.1/1]. An array is also allowed as first operand, because it is converted
to a pointer [ISO 6.3.2.1/3]. The expression denotes an object -- the element of
the array at the index that the second operand evaluates to.

The null pointer constant denotes a value whose type, as explained earlier, is
void*. *)

op checkExpression
   (symtab:SymbolTable, expr:Expression) : Option ExpressionType =
  case expr of
  | ident var ->
    {ty <- objectTypeInSymTab (symtab, var);
     Some (exprTypeObject ty)}
  | const c ->
    {ty <- checkIntegerConstant c;
     Some (exprTypeValue ty)}
  | unary (uop, expr) ->
    {ety <- checkExpression (symtab, expr);
     ty <- Some ety.typE;
     case uop of
     | PLUS  ->
       {check (arithmeticType? ty);
        Some (exprTypeValue (promoteType ty))}
     | MINUS ->
       {check (arithmeticType? ty); 
        Some (exprTypeValue (promoteType ty))}
     | NOT ->
       {check (integerType? ty);
        Some (exprTypeValue (promoteType ty))}
     | NEG ->
       {check (scalarType? ty);
        Some (exprTypeValue sint)}
     | ADDR ->
       {check ety.object;
        Some (exprTypeValue (pointer ty))}
     | STAR ->
       {ty0 <- checkPointerType ty;
        Some (exprTypeObject ty0)}}
  | binary (expr1, bop, expr2) ->
    {ety1 <- checkExpression (symtab, expr1);
     ety2 <- checkExpression (symtab, expr2);
     ty1 <- Some ety1.typE;
     ty2 <- Some ety2.typE;
     case bop of
     | MUL ->
       {check (arithmeticType? ty1 && arithmeticType? ty2);
        Some (exprTypeValue (arithConvertTypes (ty1, ty2)))}
     | DIV ->
       {check (arithmeticType? ty1 && arithmeticType? ty2);
        Some (exprTypeValue (arithConvertTypes (ty1, ty2)))}
     | REM ->
       {check (integerType? ty1 && integerType? ty2);
        Some (exprTypeValue (arithConvertTypes (ty1, ty2)))}
     | ADD ->
       {check (arithmeticType? ty1 && arithmeticType? ty2);
        Some (exprTypeValue (arithConvertTypes (ty1, ty2)))}
     | SUB ->
       {check (arithmeticType? ty1 && arithmeticType? ty2);
        Some (exprTypeValue (arithConvertTypes (ty1, ty2)))}
     | SHL ->
       {check (integerType? ty1 && integerType? ty2);
        Some (exprTypeValue (promoteType ty1))}
     | SHR ->
       {check (integerType? ty1 && integerType? ty2);
        Some (exprTypeValue (promoteType ty1))}
     | LT ->
       {check (realType? ty1 && realType? ty2);
        Some (exprTypeValue sint)}
     | GT ->
       {check (realType? ty1 && realType? ty2);
        Some (exprTypeValue sint)}
     | LE ->
       {check (realType? ty1 && realType? ty2);
        Some (exprTypeValue sint)}
     | GE ->
       {check (realType? ty1 && realType? ty2);
        Some (exprTypeValue sint)}
     | EQ ->
       {check
          (arithmeticType? ty1 && arithmeticType? ty2 ||
           embed? pointer ty1 && embed? pointer ty2 &&
           (compatibleTypes? (ty1, ty2) ||
            ty1 = pointer void || ty2 = pointer void));
        Some (exprTypeValue sint)}
     | NE ->
       {check
          (arithmeticType? ty1 && arithmeticType? ty2 ||
           embed? pointer ty1 && embed? pointer ty2 &&
           (compatibleTypes? (ty1, ty2) ||
            ty1 = pointer void || ty2 = pointer void));
        Some (exprTypeValue sint)}
     | AND ->
       {check (integerType? ty1 && integerType? ty2);
        Some (exprTypeValue (arithConvertTypes (ty1, ty2)))}
     | XOR ->
       {check (integerType? ty1 && integerType? ty2);
        Some (exprTypeValue (arithConvertTypes (ty1, ty2)))}
     | IOR ->
       {check (integerType? ty1 && integerType? ty2);
        Some (exprTypeValue (arithConvertTypes (ty1, ty2)))}
     | LAND ->
       {check (scalarType? ty1 && scalarType? ty2);
        Some (exprTypeValue sint)}
     | LOR ->
       {check (scalarType? ty1 && scalarType? ty2);
        Some (exprTypeValue sint)}}
  | cond (expr1, expr2, expr3, ty) ->
    {ety1 <- checkExpression (symtab, expr1);
     ety2 <- checkExpression (symtab, expr2);
     ety3 <- checkExpression (symtab, expr3);
     ty1 <- Some ety1.typE;
     ty2 <- Some ety2.typE;
     ty3 <- Some ety3.typE;
     check (scalarType? ty1);
     if arithmeticType? ty2 && arithmeticType? ty3 &&
        ty = arithConvertTypes (ty2, ty3) then
       Some (exprTypeValue ty)
     else if embed? struct ty2 && embed? struct ty3 then
       {check (ty2 = ty3);
        check (ty = ty2);
        Some (exprTypeValue ty)}
     else if embed? pointer ty2 && embed? pointer ty3 then
       if compatibleTypes? (ty2, ty3) then
         {check (ty = compositeType (ty2, ty3));
          Some (exprTypeValue ty)}
       else if nullPointerConst? expr2 then
         {check (ty = ty3);
          Some (exprTypeValue ty)}
       else if nullPointerConst? expr3 then
         {check (ty = ty2);
          Some (exprTypeValue ty)}
       else if ty2 = pointer void || ty3 = pointer void then
         {check (ty = pointer void);
          Some (exprTypeValue ty)}
       else
         None
     else
       None}
  | member (expr, mem) ->
    {ety <- checkExpression (symtab, expr);
     tag <- checkStructType ety.typE;
     members <- symtab.structures tag;
     ty <- members mem;
     Some {typE = ty, object = ety.object}}
  | memberp (expr, mem) ->
    {ety <- checkExpression (symtab, expr);
     ty <- checkPointerType ety.typE;
     tag <- checkStructType ty;
     members <- symtab.structures tag;
     ty' <- members mem;
     Some {typE = ty', object = true}}
  | subscript (expr, expr') ->
    {ety <- checkExpression (symtab, expr);
     ety' <- checkExpression (symtab, expr');
     ty <- checkPointerOrArrayType ety.typE;
     check (integerType? ety'.typE);
     Some (exprTypeObject ty)}
  | nullconst ->
    Some (exprTypeValue (pointer void))

(* It is useful, for later use, to lift op 'checkExpression' to a list of
expressions. *)

op checkExpressions
   (symtab:SymbolTable, exprs:List Expression) : Option (List ExpressionType) =
  case exprs of
  | [] -> Some []
  | expr::exprs ->
    {ty <- checkExpression (symtab, expr);
     tys <- checkExpressions (symtab, exprs);
     Some (ty :: tys)}


%subsubsection (* Type names *)

(* A type name must denote a valid type. If the type name is a typedef name, a
type definition with that name must be in scope [ISO 6.7.8]. Furthermore, the
tag of a (reference to a) structure type must be the same as some structure
specifier in scope [ISO 6.2.1/2]. The referenced type of a pointer type and the
element type of an array type [ISO 6.2.5/20] must recursively satisfy all the
constraints. An array must have at least one element [ISO 6.2.5/20].
Furthermore, since the element type of an array type must be a complete type
[ISO 6.2.5/20], it cannot be 'void' [ISO 6.2.5/19]. There are no constraints on
the integer types and on the 'void' type, which are built-in.

The following op checks that a type name satisfies all the needed constraints.
If it does, the type denoted by the type name is returned. *)

op checkTypeName (symtab:SymbolTable, tyn:TypeName) : Option Type =
  case tyn of
  | struct tag ->
    {check (tag in? domain symtab.structures);
     Some (struct tag)}
  | pointer tyn ->
    {ty <- checkTypeName (symtab, tyn);
     Some (pointer ty)}
  | array (tyn, n) ->
    {ty <- checkTypeName (symtab, tyn);
     check (ty ~= void);
     check (n > 0);
     Some (array (ty, n))}
  | typedef id ->
    symtab.typedefs id
  |  char  -> Some  char
  | uchar  -> Some uchar
  | schar  -> Some schar
  | ushort -> Some ushort
  | sshort -> Some sshort
  | uint   -> Some uint
  | sint   -> Some sint
  | ulong  -> Some ulong
  | slong  -> Some slong
  | ullong -> Some ullong
  | sllong -> Some sllong
  | void   -> Some void


%subsubsection (* Declarations *)

(* The following op checks constraints on object declarations w.r.t. a symbol
table. Upon successful checking, the op extends the symbol table with the newly
declared object, which is always added to the last (i.e. innermost) scope. If
the list consists of exactly one element, we are processing a file-scope
declaration. If the list has more than one element, we are processing a
block-scope declaration. If the list has no elements, checking fails, but this
situation never occurs when this op is used by the ops defined later.

The object declarations in a program in our C subset have file or block scope
[ISO 6.2.1/4].

Since file-scope object declarations have no explicit initializer in our C
subset, they constitute tentative definitions [ISO 6.9.2/2], which are
equivalent to a definition with initializer equal to 0. Even though multiple
declarations of the same identifier are allowed, for simplicity we require
unique file-scope object declarations in our C subset.

Different block-scope object declarations in the same scope must have different
names [ISO 6.2.1/2]. Since objects and structure tags have different name spaces
[ISO 6.2.3], there are no constraints between identifiers used for objects and
identifiers used for structure tags. However, since typedef names, function
names, and objects live in the same name space of ordinary identifiers [ISO
6.2.3], names of objects declared with file-scope must differ from all the
typedef and function names already present in the symbol table. However, an
object declared in an inner block may well hide a homonymous object declared in
an outer block or a typedef name or a function name [ISO 6.2.1/4]. Type
definitions and functions are always declared with file scope in our C subset,
so we require that the declared object has a name that differs from all typedefs
and functions only when the object is declared with file scope, which happens
when the symbol table for objects consists of exactly one scope.

The type of each variable cannot be an incomplete type [ISO 6.9.2/3], and so it
cannot be void [ISO 6.2.5/19]. In addition, the type must satisfy the general
constraints on types. *)

op checkObjectDeclaration
   (symtab:SymbolTable, odecl:ObjectDeclaration) : Option SymbolTable =
  let tyn = odecl.typE in
  let objn = odecl.name in
  {ty <- checkTypeName (symtab, tyn);
   check (ty ~= void);
   scopes <- Some symtab.objects;
   check (scopes ~= []);
   innermost <- Some (last scopes);
   check (objn nin? domain innermost);
   check (length scopes = 1 => objn nin? domain symtab.typedefs);
   check (length scopes = 1 => objn nin? domain symtab.functions);
   Some (symtab << {objects = (butLast scopes ++ [update innermost objn ty])})}

(* Each structure defines a name space for its members [ISO 6.2.3], which have
file scope in our C subset [ISO 6.2.1/4]. Thus, the members of a structure
specifier must have distinct names [ISO 6.2.1/2]. Furthermore, member types
cannot be incomplete [ISO 6.7.2.1/3], and so cannot be void [ISO 6.2.5/19] --
the allowed exception for the last member to have an incomplete array type [ISO
6.7.2.1/2] does not apply to our C subset, which does not have incomplete
arrays.

We check the above constraints on the member declarations of a structure
specifier by constructing, at the same time, a value of type 'TypedMembers'
introduced earlier. The checking is done w.r.t. a symbol table that includes all
the structure specifiers that precede the member declarations. *)

op checkMemberDeclarations
   (symtab:SymbolTable, decls:List MemberDeclaration) : Option TypedMembers =
  case decls of
  | [] -> Some empty
  | decl::decls ->
    let tyn = decl.typE in
    let mem = decl.name in
    {members <- checkMemberDeclarations (symtab, decls);
     ty <- checkTypeName (symtab, tyn);
     check (ty ~= void);
     check (mem nin? domain members);
     Some (update members mem ty)}

(* The tags of structures form a name space [ISO 6.2.3] in our C subset, which
has no unions or enumerations. The structure specifiers in our C subset have
file scope [ISO 6.2.1/4]. Thus, the structure specifiers must have different
tags [ISO 6.2.1/2]. Their members must satisfy the constraints formalized just
above, and there must be at least one member in each structure specifier [ISO
6.7.2.1/1].

We check these constraints w.r.t. a symbol table. Upon successful checking, the
symbol table is extended with the new structure specifier. We initialize the
typed members with no members, then process the members via op
checkMemberDeclarations, which returns all typed members. We check that there is
at least one member by checking the non-emptiness of the typed members.

Even though the scope of a structure tag starts immediately after the
introduction of the tag (before the member declarations) [ISO 6.2.1/7], in our C
subset we disallow recursive references to structure tags. We achieve that by
having the scope of a structure tag starts after the entire structure
specifier. *)

op checkStructSpecifier
   (symtab:SymbolTable, sspec:StructSpecifier) : Option SymbolTable =
  let tag = sspec.tag in
  {check (tag nin? domain symtab.structures);
   members <- checkMemberDeclarations (symtab, sspec.members);
   check (members ~= empty);
   Some (symtab << {structures = update symtab.structures tag members})}

(* The type definitions in a program in our C subset have file scope [ISO
6.2.1/4]. According to [ISO 6.7/3], two type definitions for the same name may
be present (with certain constraints), but in our C subset we disallow that.

Since typedef names and structure tags have different name spaces [ISO 6.2.3],
there are no constraints between typedef names and structure tags. However,
since typedef names and objects live in the same name space of ordinary
identifiers [ISO 6.2.3], typedef names must differ from all the object names
already present in the symbol table. The following op is always used, by the ops
defined later, when the objects component of the symbol table contains exactly
one element, i.e. when processing file-scope declarations. For completeness in
the definition of the following op, however, we check the absence of the typedef
name from all the elements of the list (if any).

The type assigned to a typedef name must, of course, satisfy all the needed
constraints on types. *)

op checkTypeDefinition
   (symtab:SymbolTable, tdef:TypeDefinition) : Option SymbolTable =
  let tyn = tdef.typE in
  let tdn = tdef.name in
  {ty <- checkTypeName (symtab, tyn);
   check (tdn nin? domain symtab.typedefs);
   check (fa(scope) scope in? symtab.objects => tdn nin? domain scope);
   Some (symtab << {typedefs = update symtab.typedefs tdn ty})}

(* We use the ops just defined to check the various kinds of declarations, at
the same time extending the symbol table. *)

op checkDeclaration
   (symtab:SymbolTable, decl:Declaration) : Option SymbolTable =
  case decl of
  | struct  sspec -> checkStructSpecifier   (symtab, sspec)
  | object  odecl -> checkObjectDeclaration (symtab, odecl)
  | typedef tdef  -> checkTypeDefinition    (symtab, tdef)


%subsubsection (* Statements *)

(* Statements are normally not regarded as having compile-time types like
expressions. However, we can regard statements as "yielding values" based on the
values they return via 'return' statements. Correspondingly, we can assign
compile-time types to statements based on the compile-time types of the
expressions of the 'return' statements; we use the 'void' type for a 'return'
statement without an expression.

The following Specware type captures the "elementary" compile-time types for
statements (as defined shortly, statement types are defined as sets of these
elements). A 'return' statement is assigned the compile-time type of its
expression, or 'void' if it has no expression. The special 'next' compile-time
"type" is assigned to statements like assignments, which do not return but
instead transfer control to the next statement. *)

type StatementTypeElement = | next | return Type

(* Since a statement may contain multiple 'return' statements that are executed
under different circumstances (e.g. an 'if' statement), in general a statement
is assigned a (finite) set of the elementary types defined just above. We regard
these sets as compile-time types for statements. *)

type StatementType = FiniteSet StatementTypeElement

(* The following ops formalize the compile-time constraints on statements. The
Specware value 'None' indicates a violation of some constraints. Otherwise, a
statement type as defined just above is returned.

The left operand of an assignment must denote an object [ISO 6.5.16/2,
6.5.16/3]. The left and right operands must be (i) two arithmetic operands, or
(ii) two compatible structures, or (iii) two pointers to compatible types, or
(iv) a pointer to a non-void type and a pointer to void, or (v) a pointer (left)
and a null pointer constant (right) [ISO 6.5.16.1/1]. Our C subset has no notion
of atomic, qualified, and unqualified types. The case of a left '_Bool' operand
does not apply to our C subset. Since, as explained earlier, the null pointer
constant has type 'void*', case (v) is covered by case (iv). As explained above,
the compile-time type of an assignment is 'next'. According to [6.3.2.1/3], an
array can be used as an operand, converted to a pointer to the initial element
of the array. Since the left operand of an assignment must denote an object, but
a pointer is a value (so it does not, directly, denote an object), it follows
that an array cannot be the left operand of an assignment. However, an array can
be the right operand of an assignment. We encapsulate all the checks for
assignability between types into a predicate.

In a function call, the called function must be in the symbol table. The
argument expressions must be assignable to the function's parameters [ISO
6.5.2.2/4]. If the function returns 'void', there cannot be any left operand to
assign the result of the call to. If a left operand is present, the same check
as assignments apply, namely the left operand must denote an object and the
function's return type must be assignable to the type of the left operand.

The test expression of an 'if' statement must have scalar type [ISO 6.8.4.1/1].
Since execution can take either branch, the compile-time type of an 'if'
statement is the union of the compile-time types of its branches. Even though,
according to [ISO 6.3.2.1/3], an array could be used as test (because it is
converted to a pointer), in our C subset we impose a more disciplined use of
arrays and so we do not automatically convert them to pointers.

As explained earlier, a 'return' statement has the compile-time type of its
expression, or 'void' if it has no expression.

The controlling expression of a 'while' or 'do' or 'for' statement must have
scalar type [ISO 6.8.5/2]. The compile-time type of a 'while' or 'do' or 'for'
statement is the compile-time type of the loop body.

Because of our treatment of assignments and function calls as statements, as
explained when the abstract syntax of 'for' loops is defined, we use statements
as the first and third (optional) expressions of a 'for' statement. We restrict
these two statements to be assignments or function calls, which is consistent
with the fact that [ISO 6.8.5] uses expressions, which are executed as
expression statement.

When checking a block, we extend the list of object maps in the symbol table
with an empty map, corresponding to the new block scope.

Like an assignment, an empty block has the 'next' compile-time type.

For a non-empty block, we take the union of the compile-time types of the
statements of the block, taking care of removing all the 'next' types except the
last one (if any). The removal is necessary because otherwise, for example, the
compile-time type of a block 'B' consisting of an assignment followed by a
'return' statement would contain 'next', even though this block 'B' always
returns a value.

A block may include object declarations, which extend the innermost scope of the
symbol table. For this reason, the op to check a block item returns a symbol
table besides a statement type. If the block item is a statement, the output
symbol table is the same as the input one. An object declaration has the 'next'
compile-time type, because it does not return any value. *)

op assignableTypes? (left:Type, right:Type) : Bool =
  arithmeticType? left && arithmeticType? right
  ||
  embed? struct left && embed? struct right && compatibleTypes? (left, right)
  ||
  embed? pointer left &&
  embed? pointer right &&
  (compatibleTypes? (left, right) ||
   left  = pointer void ||
   right = pointer void)
  ||
  (ex (ty:Type, n:Nat)
     right = array (ty, n) &&
     compatibleTypes? (left, pointer ty)) % turn array to pointer

op checkStatement (symtab:SymbolTable, stmt:Statement) : Option StatementType =
  case stmt of
  | assign (expr, expr') ->
    {ety <- checkExpression (symtab, expr);
     ety' <- checkExpression (symtab, expr');
     check ety.object;
     ty <- Some ety.typE;
     ty' <- Some ety'.typE;
     check (assignableTypes? (ty, ty'));
     Some (single next)}
  | call (expr?, fun, exprs) ->
    {(rety, tparams) <- symtab.functions fun;
     etys <- checkExpressions (symtab, exprs);
     check (length etys = length tparams);
     check (fa(i:Nat) i < length etys =>
              assignableTypes? ((tparams @ i).typE, (etys @ i).typE));
     check (rety = void => expr? = None);
     case expr? of
     | Some expr ->
       {ety <- checkExpression (symtab, expr);
        check ety.object;
        check (assignableTypes? (ety.typE, rety));
        Some (single next)}
     | None -> Some (single next)}
  | iF (expr, thenBranch, Some elseBranch) ->
    {ety <- checkExpression (symtab, expr);
     sty <- checkStatement (symtab, thenBranch);
     sty' <- checkStatement (symtab, elseBranch);
     check (scalarType? ety.typE);
     Some (sty \/ sty')}
  | iF (expr, thenBranch, None) ->
    checkStatement (symtab, (iF (expr, thenBranch, Some (block []))))
  | return (Some expr) ->
    {ety <- checkExpression (symtab, expr);
     Some (single (return ety.typE))}
  | return None ->
    Some (single (return void))
  | while (expr, body) ->
    {ety <- checkExpression (symtab, expr);
     check (scalarType? ety.typE);
     checkStatement (symtab, body)}
  | do (body, expr) ->
    {ety <- checkExpression (symtab, expr);
     check (scalarType? ety.typE);
     checkStatement (symtab, body)}
  | for (first?, expr?, third?, body) ->
    {case first? of
     | Some first ->
       {check (embed? assign first || embed? call first);
        checkStatement (symtab, first)}
     | None ->
       Some (single next);
     case expr? of
     | Some expr ->
       {ety <- checkExpression (symtab, expr);
        check (scalarType? ety.typE)}
     | None ->
       check true;
     case third? of
     | Some third ->
       {check (embed? assign third || embed? call third);
        checkStatement (symtab, third)}
     | None ->
       Some (single next);
     checkStatement (symtab, body)}
  | block items ->
    let symtab' = symtab << {objects = symtab.objects ++ [empty]} in
    checkBlockItems (symtab', items)

op checkBlockItems
   (symtab:SymbolTable, items:List BlockItem) : Option StatementType =
  case items of
  | [] -> Some (single next)
  | item::items ->
    {(sty, symtab') <- checkBlockItem (symtab, item);
     if empty? items then Some sty
     else
       {sty' <- checkBlockItems (symtab', items);
        Some (sty - next \/ sty')}} 

op checkBlockItem
   (symtab:SymbolTable, item:BlockItem) : Option (StatementType * SymbolTable) =
  case item of
  | declaration odecl ->
    {symtab' <- checkObjectDeclaration (symtab, odecl);
     Some (single next, symtab')}
  | statement stmt ->
    {sty <- checkStatement (symtab, stmt);
     Some (sty, symtab)}


%subsubsection (* Function definitions *)

(* In our C subset, a function can access all the structures, objects, and type
definitions of the program, as well as its parameters [ISO 6.2.1/2, 6.2.1/4].
Given a symbol table that consists of the externally declared structures,
objects, and types that precede the function definition we extend the symbol
table with a new block scope with the function's parameter, and then we check
the constraints on the body of the function. Even though a function's name is
visible inside the function's body because the body follows the function
declaration, in our C subset we do not add the function's name to the symbol
table until after the whole body has been processed: this prevents direct
recursive calls. Note also that since our C subset only allows functions to be
declared as part of their definition, we cannot have indirect recursive calls
either.

The return type of a function cannot be an array [ISO 6.7.6.3/1].

The identifiers of objects, typedef names, and functions belong to the name
space of ordinary identifiers [ISO 6.2.3/1]. Different entities designated by
the same identifier must have different scopes or name spaces [ISO 6.2.1/2].
Since external object declarations, type definitions, and function definitions
have the same (file) scope and the same name space, the name of each function of
our C program must be distinct from all the externally declared objects and all
the externally defined types. When op 'checkFunctionDefinition' is used by op
'checkProgram' defined later, the objects component of the symbol table always
contains exactly one element. However, for completeness, the following op checks
that the function name does not occur in any element of the list (if any).

The type names of the function's parameters must satisfy the usual constraints
and cannot be 'void' because they must be all complete [ISO 6.7.6.3/4]. In
addition, the names of the parameters must be all distinct, because they belong
to the same scope and name space [ISO 6.2.1/2]. Since parameters with array
types are adjusted to have pointer types [ISO 6.7.6.3/7], in our C subset we
require function parameters to not have array types, i.e. to be already
pointers, for simplicity.

The body of a function must be a compound statement [ISO 6.9.1].

The return value of a function is converted, as if by assignment, to the return
type of the function [ISO 6.8.6.4/3]. Thus, we check (each type in) the
statement type of the function's body against the return type of the function,
using the predicate 'assignableTypes?' defined earlier. We extend the predicate
to handle the 'void' type: 'void', and only 'void', is assignable to 'void'.
Note that if the function has return type 'void', the statement type of the body
must only include 'void', which implies that no 'return' statement with an
expression can occur in the body [ISO 6.8.6.4/1]; and conversely if the function
has a non-'void' return type, the statement type of the body must not include
'void', which implies that no 'return' statement without an expression can occur
in the body [ISO 6.8.6.4/1]. If execution falls off the end of the function
(i.e. without executing a 'return' statement), the return value is undefined
[ISO 6.9.1/12]. For well-behaved C programs, this is only acceptable if the
function returns 'void'. Thus, if the return type is not 'void', we require that
the execution of the function's body cannot fall off the end of the function,
i.e. that the statement type of the body does not include 'next'.

If successful, op 'checkFunctionDefinition' extends the symbol table with
information about the function. *)

op checkParameterDeclaration
   (symtab:SymbolTable, pdecl:ParameterDeclaration) : Option TypedParameter =
  {ty <- checkTypeName (symtab, pdecl.typE);
   check (ty ~= void);
   Some {typE = ty, name = pdecl.name}}

op checkParameterList
   (symtab:SymbolTable, plist:ParameterList) : Option TypedParameters =
  case plist of
  | [] -> Some []
  | pdecl::pdecls ->
    {tparam <- checkParameterDeclaration (symtab, pdecl);
     tparams <- checkParameterList (symtab, pdecls);
     check (tparam.name nin? map (project name) tparams);
     Some (tparam :: tparams)}

op assignableReturnTypes? (left:Type, right:Type) : Bool =
  assignableTypes? (left, right) ||
  left = void && right = void

op checkFunctionDefinition
   (symtab:SymbolTable, fun:FunctionDefinition) : Option SymbolTable =
  {rety <- checkTypeName (symtab, fun.return);
   check (~ (embed? array rety));
   check (fa(i:Nat) i < length fun.parameters =>
            ~ (embed? array (fun.parameters @ i).typE));
   check (fa(scope) scope in? symtab.objects => fun.name nin? domain scope);
   check (fun.name nin? domain symtab.typedefs);
   check (fun.name nin? domain symtab.functions);
   tparams <- checkParameterList (symtab, fun.parameters);
   let pnames = map (project name) tparams in
   let ptys = map (project typE) tparams in
   let newscope = fromAssocList (zip (pnames, ptys)) in
   let symtab' = symtab << {objects = symtab.objects ++ [newscope]} in
   case fun.body of
   | block items ->
     {sty <- checkBlockItems (symtab', items);
      check (rety ~= void => next nin? sty);
      check (fa(ty) return ty in? sty => assignableReturnTypes? (rety, ty));
      Some (symtab
            << {functions = update symtab.functions fun.name (rety, tparams)})}
   | _ -> None}


%subsubsection (* Translation units *)

(* We check an external declaration as follows. *)

op checkExternalDeclaration
   (symtab:SymbolTable, xdecl:ExternalDeclaration) : Option SymbolTable =
  case xdecl of
  | function fdef -> checkFunctionDefinition (symtab, fdef)
  | declaration decl -> checkDeclaration (symtab, decl)

(* We check a translation unit by checking its external declarations in
order. *)

op checkTranslationUnit
   (symtab:SymbolTable, tunit:TranslationUnit) : Option SymbolTable =
  case tunit of
  | [] -> Some symtab
  | xdecl::xdecls ->
    {symtab' <- checkExternalDeclaration (symtab, xdecl);
     checkTranslationUnit (symtab', xdecls)}


%subsubsection (* Programs *)

(* We check a program by checking its translation unit, starting with the empty
symbol table. The empty symbol table consists of one scope with no objects, no
type definitions, and no structures. If all the constraints are satisfied, the
following op returns the symbol table that corresponds to the program's external
declarations. *)

op emptySymbolTable : SymbolTable =
  {typedefs   = empty,
   structures = empty,
   objects    = [empty],
   functions  = empty}

op checkProgram (prg:Program) : Option SymbolTable =
  checkTranslationUnit (emptySymbolTable, prg)


%section (* Semantics *)

(* Besides syntax and syntactic constraints, [ISO] describes the semantics (i.e.
execution) of C programs. *)


%subsection (* Outcomes *)

(* [ISO] prescribes the outcomes of certain computations, while leaving the
outcomes of other computations undefined [ISO 3.4.3] or implementation-defined
[ISO 3.4.1]. In our formalization, we collectively regard undefined and
implementation-defined outcomes as non-standard -- i.e. not prescribed by the
standard.

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

In the presence of loops, a computation may fail to terminate. We model this via
a special non-temination result that is returned by Specware functions that
model the execution of non-terminating computations.

Thus, a computation can have four possible outcomes in our formalization: normal
("OK"), non-standard, error, and non-termination. The exact nature of a normal
outcome depends on the computation. So, we introduce a type of outcomes that is
parameterized over the type of the normal outcomes. We use the short name 'OC'
(for 'OutCome') so that it is not too invasive when used for the result types of
the Specware ops that formalize execution. *)

type OC a =
  | ok a
  | nonstd
  | error
  | nonterm

(* Whenever a subcomputation yields a non-standard or error or non-termination
outcome, the outer computation does too. In other words, non-standard and error
and non-termination outcomes propagate. This is the structure of an exception
monad, whose 'bind' operator is defined as follows. The use of the name
'monadBind' enables the use of Specware's monadic syntax. *)

op [a,b] monadBind (m:OC a, f: a -> OC b) : OC b =
  case m of
  | ok x    -> f x
  | nonstd  -> nonstd
  | error   -> error
  | nonterm -> nonterm

(* It is also useful to define monadic ops that return 'error' or 'nonstd' or
'nonterm' if some condition is true. *)

op errorIf (condition:Bool) : OC () =
  if condition then error else ok ()

op nonstdIf (condition:Bool) : OC () =
  if condition then nonstd else ok ()

op nontermIf (condition:Bool) : OC () =
  if condition then nonterm else ok ()


%subsection (* Object designators *)

(* Each object declaration in a program in our C subset introduces an object
[ISO 3.15]. When such an object is a structure, its members are subobjects of
the object, which can be independently written to via a suitable lvalue [ISO
6.3.2.1/1]. Similarly, when the object is an array, its elements are subobjects
and they can be written independently via a suitable lvalue. This recursively
applies to members and elements of structure members and array elements.

The "top-level" objects are the ones declared with a name. Their structure
members and array elements are subobjects of those top-level objects. The
top-level objects may be declared with file scope (i.e. outside any block) or
with block scope (i.e. inside some block). Since a declaration in an inner block
may hide a homonymous outer declaration, a name alone does not suffice to
identify a top-level object at run time. However, a name alone suffices in each
scope. So, we can identify a top-level object via (an indication of) a scope
plus a name in that scope. As defined later in type 'Storage', at each point in
time there is a list of lists of active block scopes, plus the outer file scope.
Thus, we also introduce a notion of scope designator that designates either the
file scope, or a block scope. A block scope is designated by two numbers, one
that designates an element of the outer list, and one that designates an element
of the inner list (the numbers are 0-based indices into the lists).

A program in our formalized C subset is a self-contained translation unit, in
the sense that it cannot reference entities in other translation units (cf. op
'checkProgram', which starts with an empty symbol table). However, other
translation units may call functions defined by our formalized translation unit.
If these functions have parameters of pointer type, the corresponding pointer
arguments when the functions are called may well be pointers to (sub)objects
declared in (or dynamically allocated by) those other translation units. Our
formalized translation unit can operate on those "outside objects", so our model
of storage (type 'Storage', defined later) includes a set of such outside
objects. In our model, we use an infinite type of IDs to identify outside
objects. This type is defined to be isomorphic to the natural numbers for
simplicity, but the natural numbers are just IDs, not meant to be memory
addresses.

Given a top-level object designated by a scope designation plus a name, or an
outside object designated by an ID, subobjects are designated by adding member
names (for structures) and element indices (for arrays).

Thus, we introduce the following notion of object designator as an unambiguous
way to denote a (sub)object. *)

type ScopeDesignator =
  | file
  | block Nat * Nat

type OutsideID = | outsideID Nat

type ObjectDesignator =
  | top       ScopeDesignator * Identifier
  | outside   OutsideID
  | member    ObjectDesignator * Identifier
  | subscript ObjectDesignator * Nat


%subsection (* Values *)

(* The sizes of 'short's, 'int's, 'long's, and 'long long's are captured by the
ops 'short_bits', 'int_bits', 'long_bits', and 'llong_bits' introduced and
explained earlier. We introduce Specware types for words (i.e. bit lists) of the
corresponding sizes. These words are interpreted in big endian format in our
model. Since our C subset is type-safe, it does not actually matter whether the
words are interpreted in big or little endian format, so long as they are
treated consistently thoughout the model. *)

type    ShortWord = (Bits | ofLength? short_bits)
type      IntWord = (Bits | ofLength?   int_bits)
type     LongWord = (Bits | ofLength?  long_bits)
type LongLongWord = (Bits | ofLength? llong_bits)

(* The wording in [ISO 3.19] indicates that, conceptually, a value "includes" a
type. Typical implementations only store "raw" bits inside objects [ISO 3.15],
without explicit type information, but use the declared type of the object to
interpret the object's content [ISO 6.5/6].

In our formal model of values, it is convenient to include type information. The
values in our C subset are those of the integer types, of structure types, of
pointer types, and of array types; those are all the non-'void' types in our C
subset.

Based on our definition of op CHAR_BIT, as explained earlier, char values in our
formalization consist of 8 bits, like type 'Byte' in the Specware library.

A structure (value) consists of a value assigned to each member, so we use a
finite map from identifiers (denoting members) to values. We also include the
tag of the structure, so that we have complete type information.

A pointer (value) consists of an object designator. In our C subset, we only
allow pointers that reference well-defined objects, and not arbitrary addresses
in memory. Our C subset is type-safe. We also include, as part of our model of a
pointer, the type of the object referenced by the pointer. There is also a
separate null pointer [ISO 6.3.2.3/3] value for each type [ISO 6.3.2.3/4].

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
  |  char               Byte
  | uchar               Byte
  | schar               Byte
  | ushort         ShortWord
  | sshort         ShortWord
  | uint             IntWord
  | sint             IntWord
  | ulong           LongWord
  | slong           LongWord
  | ullong      LongLongWord
  | sllong      LongLongWord
  | struct      Identifier * FiniteMap (Identifier, Value)
  | pointer     Type * ObjectDesignator
  | array       Type * List Value
  | nullpointer Type
  | undefined   Type

(* There is an obvious mapping from values to types. Note that this includes
undefined values, because at run time they are still C values -- we just do not
know what they are exactly. *)

op typeOfValue (val:Value) : Type =
  case val of
  |  char  _         ->  char
  | uchar  _         -> uchar
  | schar  _         -> schar
  | ushort _         -> ushort
  | sshort _         -> sshort
  | uint   _         -> uint
  | sint   _         -> sint
  | ulong  _         -> ulong
  | slong  _         -> slong
  | ullong _         -> ullong
  | sllong _         -> sllong
  | struct (tag, _)  -> struct tag
  | pointer (ty, _)  -> pointer ty
  | array (ty, vals) -> array (ty, length vals)
  | nullpointer ty   -> pointer ty
  | undefined ty     -> ty

(* We lift some of the predicates that classify types to predicates that
classify values. Note that undefined values of the correct types are
included. *)

op integerValue? (val:Value) : Bool =
  integerType? (typeOfValue val)

op arithmeticValue? (val:Value) : Bool =
  arithmeticType? (typeOfValue val)

op pointerValue? (val:Value) : Bool =
  embed? pointer (typeOfValue val)

op structValue? (val:Value) : Bool =
  embed? struct (typeOfValue val)

op arrayValue? (val:Value) : Bool =
  embed? array (typeOfValue val)

op scalarValue? (val:Value) : Bool =
  scalarType? (typeOfValue val)

(* We can remove the constructors of integer values, and retrieve the bits that
comprise them. It is an error to do that on non-integer values. If the value is
an undefined integer, a non-standard outcome is produced. *)

op bitsOfIntegerValue (val:Value) : OC Bits =
  case val of
  |  char  x -> ok x
  | uchar  x -> ok x
  | schar  x -> ok x
  | ushort x -> ok x
  | sshort x -> ok x
  | uint   x -> ok x
  | sint   x -> ok x
  | ulong  x -> ok x
  | slong  x -> ok x
  | ullong x -> ok x
  | sllong x -> ok x
  | undefined ty -> if integerType? ty then nonstd else error
  | _ -> error

(* Given an integer type and bits of the type's size, we can create a value with
those bits and that type. *)

op valueOfBits
   (bits:Bits, ty:Type | integerType? ty && length bits = typeBits ty) : Value =
  the(val:Value) typeOfValue val = ty && bitsOfIntegerValue val = ok bits

(* Each integer value encodes a mathematical integer. The outcome is an error if
the value is not an integer, and non-standard if the value is undefined. *)

op mathIntOfValue (val:Value) : OC Int =
  {bits <- bitsOfIntegerValue val;
   if unsignedIntegerType? (typeOfValue val) ||
      plainCharsAreUnsigned && typeOfValue val = char then
     ok (toNat bits)
   else
     ok (toInt bits)}

(* A mathematical integer in the range of an integer type can be represented in
that type. *)

op valueOfMathInt
   (i:Int, ty:Type | integerType? ty && i in? rangeOfIntegerType ty) : Value =
  the(val:Value) typeOfValue val = ty && mathIntOfValue val = ok i

(* Each scalar type has a "zero" value. For integers, it is the representation
of the mathematical 0. For pointers, it is the null pointer. *)

op zeroOfScalarType (ty:Type | scalarType? ty) : Value =
  if integerType? ty then valueOfMathInt (0, ty) else nullpointer ty

(* The zero of an integer type consists of all 0 bits. Note that, because of our
environmental choices about the absence of padding bits and the two's complement
representation of signed integers, the all-0-bits pattern is the only
representation of the integer 0 values. In particular, two's complement do not
have positive and negative zeros. *)

theorem zero_of_integer_type_is_all_zeros is
  fa(ty:Type) integerType? ty =>
              bitsOfIntegerValue (zeroOfScalarType ty) =
                ok (repeat B0 (typeBits ty))

(* The following predicate tests whether a scalar value is 0 or not. The result
is an error if the value is not scalar, and non-standard if it is undefined. *)

op zeroScalarValue? (val:Value) : OC Bool =
  if scalarValue? val then
    if embed? undefined val then nonstd
    else ok (ex(ty:Type) scalarType? ty && val = zeroOfScalarType ty)
  else
    error

(* It is useful to introduce Specware constants for the signed ints 0 and 1,
because they are returned by some operators, as formalized later. *)

op int0 : Value = valueOfMathInt (0, sint)

op int1 : Value = valueOfMathInt (1, sint)


%subsection (* States *)

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

(* As mentioned in the comments for type 'ObjectDesignator', our model of
storage includes outside objects, which are identified by the IDs introduced
earlier. *)

type OutsideStorage = FiniteMap (OutsideID, Value)

(* As mentioned in the comments for type 'ObjectDesignator', at each point in
time the file scope is active, along with a list of lists of block scopes. The
list of lists arises as follows: the outer list corresponds to the function call
stack, i.e. there is an element for each nested function call; the inner list of
each element of the outer list corresponds to the nested block scopes inside
that function's body. Note that the nesting of scopes only occurs within each
element of the outer list (i.e. call stack), but not within the outer list
itself, because block scopes inside different functions are unrelated.

The objects declared with file scope have static storage duration [ISO 6.2.4/3],
while the objects declared with block scope have automatic storage duration [ISO
6.2.4/5].

We model the static storage as a named storage, and the automatic storage as a
list of lists of named storages. We also have an outside storage for outside
objects. *)

type Storage =
  {static    :            NamedStorage,
   automatic : List (List NamedStorage),
   outside   :          OutsideStorage}

(* Besides storage, it is convenient to include in the state of a C program in
our subset also a symbol table of type definitions, a symbol table of structure
types, and information about functions (consisting of return type, typed
parameters, and body). These are used to execute declarations at run time, as
formalized later. *)

type FunctionInfo =
  {return     : Type,
   parameters : TypedParameters,
   body       : Statement}

type FunctionsInfo = FiniteMap (Identifier, FunctionInfo)

type State =
  {storage    : Storage,
   typedefs   : TypedefTable,
   structures : StructTable,
   functions  : FunctionsInfo}

(* The following ops provide convenience in updating parts of the state. Using
typical programming language terminology, we call each element of the outer list
(of named storages that form the automatic storage) a 'frame' (this term is not
used in [ISO]). *)

op updateStaticStorage (state:State, sstore:NamedStorage) : State =
  state << {storage = state.storage << {static = sstore}}

op updateStaticObject (state:State, name:Identifier, val:Value) : State =
  updateStaticStorage (state, update state.storage.static name val)

op updateAutomaticStorage
   (state:State, astore:List (List NamedStorage)) : State =
  state << {storage = state.storage << {automatic = astore}}

op updateAutomaticFrame
   (state:State, f:Nat, frame:List NamedStorage |
    f < length state.storage.automatic) : State =
  let newauto = update (state.storage.automatic, f, frame) in
  updateAutomaticStorage (state, newauto)

op updateAutomaticObjects
   (state:State, f:Nat, o:Nat, objs:NamedStorage |
    f < length state.storage.automatic &&
    o < length (state.storage.automatic @ f)) : State =
  let newframe = update (state.storage.automatic @ f, o, objs) in
  updateAutomaticFrame (state, f, newframe)

op updateAutomaticObject
   (state:State, f:Nat, o:Nat, name:Identifier, val:Value |
    f < length state.storage.automatic &&
    o < length (state.storage.automatic @ f)) : State =
  let newobjs = update (state.storage.automatic @ f @ o) name val in
  updateAutomaticObjects (state, f, o, newobjs)

op updateOutsideStorage (state:State, ostore:OutsideStorage) : State =
  state << {storage = state.storage << {outside = ostore}}

op updateOutsideObject (state:State, id:OutsideID, val:Value) : State =
  updateOutsideStorage (state, update state.storage.outside id val)

(* An object name denotes the object declared with that name in the innermost
block that declares an object with that name. The following op returns the
designator of the innermost scope that declares an object with the argument
name. It is an error if no object with the given name is declared in any scope.

If there is no automatic storage, the object is searched in the static storage,
whose objects have file scope. Otherwise, the object is searched in the topmost
(i.e. last) frame, starting with the innermost block. Objects in other frames
cannot be referenced because they are not in scope.

Note that the recursive call to the following op is made with a storage whose
top frame's innermost scope has been removed, reflecting the search from inner
to outer scope. If the op is called with an empty frame, it means that the
object has not been found in any block scope of the topmost frame, and thus it
is searched in the static storage, achieved by removing the automatic storage
altogether in the recursive call. Since list indices are numbered from 0, we
return the lengths of the lists minus 1 as the indices of a block scope. *)

op scopeOfObject (state:State, name:Identifier) : OC ScopeDesignator =
  let store = state.storage in
  if empty? store.automatic then
    if name in? domain store.static then ok file else error
  else
    let topframe = last store.automatic in
    if empty? topframe then
      scopeOfObject (updateAutomaticStorage (state, []), name)
    else
      if name in? domain (last topframe) then
        ok (block (length store.automatic - 1, length topframe - 1))
      else
        let state' =
            updateAutomaticFrame
              (state, length store.automatic - 1, butLast topframe) in
        scopeOfObject (state', name)

(* The following op returns the complete object designator for a named object,
by pairing the name with the scope designator returned by the op above. It is an
error if the object's scope is not found. *)

op designatorOfObject (state:State, name:Identifier) : OC ObjectDesignator =
  {scope <- scopeOfObject (state, name);
   ok (top (scope, name))}

(* The following ops read and write the value of a top-level object. The object
must exist. When writing, the new value must have the same type as the old
value. *)

op readTopObject
   (state:State, scope:ScopeDesignator, name:Identifier) : OC Value =
  let store = state.storage in
  case scope of
  | file ->
    if name in? domain store.static then
      ok (store.static @ name)
    else
      error
  | block (f, o) ->
    let objs = store.automatic @ f @ o in
    if name in? domain objs then
      ok (objs @ name)
    else
      error

op writeTopObject
   (state:State, scope:ScopeDesignator, name:Identifier, newval:Value)
   : OC State =
  {oldval <- readTopObject (state, scope, name);
   errorIf (typeOfValue oldval ~= typeOfValue newval);
   case scope of
   | file -> ok (updateStaticObject (state, name, newval))
   | block (f, o) -> ok (updateAutomaticObject (state, f, o, name, newval))}

(* The following ops read and write the value of an outside object. The object
must exist. When writing, the new value must have the same type as the old
value. *)

op readOutsideObject (state:State, id:OutsideID) : OC Value =
  let store = state.storage in
  if id in? domain store.outside then
    ok (store.outside @ id)
  else
    error

op writeOutsideObject (state:State, id:OutsideID, newval:Value) : OC State =
  {oldval <- readOutsideObject (state, id);
   errorIf (typeOfValue oldval ~= typeOfValue newval);
   ok (updateOutsideObject (state, id, newval))}

(* The following ops read and write the value of the designated object.

An undefined value of an aggregate type is equivalent to an aggregation of
undefined values. In other words, an undefined structure is equivalent to a
structure of undefined values (one for each member), and an undefined array is
equivalent to an array of undefined values (one for each element). This applies
recursively to members and elements of members and elements. This equivalence is
important when reading and writing values via the following ops. Suppose that a
local variable of a structure type is declared; as formalizer later, the
undefined value of that structure is initially assigned to the local variable.
Suppose that we read a member of that structure: we need to look up the
structure type in the state, find the member's type, and return the undefined
value of the member type. Similarly, for an undefined array, we need to return
the undefined value of the array element type. When writing a member into an
undefined structure, we need to replace the undefined structure with a structure
of undefined values (save for the value that we are writing into the member).
Similarly, when writing an element into an undefined array, we need to replace
the undefined array with an array of undefined values (save for the value that
we are writing into the element).

To write a new value into a top-level or outside object, we just write the value
into the object using op writeTopObject or writeOutsideObject above. To assign a
new value to a member of a structure or an element of an array, we first
retrieve the old value of the structure or array (by reading the value from the
super-object designator) -- not of the member or element that we have to write
into, but of the enclosing structure or array. Then we overwrite the member of
the old structure value, or the element of the old array value, with the new
value for the member or element, obtaining a new value for the enclosing
structure or array. Finally, we recursively assign this new structure or array
value to the super-object designator. The recursion eventually terminates with a
top-level object. *)

op readObject (state:State, obj:ObjectDesignator) : OC Value =
  case obj of
  | top (scope, name) ->
    readTopObject (state, scope, name)
  | outside id ->
    readOutsideObject (state, id)
  | member (obj', mem) ->
    {val' <- readObject (state, obj');
     case val' of
     | struct (_, members) ->
       (case members mem of
       | None -> error
       | Some val -> ok val)
     | undefined (struct tag) ->
       (case state.structures tag of
       | None -> error
       | Some tmembers ->
         (case tmembers mem of
         | None -> error
         | Some ty -> ok (undefined ty)))
     | _ -> error}
  | subscript (obj', i) ->
    {val' <- readObject (state, obj');
     case val' of
     | array (_, elements) ->
       if i < length elements then
         ok (elements @ i)
       else
         error
     | undefined (array (ty, _)) ->
       ok (undefined ty)
     | _ -> error}

op writeObject (state:State, obj:ObjectDesignator, newval:Value) : OC State =
  case obj of
  | top (scope, name) ->
    writeTopObject (state, scope, name, newval)
  | outside id ->
    writeOutsideObject (state, id, newval)
  | member (obj_struct, mem) ->
    {oldval_struct <- readObject (state, obj_struct);
     case oldval_struct of
     | struct (tag, members) ->
       (case members mem of
       | None -> error
       | Some oldval ->
         if typeOfValue oldval = typeOfValue newval then
           let newval_struct = struct (tag, update members mem newval) in
           writeObject (state, obj_struct, newval_struct)
         else
           error)
     | undefined (struct tag) ->
       (case state.structures tag of
       | None -> error
       | Some tmembers ->
         let allundef = fn mem:Identifier ->
             (case tmembers mem of
             | None -> None
             | Some ty -> Some (undefined ty))
         in
         (case tmembers mem of
         | None -> error
         | Some ty ->
           if ty = typeOfValue newval then
             let newval_struct = struct (tag, update allundef mem newval) in
             writeObject (state, obj_struct, newval_struct)
           else
             error))
     | _ -> error}
  | subscript (obj_array, i) ->
    {oldval_array <- readObject (state, obj_array);
     case oldval_array of
     | array (ty, elements) ->
       if i < length elements && ty = typeOfValue newval then
         let newval_array = array (ty, update (elements, i, newval)) in
         writeObject (state, obj_array, newval_array)
       else
         error
     | undefined (array (ty, n)) ->
       if i < n && ty = typeOfValue newval then
         let allundef = List.repeat (undefined ty) n in
         let newval_array = array (ty, update (allundef, i, newval)) in
         writeObject (state, obj_array, newval_array)
       else
         error
     | _ -> error}

(* A symbol table is essentially a compile-time summary/representation of the
run-time state. The following op abstracts a state into a symbol table.

The static storage, which is a map from names to values, is turned into a map
from names to types by applying op 'typeOfValue' to all the values in the map.
Technically, this is done by lifting 'typeOfValue' to operate on optional values
and types (via op 'mapOption') and then composing it with the named storage map,
as encapsulated in op 'objectTableOfNamedStorage' below. The latter is applied
to all the blocks of the topmost frame of the automatic storage, and the result
appended to the map for the static storage. The outside storage does not
contribute to the symbol table.

The function table is created by dropping the bodies from the function
information in the state, using the same 'mapOption' and function composition
technique described above for object tables.

The type definition table and the structure table are just copied from the state
into the symbol table. *)

op objectTableOfNamedStorage
   (store:NamedStorage) : FiniteMap (Identifier, Type) =
  (mapOption typeOfValue) o store

op objectTableOfStorage (store:Storage) : ObjectTable =
  if empty? store.automatic then
    [objectTableOfNamedStorage store.static]
  else
    objectTableOfNamedStorage store.static ::
    map objectTableOfNamedStorage (last store.automatic)

op functionTableOfFunctionsInfo (funsinfo:FunctionsInfo) : FunctionTable =
  (mapOption (fn funinfo:FunctionInfo -> (funinfo.return, funinfo.parameters)))
  o
  funsinfo

op symbolTableOfState (state:State) : SymbolTable =
  {typedefs   = state.typedefs,
   structures = state.structures,
   functions  = functionTableOfFunctionsInfo state.functions,
   objects    = objectTableOfStorage state.storage}

(* The following ops collect all the object designators that occur in values,
named storages, frames, outside storages, storages, and states. *)

op objDesignatorsInValue (val:Value) : FiniteSet ObjectDesignator =
  case val of
  | pointer (_, obj) ->
    single obj
  | array (_, vals) ->
    (fn obj -> (ex(val) val in? vals && obj in? objDesignatorsInValue val))
  | struct (_, members) ->
    (fn obj -> (ex(mem) mem in? domain members &&
                        obj in? objDesignatorsInValue (members @ mem)))
  | _ ->
    empty

op objDesignatorsInNamedStorage
   (store:NamedStorage) : FiniteSet ObjectDesignator =
  fn obj -> (ex(name:Identifier) name in? domain store &&
                                 obj in? objDesignatorsInValue (store @ name))

op objDesignatorsInFrame
   (frame:List NamedStorage) : FiniteSet ObjectDesignator =
  fn obj -> (ex(b:Nat) b < length frame &&
                       obj in? objDesignatorsInNamedStorage (frame @ b))

op objDesignatorsInFrames
   (frames:List (List NamedStorage)) : FiniteSet ObjectDesignator =
  fn obj -> (ex(f:Nat) f < length frames &&
                       obj in? objDesignatorsInFrame (frames @ f))

op objDesignatorsInOutsideStorage
   (store:OutsideStorage) : FiniteSet ObjectDesignator =
  fn obj -> (ex(id:OutsideID) id in? domain store &&
                              obj in? objDesignatorsInValue (store @ id))

op objDesignatorsInStorage (store:Storage) : FiniteSet ObjectDesignator =
  objDesignatorsInNamedStorage   store.static \/
  objDesignatorsInFrames         store.automatic \/
  objDesignatorsInOutsideStorage store.outside

op objDesignatorsInState (state:State) : FiniteSet ObjectDesignator =
  objDesignatorsInStorage state.storage


%subsection (* State invariants *)

(* Not all the states in the state space defined by type 'State' correspond to
states that can actually happen at run time, when a program satisfying the
compile-time constraints is executed. There are certain invariants that are true
of the initial state and that are preserved by execution. We define some of
these invariants.

An important invariant is the absence of circularities in the structure types in
the state. In other words, given a structure type S, no member of S can have a
type that references S, and no member or element of a member S can, and so on
recursively. (As explained in the comments for op 'checkStructSpecifier', our C
subset disallows recursive structure via pointers, unlike [ISO].)

The following op says whether a type references a structure (via a tag). This
happens when the type is the structure type itself, or is a pointer to the
structure, or is an array of those structures. *)

op typeReferencesStruct? (ty:Type, tag:Identifier) : Bool =
  case ty of
  | struct tag' -> tag' = tag
  | array  (ty', _) -> typeReferencesStruct? (ty', tag)
  | pointer ty'     -> typeReferencesStruct? (ty', tag)
  | _ -> false

(* The following op says whether a structure (identified by tag) references
another structure (identifier by tag'). This happens when the first structure is
in the state and the type of at least one of its members directly references the
second structure. *)

op structReferencesStruct?
   (state:State, tag:Identifier, tag':Identifier) : Bool =
  tag in? domain state.structures &&
  (let tmembers = state.structures @ tag in
  (ex(mem) mem in? domain tmembers &&
           typeReferencesStruct? (tmembers @ mem, tag')))

(* A circularity arises when there is a list of two or more structures such that
each one references the next one, and the first and last one in the list
coincide. Negating this condition yields a predicate to test for
non-circularity. *)

op noCircularStructs? (state:State) : Bool =
  ~ (ex (tags:List Identifier)
       length tags >= 2 &&
       (fa(i:Nat) i < length tags - 1 =>
          structReferencesStruct? (state, tags @ i, tags @ (i + 1))) &&
       head tags = last tags)

(* A similar invariant is the absence of circularities in the function call
graph. In other, no function can call itself, directly or indirectly.

The following predicates say whether a statement, block item, or block items
call(s) a function with a given identifier. *)

op statementCallsFunction? (stmt:Statement, fun:Identifier) : Bool =
  case stmt of
  | call (_, fun', _) -> fun' = fun
  | iF (_, thenBranch, elseBranch?) ->
    statementCallsFunction? (thenBranch, fun) ||
    (case elseBranch? of
    | Some elseBranch -> statementCallsFunction? (elseBranch, fun)
    | None -> false)
  | block items -> blockItemsCallFunction? (items, fun)
  | _ -> false

op blockItemsCallFunction? (items:List BlockItem, fun:Identifier) : Bool =
  case items of
  | [] -> false
  | item::items ->
    blockItemCallsFunction? (item, fun) ||
    blockItemsCallFunction? (items, fun)

op blockItemCallsFunction? (item:BlockItem, fun:Identifier) : Bool =
  case item of
  | declaration _ -> false
  | statement stmt -> statementCallsFunction? (stmt, fun)

(* The following predicate says whether a function (with name fun) calls another
function (with name fun'), directly. This happens when the first function is in
the state and its body calls the second function. *)

op functionCallsFunction?
   (state:State, fun:Identifier, fun':Identifier) : Bool =
  fun in? domain state.functions &&
  (let funinfo = state.functions @ fun in
  statementCallsFunction? (funinfo.body, fun'))

(* A circularity arises when there is a list of two or more functions such that
each one references the next one, and the first and last one in the list
coincide. Negating this condition yields a predicate to test for
non-circularity. *)

op noCircularFunctions? (state:State) : Bool =
  ~ (ex (funs:List Identifier)
       length funs >= 2 &&
       (fa(i:Nat) i < length funs - 1 =>
          functionCallsFunction? (state, funs @ i, funs @ (i + 1))) &&
       head funs = last funs)

(* Another important invariant is that the body of each function in the state is
a block whose items satisfy the compile-time constraints for lists of block
items. The symbol table w.r.t. which the constraints are checked, is constructed
from the state, but all the automatic-storage scopes are replaced with one scope
for the function, which contains the functions parameters. Furthermore, the
function's body always return something matching the return type (nothing if
'void'). *)

op functionBodiesOK? (state:State) : Bool =
  fa (name:Identifier, funinfo:FunctionInfo)
    state.functions name = Some funinfo =>
    (let rety = funinfo.return in
     let tparams = funinfo.parameters in
     let pnames = map (project name) tparams in
     let ptys = map (project typE) tparams in
     let funscope = fromAssocList (zip (pnames, ptys)) in
     let symtab = symbolTableOfState state in
     let symtab' = symtab << {objects = [head symtab.objects] ++ [funscope]} in
     case funinfo.body of
     | block items ->
       (case checkBlockItems (symtab', items) of
       | Some sty ->
         (rety ~= void => next nin? sty) &&
         (fa(ty) return ty in? sty => assignableReturnTypes? (rety, ty))
       | None -> false)
     | _ -> false)

(* Another important invariant is that every object designator in the state
designates an object in the state. The condition that an object designator
designates an object in the state is equivalent to op 'readObject' returning
'ok'. *)

op objDesignatorOK? (state:State, obj:ObjectDesignator) : Bool =
  embed? ok (readObject (state, obj))

op allObjDesignatorsOK? (state:State) : Bool =
  fa(obj) obj in? objDesignatorsInState state => objDesignatorOK? (state, obj)

(* We put together the above invariants into one predicate *)

op invariants? (state:State) : Bool =
  noCircularStructs?   state &&
  noCircularFunctions? state &&
  functionBodiesOK?    state &&
  allObjDesignatorsOK? state


%subsection (* Attachment and detachment of outside storage *)

(* When modeling the interaction of a program in our C subset with outside code,
it is convenient to attach and detach outside storage to and from the state. If
outside code calls a function in our C program, there will be an outside storage
to be attached to the state. During the execution of the function, assuming no
multi-threading (as our formal model assumes), outside storage can only be
changed by our program (which does not call the outside code). When the function
returns, the outside storage can be detached from the state, because at that
point the outside code can modify the external storage. By attaching and
detaching outside storage to the state, we can model various forms of
interaction between our C program and outside code, and we can model various
kinds on assumptions on modifications to outside storage made by outside code in
between calls to functions in our C program.

In order to attach and detach outside storage, certain closure conditions on
pointers (i.e. object designators) must be satisfied. These conditions are
modeled below, along with ops to attach and detach outside storage.

We start with an op that returns the object designators that are in a state but
not in the outside storage of the state. *)

op objDesignatorsInNonOutsideStorage
   (state:State) : FiniteSet ObjectDesignator =
  objDesignatorsInNamedStorage state.storage.static \/
  objDesignatorsInFrames       state.storage.automatic

(* Together with the object designators in the outside storage, the object
designators returned by op 'objDesignatorsInNonOutsideStorage' are all the
object designators in the state. *)

theorem object_designators_outside_nonoutside_union is
  fa(state:State)
    objDesignatorsInState state =
    objDesignatorsInNonOutsideStorage state \/
    objDesignatorsInOutsideStorage state.storage.outside

theorem object_designators_outside_nonoutside_intersection is
  fa(state:State)
    objDesignatorsInNonOutsideStorage state /\
    objDesignatorsInOutsideStorage state.storage.outside = empty

(* The following op says whether the non-outside storage of a state has no
references to the outside storage of the state. *)

op noReferencesToOutsideStorage? (state:State) : Bool =
  fa(obj) obj in? objDesignatorsInNonOutsideStorage state =>
          ~ (embed? outside obj)

(* The following op says whether an outside storage has only references to
outside storage. *)

op allReferencesToOutsideStorage? (ostore:OutsideStorage) : Bool =
  fa(obj) obj in? objDesignatorsInOutsideStorage ostore => embed? outside obj

(* If the outside and the non-outside storage of a state are partitioned
(i.e. the non-outside storage has no references to the outside storage, and the
outside storage has no references to the non-outside storage), we allow the
outside storage to be detached from the state. The state invariants are
maintained. *)

op detachableOutsideStorage? (state:State) : Bool =
  noReferencesToOutsideStorage? state &&
  allReferencesToOutsideStorage? (state.storage.outside)

op detachOutsideStorage
   (state:State | detachableOutsideStorage? state) : State =
  updateOutsideStorage (state, empty)

theorem detachOutsideStorage_invariants is
  fa(state:State) invariants? state && detachableOutsideStorage? state =>
                  invariants? (detachOutsideStorage state)

(* If a state has empty outside storage, an outside storage with no references
to the state's storage can be attached to the state. The state invariants are
maintained. *)

op attachableOutsideStorage? (state:State, ostore:OutsideStorage) : Bool =
  empty? state.storage.outside && allReferencesToOutsideStorage? ostore

op attachOutsideStorage
   (state:State, ostore:OutsideStorage |
    attachableOutsideStorage? (state, ostore)) : State =
  updateOutsideStorage (state, ostore)

theorem attachOutsideStorage_invariants is
  fa (state:State, ostore:OutsideStorage)
    invariants? state && attachableOutsideStorage? (state, ostore) =>
    invariants? (attachOutsideStorage (state, ostore))


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

op convertInteger (val:Value, ty:Type | integerType? ty) : OC Value =
  {i <- mathIntOfValue val;
   if i in? rangeOfIntegerType ty then
     ok (valueOfMathInt (i, ty))
   else if unsignedIntegerType? ty || (plainCharsAreUnsigned && ty = char) then
     let max1:Nat = maxOfIntegerType ty + 1 in
     let i':Int = the(i':Int) i' in? rangeOfIntegerType ty &&
                              (ex(k:Int) i' = i + k * max1) in
     ok (valueOfMathInt (i', ty))
   else
     nonstd}

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


%subsubsection (* Integer promotions *)

(* At run time, integer promotion [ISO 6.3.1.1/2] can be expressed as a mapping
from values to values: the value is converted to the type returned by op
'promoteType'. *)

op promoteValue (val:Value) : OC Value =
  if integerValue? val then
    convertInteger (val, promoteType (typeOfValue val))
  else
    error


%subsubsection (* Usual arithmetic conversions *)

(* At run time, the 'usual arithmetic conversions' [ISO 6.3.1.8] can be
expressed as a mapping from pairs of values to pairs of values: the original
values are converted to two values of the type returned by op
arithConvertTypes. *)

op arithConvertValues (val1:Value, val2:Value) : OC (Value * Value) =
  if arithmeticValue? val1 && arithmeticValue? val2 then
    let ty = arithConvertTypes (typeOfValue val1, typeOfValue val2) in
    {newval1 <- convertInteger (val1, ty);
     newval2 <- convertInteger (val2, ty);
     ok (newval1, newval2)}
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

op convertPointer (val:Value, ty:Type | embed? pointer ty) : OC Value =
  let ty0 = typeOfValue val in
  if compatibleTypes? (ty0, ty) then
    ok val
  else if embed? pointer ty0 && (ty0 = pointer void || ty = pointer void) then
    if embed? nullpointer val then
      ok (nullpointer ty)
    else
      nonstd
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

op convertForAssignment (val:Value, ty:Type) : OC Value =
  if arithmeticType? ty then
    convertInteger (val, ty)
  else if embed? struct ty && compatibleTypes? (typeOfValue val, ty) then
    ok val
  else if embed? pointer ty then
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

op evaluateIntegerConstant (c:IntegerConstant) : OC Value =
  case checkIntegerConstant c of
  | Some ty -> ok (valueOfMathInt (integerConstantValue c, ty))
  | None -> error


%subsection (* Unary and binary operators *)

(* The unary '+' operator requires an arithmetic operand [ISO 6.5.3.3/1] and
just returns the promoted operand [ISO 6.5.3.3/2]. Note that op 'promoteValue'
returns an error if the value is not arithmetic. *)

op operator_PLUS (val:Value) : OC Value =
  promoteValue val

(* The unary '-' operator requires an arithmetic operand [ISO 6.5.3.3/1] and
returns the negative of its promoted operand [ISO 6.5.3.3/3].

If the operand is unsigned, we follow the laws of arithmetic modulo MAX + 1
(where MAX is maximum integer representable in the operand's type) [ISO
6.2.5/9].

If the operand is signed and its negative cannot be represented in the operand's
type, the behavior is undefined [ISO 6.5/5]. *)

op operator_MINUS (val:Value) : OC Value =
  {val' <- promoteValue val;
   let ty = typeOfValue val' in
   let ok x = mathIntOfValue val' in
   let y = - x in
   if unsignedIntegerType? ty then
     ok (valueOfMathInt (y modF (maxOfIntegerType ty + 1), ty))
   else
     if y in? rangeOfIntegerType ty then
       ok (valueOfMathInt (y, ty))
     else
       nonstd}

(* The '~' operator requires an integer operand [ISO 6.5.3.3/1] and returns the
bitwise complement of the promoted operand [ISO 6.5.3.3/4]. *)

op operator_NOT (val:Value) : OC Value =
  {val' <- promoteValue val;
   bits <- bitsOfIntegerValue val';
   ok (valueOfBits (Bits.not bits, typeOfValue val'))}

(* The '!' operator requires a scalar operand [ISO 6.5.3.3/1] and returns the
signed int 1 or 0 depending on whether the operator compares equal or unequal to
0 [ISO 6.5.3.3/5]. *)

op operator_NEG (val:Value) : OC Value =
  {isZero <- zeroScalarValue? val;
   if isZero then ok int1 else ok int0}

(* The binary '*' operator requires arithmetic operands [ISO 6.5.5/2], performs
the usual arithmetic conversions [ISO 6.5.5/3], and returns the product [ISO
6.5.5/4]. Note that op arithConvertValues returns an error if any of the values
is not arithmetic.

If the operands are unsigned, we follow the laws of arithmetic modulo MAX+1
(where MAX is maximum integer representable in the operand's type) [ISO
6.2.5/9].

If the operands are signed and their product cannot be represented in the
operand's type, the behavior is undefined [ISO 6.5/5]. *)

op operator_MUL (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ty = typeOfValue val1' in
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   let y = x1 * x2 in
   if unsignedIntegerType? ty then
     ok (valueOfMathInt (y modF (maxOfIntegerType ty + 1), ty))
   else
     if y in? rangeOfIntegerType ty then
       ok (valueOfMathInt (y, ty))
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

op operator_DIV (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ty = typeOfValue val1' in
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   if x2 = 0 then nonstd else
   let y = x1 divT x2 in
   if unsignedIntegerType? ty then
     ok (valueOfMathInt (y modF (maxOfIntegerType ty + 1), ty))
   else
     if y in? rangeOfIntegerType ty then
       ok (valueOfMathInt (y, ty))
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

op operator_REM (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ty = typeOfValue val1' in
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   if x2 = 0 then nonstd else
   let y = x1 modT x2 in
   if unsignedIntegerType? ty then
     ok (valueOfMathInt (y modF (maxOfIntegerType ty + 1), ty))
   else
     if y in? rangeOfIntegerType ty then
       ok (valueOfMathInt (y, ty))
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

op operator_ADD (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ty = typeOfValue val1' in
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   let y = x1 + x2 in
   if unsignedIntegerType? ty then
     ok (valueOfMathInt (y modF (maxOfIntegerType ty + 1), ty))
   else
     if y in? rangeOfIntegerType ty then
       ok (valueOfMathInt (y, ty))
     else
       nonstd}

(* The binary '-' operator requires arithmetic operands (our C subset excludes
pointer arithmetic) [ISO 6.5.6/3], performs the usual arithmetic conversions
[ISO 6.5.6/4], and returns the difference [ISO 6.5.6/6].

If the operands are unsigned, we follow the laws of arithmetic modulo MAX+1
(where MAX is maximum integer representable in the operand's type) [ISO
6.2.5/9].

If the operands are signed and their product cannot be represented in the
operand's type, the behavior is undefined [ISO 6.5/5]. *)

op operator_SUB (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ty = typeOfValue val1' in
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   let y = x1 - x2 in
   if unsignedIntegerType? ty then
     ok (valueOfMathInt (y modF (maxOfIntegerType ty + 1), ty))
   else
     if y in? rangeOfIntegerType ty then
       ok (valueOfMathInt (y, ty))
     else
       nonstd}

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

op operator_SHL (val1:Value, val2:Value) : OC Value =
  {val1' <- promoteValue val1;
   val2' <- promoteValue val2;
   let ty = typeOfValue val1' in
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   if x2 < 0 || x2 >= typeBits ty then nonstd else
   let y = x1 * 2**x2 in
   if unsignedIntegerType? ty then
     ok (valueOfMathInt (y modF (maxOfIntegerType ty + 1), ty))
   else
     if x1 >= 0 && y in? rangeOfIntegerType ty then
       ok (valueOfMathInt (y, ty))
     else
       nonstd}

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

(* The '>>' operator requires integer operands [ISO 6.5.7/2], promotes them, and
right-shifts the first operand E1 by the number of positions E2 indicated by the
second operand [ISO 6.5.7/5]. If E2 is negative or greater than or equal to the
size of E1, the behavior is undefined [ISO 6.5.7/3].

If E1 is unsigned, or if it signed and non-negative, the result is the integral
part of the quotient E1 / 2^E2 [ISO 6.5.7/5]. Otherwise, the result is
implementation-dependent [ISO 6.5.7/5]. *)

op operator_SHR (val1:Value, val2:Value) : OC Value =
  {val1' <- promoteValue val1;
   val2' <- promoteValue val2;
   let ty = typeOfValue val1' in
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   if x2 < 0 || x2 >= typeBits ty then nonstd else
   let y = x1 divT 2**x2 in
   if unsignedIntegerType? ty ||
      signedIntegerType? ty && x1 >= 0 then
     ok (valueOfMathInt (y, ty))
   else
     nonstd}

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

(* The '<', '>', '<=', and '>=' operators require real operands (our C subset
excludes pointer comparisons) [ISO 6.5.8/2], perform the usual arithmetic
conversions [ISO 6.5.8/3], and return the signed int 1 or 0 depending on whether
the comparison is true or false [ISO 6.5.8/6]. *)

op operator_LT (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   if x1 < x2 then ok int1 else ok int0}

op operator_GT (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   if x1 > x2 then ok int1 else ok int0}

op operator_LE (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   if x1 <= x2 then ok int1 else ok int0}

op operator_GE (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ok x1 = mathIntOfValue val1' in
   let ok x2 = mathIntOfValue val2' in
   if x1 >= x2 then ok int1 else ok int0}

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

op operator_EQ (val1:Value, val2:Value) : OC Value =
  if arithmeticValue? val1 && arithmeticValue? val2 then
    {(val1', val2') <- arithConvertValues (val1, val2);
     let x1 = mathIntOfValue val1' in
     let x2 = mathIntOfValue val2' in
     if x1 = x2 then ok int1 else ok int0}
  else if pointerValue? val1 && pointerValue? val2 &&
          (compatibleTypes? (typeOfValue val1, typeOfValue val2) ||
           typeOfValue val1 = pointer void ||
           typeOfValue val2 = pointer void) then
    if embed? undefined val1 || embed? undefined val2 then
      nonstd
    else if embed? nullpointer val1 && embed? nullpointer val2
            || val1 = val2 then
      ok int1
    else
      ok int0
  else
    error

op operator_NE (val1:Value, val2:Value) : OC Value =
  {eq_result <- operator_EQ (val1, val2);
   if eq_result = int0 then ok int1 else ok int0}

(* The binary '&' operator, the '^' operator, and the '|' operator require
integer operands [ISO 6.5.10/2, 6.5.11/2, 6.5.12/2], perform the usual
arithmetic conversions [ISO 6.5.10/3, 6.5.11/3, 6.5.12/3], and return the
bitwise AND [ISO 6.5.10/4], exclusive OR [ISO 6.5.11/4], and inclusive OR [ISO
6.5.12/4] of their operands. *)

op operator_AND (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ty = typeOfValue val1' in
   let ok bits1 = bitsOfIntegerValue val1' in
   let ok bits2 = bitsOfIntegerValue val2' in
   ok (valueOfBits (bits1 Bits.and bits2, ty))}

op operator_XOR (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ty = typeOfValue val1' in
   let ok bits1 = bitsOfIntegerValue val1' in
   let ok bits2 = bitsOfIntegerValue val2' in
   ok (valueOfBits (bits1 Bits.xor bits2, ty))}

op operator_IOR (val1:Value, val2:Value) : OC Value =
  {(val1', val2') <- arithConvertValues (val1, val2);
   let ty = typeOfValue val1' in
   let ok bits1 = bitsOfIntegerValue val1' in
   let ok bits2 = bitsOfIntegerValue val2' in
   ok (valueOfBits (bits1 Bits.ior bits2, ty))}

(* We do not define ops 'operator_LAND' and 'operator_LOR' for the '&&' and '||'
operators because they are non-strict, i.e. the second value is calculated only
if the first value does not already determine the result, as formalized below.
We do not define ops 'operator_ADDR' and 'operator_STAR' because they do not
quite operate on values, as formalized below. *)


%subsection (* Expressions *)

(* The result of an expression in our C subset is an object designator or a
value [ISO 6.5/1]. In our C subset, expressions do not have side effects and
never designate functions.

The following type captures these two kinds of expression result. *)

type ExpressionResult =
  | object ObjectDesignator
  | value  Value

(* If a subexpression results in an object designator, but the superexpression
needs a value, the object designator is converted into a value, namely the value
stored in the designated object. The following op coerces an expression result
into a value -- if already a value, there is no change. In order to retrieve the
value stored in an object, the op has a state argument. *)

op expressionValue (state:State, res:ExpressionResult) : OC Value =
  case res of
  | object obj -> readObject (state, obj)
  | value val -> ok val

(* It is convenient to lift the previous op to lists. *)

op expressionValues
   (state:State, ress:List ExpressionResult) : OC (List Value) =
  case ress of
  | [] -> ok []
  | res::ress ->
    {val <- expressionValue (state, res);
     vals <- expressionValues (state, ress);
     ok (val :: vals)}

(* We lift op typeOfValue to expression results and expression types. The type
of an expression type is the type of the value of the expression result. The
object flag is set iff the expression result is an object designator. *)

op typeOfExpressionResult
   (state:State, res:ExpressionResult) : OC ExpressionType =
  {val <- expressionValue (state, res);
   ok {typE = typeOfValue val, object = embed? object res}}

(* For most purposes, (an object designator to) an array that results from an
expression is converted into a pointer to the array's initial element [ISO
6.3.2.1/3]. The following op performs this conversion on an expression result,
when needed. An expression result that is a value is not changed, even if the
value itself is a value, because as formalized later the evaluation of an
expression never yields an array value as result, only an array designator. *)

op convertToPointerIfArray
   (state:State, res:ExpressionResult) : OC ExpressionResult =
  case res of
  | object obj ->
    {val <- readObject (state, obj);
     case typeOfValue val of
     | array (ty, n) ->
       if n ~= 0 then ok (value (pointer (ty, subscript (obj, 0))))
       else nonstd % array is empty, so there is no initial element
     | _ -> ok (object obj)} % no change
  | value val -> ok (value val)  % no change

(* It is convenient to lift the previous op to lists. *)

op convertToPointersIfArrays
   (state:State, ress:List ExpressionResult) : OC (List ExpressionResult) =
  case ress of
  | [] -> ok []
  | res::ress ->
    {res' <- convertToPointerIfArray (state, res);
     ress' <- convertToPointersIfArrays (state, ress);
     ok (res' :: ress')}

(* We formalize expression evaluation via an op that, given a state, returns an
expression result outcome.

Op 'convertToPointerIfArray' is applied to every operand (that may be an array),
except for the operand of unary '&' [ISO 6.3.2.1/3] -- note that our C subset
does not include the 'sizeof' operator, which is the other case in which op
'convertToPointerIfArray' should not be used.

A variable [ISO 6.5.1/2] evaluates to the object designator that the variable
references.

An integer constant [ISO 6.5.1/3] evaluates to the integer value formalized by
op 'evaluateIntegerConstant'.

In a unary expression, first the operand is evaluated, then the operator is
applied. For the unary '&' operator, the operand must result in an object
designator [ISO 6.5.3.2/1], which is returned as a pointer value [ISO
6.5.3.2/3]. For the unary '*' operator, the operand must be a pointer [ISO
6.5.3.2/2], which is returned as an object designator [ISO 6.5.3.2/4]. There is
an exception to this evaluation procedure: an expression of the form '&*E'
evaluates to the same as E, i.e. '&' and '*' are not applied [ISO 6.5.3.2/3].
The difference between the normal evaluation procedure and this exception is
visible when 'E' is null: dereferencing null yields undefined behavior [ISO
6.5.3.2/4]. Dereferencing an undefined pointer value yields undefined behavior.
The other exception to normal evaluation mentioned in [ISO 6.5.3.2/3], namely
the evaluation of an expression of the form '&E[I]', which evaluates to the same
as 'E + I', makes a difference in our C subset only if 'E' is null and 'I' is 0,
because in that case the result is null instead of being non-standard. If 'E' is
null and 'I' is not 0, then 'E + I' is undefined according to [ISO 6.5.6/8],
just like '&E[I]' is undefined. If 'E' is not null, then there is no difference
between the result of '&E[I]' and 'E + I' according to [ISO]. Note also that,
according to [ISO 6.3.2.1/3], we do not use op 'convertToPointerIfArray' on the
operand of unary '&'.

In a binary expression with any operator but '&&' and '||', first the operands
are evaluated, then the operator is applied. Since expressions in our C subset
have no side-effects, and since they both must be evaluated (in some order), it
makes no difference which one is evaluated first.

In a binary expression with the '&&' or '||' operator, the first operand, which
must be scalar [ISO 6.5.13/2, 6.5.14/2], is compared with 0. If that suffices to
determine the result (i.e. 0 for '&&', non-0 for '||'), the result (i.e. the
signed int 0 or 1) is returned. Otherwise, the second operand, which must be
scalar [ISO 6.5.13/2, 6.5.14/2] is compared with 0, returning the signed 'int' 0
or 1 depending on whether the comparison with 0 succeeds or fails. In other
words, '&&' and '||' guarantee left-to-right evaluation and the second operand
is evaluated only if needed [ISO 6.5.13/4, 6.5.14/4].

A conditional expression requires a scalar first operand [ISO 6.5.15/2], which
it evaluates and compares with 0 [ISO 6.5.15/4]. Based on the result of the
comparison, the second or third operand is evaluated and returned [ISO
6.5.15/4], converted to the type that is the fourth argument of the 'cond'
constructor. This explains the reason for this fourth argument: without this
fourth argument, since only one of the second and third operands is evaluated,
we would not have enough information to calculate the type of the result, which
depends on the types of both second and third operands (cf. op
'checkExpression').

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

op evaluate (state:State, expr:Expression) : OC ExpressionResult =
  case expr of
  | ident var -> 
    {obj <- designatorOfObject (state, var);
     ok (object obj)}
  | const c ->
    {val <- evaluateIntegerConstant c;
     ok (value val)}
  | unary (uop, expr) ->
    % special treatment for expr of the form '& * expr0':
    if uop = ADDR && (ex(expr0:Expression) expr = unary (STAR, expr0)) then
      let unary (STAR, expr0) = expr in
      evaluate (state, expr0)
    % special treatment for expr of the form '& expr0 [ expr1 ]',
    % if 'expr1' yields 0:
    else if uop = ADDR &&
            (ex (expr0:Expression,
                 expr1:Expression,
                 res1:ExpressionResult,
                 val1:Value)
               expr = subscript (expr0, expr1) &&
               evaluate (state, expr1) = ok res1 &&
               expressionValue (state, res1) = ok val1 &&
               mathIntOfValue val1 = ok 0) then
      let subscript (expr0, _) = expr in
      evaluate (state, expr0)
    % normal evaluation procedure for unary operators:
    else
    {res <- evaluate (state, expr);
     case uop of
     | ADDR ->
       (case res of
       | object obj ->
         {val <- expressionValue (state, res);
          ok (value (pointer (typeOfValue val, obj)))}
       | value _ -> error)
     | STAR ->
       {res' <- convertToPointerIfArray (state, res);
        val <- expressionValue (state, res');
        case val of
        | pointer (_, obj)      -> ok (object obj)
        | nullpointer _         -> nonstd
        | undefined (pointer _) -> nonstd
        | _                     -> error}
     | PLUS ->
       {val <- expressionValue (state, res);
        val' <- operator_PLUS val;
        ok (value val')}
     | MINUS ->
       {val <- expressionValue (state, res);
        val' <- operator_MINUS val;
        ok (value val')}
     | NOT ->
       {val <- expressionValue (state, res);
        val' <- operator_NOT val;
        ok (value val')}
     | NEG ->
       {res' <- convertToPointerIfArray (state, res);
        val <- expressionValue (state, res');
        val' <- operator_NEG val;
        ok (value val')}}
  | binary (expr1, bop, expr2) ->
    {res1 <- evaluate (state, expr1);
     res1' <- convertToPointerIfArray (state, res1);
     val1 <- expressionValue (state, res1');
     if bop = LAND then
       {isZero1 <- zeroScalarValue? val1;
        if isZero1 then ok (value int0)
        else
          {res2 <- evaluate (state, expr2);
           res2' <- convertToPointerIfArray (state, res2);
           val2 <- expressionValue (state, res2');
           isZero2 <- zeroScalarValue? val2;
           if isZero2 then ok (value int0) else ok (value int1)}}
     else if bop = LOR then
       {isZero1 <- zeroScalarValue? val1;
        if ~ isZero1 then ok (value int1)
        else
          {res2 <- evaluate (state, expr2);
           res2' <- convertToPointerIfArray (state, res2);
           val2 <- expressionValue (state, res2');
           isZero2 <- zeroScalarValue? val2;
           if isZero2 then ok (value int0) else ok (value int1)}}
     else
     {res2 <- evaluate (state, expr2);
      res2' <- convertToPointerIfArray (state, res2);
      val2 <- expressionValue (state, res2');
      case bop of
      | MUL ->
        {val' <- operator_MUL (val1, val2);
         ok (value val')}
      | DIV ->
        {val' <- operator_DIV (val1, val2);
         ok (value val')}
      | REM ->
        {val' <- operator_REM (val1, val2);
         ok (value val')}
      | ADD ->
        {val' <- operator_ADD (val1, val2);
         ok (value val')}
      | SUB ->
        {val' <- operator_SUB (val1, val2);
         ok (value val')}
      | SHL ->
        {val' <- operator_SHL (val1, val2);
         ok (value val')}
      | SHR ->
        {val' <- operator_SHR (val1, val2);
         ok (value val')} 
      | LT ->
        {val' <- operator_LT (val1, val2);
         ok (value val')}
      | GT ->
        {val' <- operator_GT (val1, val2);
         ok (value val')}
      | LE ->
        {val' <- operator_LE (val1, val2);
         ok (value val')}
      | GE ->
        {val' <- operator_GE (val1, val2);
         ok (value val')}
      | EQ ->
        {val' <- operator_EQ (val1, val2);
         ok (value val')}
      | NE ->
        {val' <- operator_NE (val1, val2);
         ok (value val')}
      | AND ->
        {val' <- operator_AND (val1, val2);
         ok (value val')}
      | XOR ->
        {val' <- operator_XOR (val1, val2);
         ok (value val')}
      | IOR ->
        {val' <- operator_IOR (val1, val2);
         ok (value val')}}}
  | cond (expr1, expr2, expr3, ty) ->
    {res1 <- evaluate (state, expr1);
     res1' <- convertToPointerIfArray (state, res1);
     val1 <- expressionValue (state, res1');
     isZero <- zeroScalarValue? val1;
     if ~ isZero then
       {res2 <- evaluate (state, expr2);
        res2' <- convertToPointerIfArray (state, res2);
        val2 <- expressionValue (state, res2');
        if integerType? ty then
          {val' <- convertInteger (val2, ty);
           ok (value val')}
        else if embed? pointer ty then
          {val' <- convertPointer (val2, ty);
           ok (value val')}
        else if typeOfValue val2 = ty then
          ok (value val2)
        else
          error}
     else
       {res3 <- evaluate (state, expr3);
        res3' <- convertToPointerIfArray (state, res3);
        val3 <- expressionValue (state, res3');
        if integerType? ty then
          {val' <- convertInteger (val3, ty);
           ok (value val')}
        else if embed? pointer ty then
          {val' <- convertPointer (val3, ty);
           ok (value val')}
        else if typeOfValue val3 = ty then
          ok (value val3)
        else
          error}}
  | member (expr, mem) ->
    {res <- evaluate (state, expr);
     val <- expressionValue (state, res);
     case typeOfValue val of
     | struct tag ->
       (case state.structures tag of
       | None -> error
       | Some tmembers ->
         {errorIf (mem nin? domain tmembers);
          case res of
          | object obj -> ok (object (member (obj, mem)))
          | value val ->
            (case val of
            | struct (_, members) -> ok (value (members @ mem))
            | undefined _ -> nonstd)})
     | _ -> error}
  | memberp (expr, mem) ->
    {res <- evaluate (state, expr);
     val <- expressionValue (state, res);
     case typeOfValue val of
     | pointer (struct tag) ->
       (case state.structures tag of
       | None -> error
       | Some tmembers ->
         {errorIf (mem nin? domain tmembers);
          case val of
          | pointer (_, obj) -> ok (object (member (obj, mem)))
          | undefined _ -> nonstd})
     | _ -> error}
  | subscript (expr, expr') ->
    {res0 <- evaluate (state, expr);
     res <- convertToPointerIfArray (state, res0);
     val <- expressionValue (state, res);
     res' <- evaluate (state, expr');
     val' <- expressionValue (state, res');
     case typeOfValue val of
     | pointer _ ->
       (case res of
       | object (subscript (obj, i)) ->
         (case readObject (state, obj) of
         | ok (array (_, vals)) ->
           {j <- mathIntOfValue val';
            nonstdIf (j < 0 || i + j >= length vals);
            ok (object (subscript (obj, i + j)))}
         | _ -> nonstd)
       | _ -> error)
     | _ -> error}
  | nullconst ->
    ok (value (nullpointer (pointer void)))

(* Evaluating, in a state that satisfies the invariants, an expression that
satisfies the compile-time constraints w.r.t. the symbol table of the state,
does not yield an error. Furthermore, if a normal outcome occurs, the expression
result has the expression type inferred by the compile-time constraints. *)

theorem expression_evaluation is
  fa (state:State, expr:Expression, ety:ExpressionType)
    invariants? state &&
    checkExpression (symbolTableOfState state, expr) = Some ety =>
    (case evaluate (state, expr) of
    | ok res -> typeOfExpressionResult (state, res) = ok ety
    | error -> false
    | nonstd -> true
    | nonterm -> true)

(* It is useful to introduce an op to evaluate a sequence of expressions, one
after the other. *)

op evaluateAll
   (state:State, exprs:List Expression) : OC (List ExpressionResult) =
  case exprs of
  | [] -> ok []
  | expr::exprs ->
    {res <- evaluate (state, expr);
     ress <- evaluateAll (state, exprs);
     ok (res :: ress)}


%subsection (* Type names *)

(* A type name denotes a type. The following op returns the type denoted by a
type name w.r.t. a state. Recall that a state includes a symbol table for type
definitions: this is used to look up, and expand away, typedef names. This op is
similar to op 'checkTypeName'. *)

op expandTypeName (state:State, tyn:TypeName) : OC Type =
  case tyn of
  | typedef tdn ->
    (case state.typedefs tdn of
    | None -> error
    | Some ty -> ok ty)
  | pointer tyn ->
    {ty <- expandTypeName (state, tyn);
     ok (pointer ty)}
  | array (tyn, n) ->
    {ty <- expandTypeName (state, tyn);
     ok (array (ty, n))}
  | struct tag -> ok (struct tag)
  |  char  -> ok  char
  | uchar  -> ok uchar
  | schar  -> ok schar
  | ushort -> ok ushort
  | sshort -> ok sshort
  | uint   -> ok uint
  | sint   -> ok sint
  | ulong  -> ok ulong
  | slong  -> ok slong
  | ullong -> ok ullong
  | sllong -> ok sllong
  | void   -> ok void


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
non-circularity of the structures is part of the state invariants. *)

op zeroOfType (state:State, ty:Type) : OC Value =
  if ~ (invariants? state) then error else
  case ty of
  | void -> error
  | struct tag ->
    (case state.structures tag of
    | None -> error
    | Some tmembers ->
      let orderedMembers: List (Identifier * Type) =
          toAssocList tmembers (String.<=) in
      let (mems, tys) = unzip orderedMembers in
      {vals <- zerosOfTypes (state, tys);
       ok (struct (tag, fromAssocList (zip (mems, vals))))})
  | array (ty0, n) ->
    {val0 <- zeroOfType (state, ty0);
     ok (array (ty0, repeat val0 n))}
  | ty -> ok (zeroOfScalarType ty)

op zerosOfTypes (state:State, tys:List Type) : OC (List Value) =
  if ~ (invariants? state) then error else
  case tys of
  | [] -> ok []
  | ty::tys ->
    {val <- zeroOfType (state, ty);
     vals <- zerosOfTypes (state, tys);
     ok (val::vals)}


%subsection (* Declarations *)

(* When an object declaration is encountered at run time, the declared object is
added to the innermost active scope of the storage. This could be in the static
storage (for an object declared with file scope) or in the automatic storage
(for an object declared with block scope).

If the declared object has file scope, it goes into static storage and it is
initialized to 0 [ISO 6.9.2/2]. If the declared object has block scope, it goes
into automatic storage; if it has no initializer, its initial value is
indeterminate [ISO 6.7.8/10]. Since object declarations in our C subset have no
explicit initializer, we set the initial value to be undefined. *)

op execObjectDeclaration (state:State, odecl:ObjectDeclaration) : OC State =
  {ty <- expandTypeName (state, odecl.typE);
   zeroVal <- zeroOfType (state, ty);
   errorIf (odecl.name in? domain state.typedefs);
   let store = state.storage in
   if store.automatic = [] then
     {errorIf (odecl.name in? domain store.static);
      errorIf (odecl.name in? domain state.typedefs);
      errorIf (odecl.name in? domain state.functions);
      ok (updateStaticObject (state, odecl.name, zeroVal))}
   else
     let topframe = last store.automatic in
     {errorIf (empty? topframe);
      errorIf (odecl.name in? domain (last topframe));
      ok (updateAutomaticObject
           (state, length store.automatic - 1, length topframe - 1,
                   odecl.name, undefined ty))}}

(* Executing, in a state that satisfies the invariants, an object declaration
that satisfies the compile-time constraints w.r.t. the symbol table of the
state, does not yield an error. Furthermore, if a normal outcome occurs, the new
state satisfies the invariants and the symbol table of the new state is the one
inferred by the compile-time constraints. *)

theorem object_declaration_execution is
  fa (state:State, odecl:ObjectDeclaration, symtab:SymbolTable)
    invariants? state &&
    checkObjectDeclaration (symbolTableOfState state, odecl) = Some symtab =>
    (case execObjectDeclaration (state, odecl) of
    | ok state' -> invariants? state' && symtab = symbolTableOfState state'
    | error -> false
    | nonstd -> true
    | nonterm -> true)

(* When a structure specifier is encountered, the state of the program is
extended with information about the structure. *)

op execMemberDeclarations
   (state:State, decls:List MemberDeclaration) : OC TypedMembers =
  case decls of
  | [] -> ok empty
  | decl::decls ->
    let tyn = decl.typE in
    let mem = decl.name in
    {tmembers <- execMemberDeclarations (state, decls);
     ty <- expandTypeName (state, tyn);
     errorIf (ty = void);
     errorIf (mem in? domain tmembers);
     ok (update tmembers mem ty)}

op execStructSpecifier (state:State, sspec:StructSpecifier) : OC State =
  let tag = sspec.tag in
  {errorIf (tag in? domain state.structures);
   tmembers <- execMemberDeclarations (state, sspec.members);
   errorIf (tmembers = empty);
   ok (state << {structures = update state.structures tag tmembers})}

(* Executing, in a state that satisfies the invariants, a structure specifier
that satisfies the compile-time constraints w.r.t. the symbol table of the
state, does not yield an error. Furthermore, if a normal outcome occurs, the new
state satisfies the invariants and the symbol table of the new state is the one
inferred by the compile-time constraints. *)

theorem structure_specifier_execution is
  fa (state:State, sspec:StructSpecifier, symtab:SymbolTable)
    invariants? state &&
    checkStructSpecifier (symbolTableOfState state, sspec) = Some symtab =>
    (case execStructSpecifier (state, sspec) of
    | ok state' -> invariants? state' && symtab = symbolTableOfState state'
    | error -> false
    | nonstd -> true
    | nonterm -> true)

(* When a type definition is encountered, the state of the program is extended
with information about the structure. *)

op execTypeDefinition (state:State, tdef:TypeDefinition) : OC State =
  let tyn = tdef.typE in
  let tdn = tdef.name in
  {ty <- expandTypeName (state, tyn);
   errorIf (tdn in? domain state.typedefs);
   errorIf (tdn in? domain state.storage.static);
   errorIf (tdn in? domain state.functions);
   ok (state << {typedefs = update state.typedefs tdn ty})}

(* Executing, in a state that satisfies the invariants, a type definition that
satisfies the compile-time constraints w.r.t. the symbol table of the state,
does not yield an error. Furthermore, if a normal outcome occurs, the new state
satisfies the invariants and the symbol table of the new state is the one
inferred by the compile-time constraints. *)

theorem type_definition_execution is
  fa (state:State, tdef:TypeDefinition, symtab:SymbolTable)
    invariants? state &&
    checkTypeDefinition (symbolTableOfState state, tdef) = Some symtab =>
    (case execTypeDefinition (state, tdef) of
    | ok state' -> invariants? state' && symtab = symbolTableOfState state'
    | error -> false
    | nonstd -> true
    | nonterm -> true)

(* When a declaration is encountered, the state of the program is extended with
the declaration. *)

op execDeclaration (state:State, decl:Declaration) : OC State =
  case decl of
  | struct  sspec -> execStructSpecifier   (state, sspec)
  | object  odecl -> execObjectDeclaration (state, odecl)
  | typedef tdef  -> execTypeDefinition    (state, tdef)

(* Executing, in a state that satisfies the invariants, a declaration that
satisfies the compile-time constraints w.r.t. the symbol table of the state,
does not yield an error. Furthermore, if a normal outcome occurs, the new state
satisfies the invariants and the symbol table of the new state is the one
inferred by the compile-time constraints. *)

theorem declaration_execution is
  fa (state:State, decl:Declaration, symtab:SymbolTable)
    invariants? state &&
    checkDeclaration (symbolTableOfState state, decl) = Some symtab =>
    (case execDeclaration (state, decl) of
    | ok state' -> invariants? state' && symtab = symbolTableOfState state'
    | error -> false
    | nonstd -> true
    | nonterm -> true)


%subsection (* Statements *)

(* As formalized below, entering a block extends the top frame of the automatic
storage with a new, empty scope, which is retracted when the block is
exited. Upon retraction, any pointer to an object allocated in that block
becomes dangling. The dangling pointer may be in an object in an outer
scope. Similarly, calling a function extends the automatic storage with a new
frame, which is retracted when the function returns, potentially leaving
dangling pointers in the state.

In order to maintain the type safety of our C subset, we need to prevent these
dangling pointers from being used. To this end, the following ops sets them to
an undefined value. The following ops systematically set to 'undefined' any
pointer that designates an object in frame f and, if present, block b of frame f
-- if is not present, all pointers to all objects in frame f are set to
'undefined' (this happens when returning from a function). An op to extract the
scope designator from an object designator is also defined. *)

op scopeOfObjectDesignator
   (obj:ObjectDesignator | ~(embed? outside obj)) : ScopeDesignator =
  case obj of
  | top (scope, _)     -> scope
  | member    (obj, _) -> scopeOfObjectDesignator obj
  | subscript (obj, _) -> scopeOfObjectDesignator obj

op undefinePointersInValue (val:Value, f:Nat, b?:Option Nat) : Value =
  case val of
  | pointer (ty, obj) ->
    let dangling:Bool =
        case b? of
        | Some b -> scopeOfObjectDesignator obj = block (f, b)
        | None -> (ex(b:Nat) scopeOfObjectDesignator obj = block (f, b))
    in
    if dangling then undefined (pointer ty) else val
  | array (ty, vals) ->
    array (ty, undefinePointersInValues (vals, f, b?))
  | struct (tag, members) ->
    let orderedMembers: List (Identifier * Value) =
        toAssocList members (String.<=) in
    let (mems, vals) = unzip orderedMembers in
    let vals' = undefinePointersInValues (vals, f, b?) in
    let members' = fromAssocList (zip (mems, vals')) in
    struct (tag, members')
  | val -> val

op undefinePointersInValues
   (vals:List Value, f:Nat, b?:Option Nat) : List Value =
  case vals of
  | [] -> []
  | val::vals -> undefinePointersInValue (val, f, b?) ::
                 undefinePointersInValues (vals, f, b?)

op undefinePointersInNamedStorage
   (store:NamedStorage, f:Nat, b?:Option Nat) : NamedStorage =
  fn name:Identifier ->
    case store name of
    | Some val -> Some (undefinePointersInValue (val, f, b?))
    | None -> None

op undefinePointersInFrame
   (frame:List NamedStorage, f:Nat, b?:Option Nat) : List NamedStorage =
  map (fn nstore:NamedStorage -> undefinePointersInNamedStorage (nstore, f, b?))
      frame

op undefinePointersInOutsideStorage
   (store:OutsideStorage, f:Nat, b?:Option Nat) : OutsideStorage =
  fn id:OutsideID ->
    case store id of
    | Some val -> Some (undefinePointersInValue (val, f, b?))
    | None -> None

op undefinePointersInStorage (store:Storage, f:Nat, b?:Option Nat) : Storage =
  {static = undefinePointersInNamedStorage (store.static, f, b?),
   automatic = map (fn frame:List NamedStorage ->
                       undefinePointersInFrame (frame, f, b?))
                   store.automatic,
   outside = undefinePointersInOutsideStorage (store.outside, f, b?)}

op undefinePointersInState (state:State, f:Nat, b?:Option Nat) : State =
  state << {storage = undefinePointersInStorage (state.storage, f, b?)}

(* In order to call a function, a list of values must be supplied as arguments
[ISO 6.5.2.2/4]. The values are assigned to the function's parameters, and
therefore must match the number and types of the parameters (matching of types
is up to assignment). The following op creates a named storage with the
arguments stored into the parameters, while at the same time checking that they
match in number and types. *)

op assignArgumentsToParameters
   (state:State, tparams:TypedParameters, args:List Value) : OC NamedStorage =
  case tparams of
  | [] -> if args ~= [] then error else ok empty
  | tparam::tparams ->
    (case args of
    | [] -> error
    | val::vals ->
      {nstore <- assignArgumentsToParameters (state, tparams, vals);
       if tparam.name in? domain nstore then
         error
       else
         {val' <- convertForAssignment (val, tparam.typE);
          ok (update nstore tparam.name val')}})

(* After executing a statement 'S' in our C subset, control is transferred
either to the next statement to execute, or to the caller of the function in
which 'S' occurs. The latter case happens when executing a 'return'. The
following Specware type captures these two possible forms of statement
completion. In the return case, the returned value is included ('None' if the
'return' statement has no expression. *)

type StatementCompletion = | next | return Option Value

(* We lift op 'typeOfValue' to statement completions and statement type
elements. *)

op typeOfStatementCompletion
   (scomp:StatementCompletion) : StatementTypeElement =
  case scomp of
  | next              -> next
  | return (Some val) -> return (typeOfValue val)
  | return None       -> return void

(* We also introduce a relation that says when a statement completion has a
statement type. Because a statement type is a set, we need a relation. *)

op statementCompletionHasType?
   (scomp:StatementCompletion, sty:StatementType) : Bool =
  ex(styelem:StatementTypeElement)
    styelem in? sty && typeOfStatementCompletion scomp = styelem

(* Besides a completion, the execution of a statement is characterized by side
effects on the state. Thus, we regard the result of executing a statement as
consisting of an (updated) state plus a completion. We formalize statement
execution via an op that, given a state, returns a statement result outcome.

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

type StatementResult =
 {state      : State,
  completion : StatementCompletion}

op execStatement (state:State, stmt:Statement) : OC StatementResult =
  case stmt of
  | assign (expr1, expr2) ->
    {res1 <- evaluate (state, expr1);
     oldval <- expressionValue (state, res1);
     case res1 of
     | object obj ->
       {res2 <- evaluate (state, expr2);
        res2' <- convertToPointerIfArray (state, res2);
        newval <- expressionValue (state, res2');
        newval' <- convertForAssignment (newval, typeOfValue oldval);
        state' <- writeObject (state, obj, newval');
        ok {state = state', completion = next}}
     | value _ -> error}
  | call (expr?, fun, exprs) ->
    {ress <- evaluateAll (state, exprs);
     ress' <- convertToPointersIfArrays (state, ress);
     args <- expressionValues (state, ress');
     (state', val?) <- callFunction (state, fun, args);
     case expr? of
     | Some expr ->
       {res <- evaluate (state', expr);
        oldval <- expressionValue (state', res);
        case res of
        | object obj ->
          (case val? of
          | Some newval ->
            {newval' <- convertForAssignment (newval, typeOfValue oldval);
             state'' <- writeObject (state', obj, newval');
             ok {state = state'', completion = next}}
          | None -> error)
        | value _ -> error}
     | None -> ok {state = state', completion = next}}
  | iF (expr, thenBranch, Some elseBranch) ->
    {res <- evaluate (state, expr);
     res' <- convertToPointerIfArray (state, res);
     condition <- expressionValue (state, res');
     isZero <- zeroScalarValue? condition;
     if ~ isZero then
       execStatement (state, thenBranch)
     else
       execStatement (state, elseBranch)}
  | iF (expr, thenBranch, None) ->
    execStatement (state, iF (expr, thenBranch, Some (block [])))
  | return (Some expr) ->
    {res <- evaluate (state, expr);
     res' <- convertToPointerIfArray (state, res);
     val <- expressionValue (state, res');
     errorIf (empty? state.storage.automatic);
     let f = length state.storage.automatic - 1 in
     let state' = updateAutomaticStorage
                    (state, butLast state.storage.automatic) in
     ok {state = undefinePointersInState (state, f, None),
         completion = return (Some val)}}
  | return None ->
    if empty? state.storage.automatic then error else
    let f = length state.storage.automatic - 1 in
    let state' = updateAutomaticStorage
                   (state, butLast state.storage.automatic) in
    ok {state = undefinePointersInState (state, f, None),
        completion = return None}
  | while (expr, body) ->
    % the loop does not terminate if there is a stream of states:
    if (ex(states:Stream State)
          % the stream starts with the initial state:
          states 0 = state &&
          % for each state in the stream:
          (fa(i:Nat)
             % the test is true:
             (ex (res:ExpressionResult, res':ExpressionResult, condition:Value)
                evaluate (states i, expr) = ok res &&
                convertToPointerIfArray (state, res) = ok res' &&
                expressionValue (states i, res') = ok condition &&
                zeroScalarValue? condition = ok false)
             &&
             % the body completes and yields the next state:
             execStatement (states i, body) =
              ok {state = states (i + 1), completion = next}))
    then
      nonterm
    % otherwise, the loop eventually terminates:
    else
      {res <- evaluate (state, expr);
       res' <- convertToPointerIfArray (state, res);
       condition <- expressionValue (state, res');
       isZero <- zeroScalarValue? condition;
       % terminate if test is false:
       if isZero then
         ok {state = state, completion = next}
       % keep going if test is true (will terminate eventually, either because
       % the test will become false or because the body will execute a 'return'
       % statement):
       else
         execStatement
          (state, block [statement body, statement (while (expr, body))])}
  | do (body, expr) ->
    execStatement
     (state, block [statement body, statement (while (expr, body))])
  | for (first?, expr?, third?, body) ->
    let pre:List BlockItem =
        case first? of Some first -> [statement first] | None -> [] in
    let test:Expression =
        case expr? of Some expr -> expr | None -> const "1" in
    let post:List BlockItem =
        case third? of Some third -> [statement third] | None -> [] in
    execStatement
     (state,
      block (pre ++
             [statement (while (test, block ([statement body] ++ post)))]))
  | block items ->
    if empty? state.storage.automatic then error else
    let topframe = last state.storage.automatic in
    let f = length state.storage.automatic - 1 in
    let state' = updateAutomaticFrame (state, f, topframe ++ [empty]) in
    {res <- execBlockItems (state', items);
     let topframe' = last res.state.storage.automatic in
     let b = length topframe' - 1 in
     let state'' = updateAutomaticFrame (res.state, f, butLast topframe') in
     ok (res << {state = undefinePointersInState (state'', f, Some b)})}

op execBlockItems (state:State, items:List BlockItem) : OC StatementResult =
  case items of
  | [] -> ok {state = state, completion = next}
  | item::items ->
    {result <- execBlockItem (state, item);
     if result.completion = next then
       execBlockItems (result.state, items)
     else
       ok result}

op execBlockItem (state:State, item:BlockItem) : OC StatementResult =
  case item of
  | declaration odecl ->
    {state' <- execObjectDeclaration (state, odecl);
     ok {state = state', completion = next}}
  | statement stmt -> execStatement (state, stmt)

op callFunction (state:State, name:Identifier, args:List Value)
                : OC (State * Option Value) =
  case state.functions name of
  | None -> error
  | Some funinfo ->
    {newscope <- assignArgumentsToParameters (state, funinfo.parameters, args);
     let state' = updateAutomaticStorage
                    (state, state.storage.automatic ++ [[newscope]]) in
     case funinfo.body of
     | block items ->
       {result <- execBlockItems (state', items);
        case result.completion of
        | return (Some val) ->
          if embed? undefined val then
            nonstd
          else
            {val' <- convertForAssignment (val, funinfo.return);
             ok (result.state, Some val')}
        | _ ->
          if funinfo.return = void then
            ok (result.state, None)
          else
            error}
     | _ -> error}

(* Executing, in a state that satisfies the invariants, a statement that
satisfies the compile-time constraints w.r.t. the symbol table of the state,
does not yield an error. Furthermore, if a normal outcome occurs, the new state
satisfies the invariants and the completion of the statement has the statement
type inferred by the compile-time constraints.

The same applies to lists of block items. For single block items, an additional
property is that, in case of normal outcome, the new symbol table is the one of
the new state.

It is also the case that calling a function in a state that satisfies the
invariants, with argument values that match the function's parameters, does not
yield an error. Furthermore, if a normal outcome occurs, the new state satisfies
the invariants and the returned optional value matches the function's return
type (where None matches void).

The following four theorems must be proved simultaneously by induction. *)

theorem statement_execution is
  fa (state:State, stmt:Statement, sty:StatementType)
    invariants? state &&
    checkStatement (symbolTableOfState state, stmt) = Some sty =>
    (case execStatement (state, stmt) of
    | ok result -> invariants? result.state &&
                   statementCompletionHasType? (result.completion, sty)
    | error -> false
    | nonstd -> true
    | nonterm -> true)

theorem block_items_execution is
  fa (state:State, items:List BlockItem, sty:StatementType)
    invariants? state &&
    checkBlockItems (symbolTableOfState state, items) = Some sty =>
    (case execBlockItems (state, items) of
    | ok result -> invariants? result.state &&
                   statementCompletionHasType? (result.completion, sty)
    | error -> false
    | nonstd -> true
    | nonterm -> true)

theorem block_item_execution is
  fa (state:State, item:BlockItem, sty:StatementType, symtab:SymbolTable)
    invariants? state &&
    checkBlockItem (symbolTableOfState state, item) = Some (sty, symtab) =>
    (case execBlockItem (state, item) of
    | ok result -> invariants? result.state &&
                   statementCompletionHasType? (result.completion, sty) &&
                   symtab = symbolTableOfState result.state
    | error -> false
    | nonstd -> true
    | nonterm -> true)

theorem function_call is
  fa (state:State, name:Identifier, funinfo:FunctionInfo, args:List Value)
    invariants? state &&
    state.functions name = Some funinfo &&
    length args = length funinfo.parameters &&
    (fa (i:Nat)
       i < length args &&
       assignableTypes?
         (typeOfValue (args @ i), (funinfo.parameters @ i).typE)) =>
    (case callFunction (state, name, args) of
    | ok (state', val?) -> invariants? state' &&
                           (case val? of
                           | Some val -> typeOfValue val = funinfo.return
                           | None -> funinfo.return = void)
    | error -> false
    | nonstd -> true
    | nonterm -> true)


%subsection (* Function definitions *)

(* Executing a function definition incorporates the function into the state,
similarly to other external declarations. *)

op execParameterList (state:State, plist:ParameterList) : OC TypedParameters =
  case plist of
  | [] -> ok []
  | pdecl::pdecls ->
    {ty <- expandTypeName (state, pdecl.typE);
     errorIf (ty = void);
     tparams <- execParameterList (state, pdecls);
     errorIf (pdecl.name in? map (project name) tparams);
     ok ({typE = ty, name = pdecl.name} :: tparams)}

op execFunctionDefinition (state:State, fun:FunctionDefinition) : OC State =
  {rety <- expandTypeName (state, fun.return);
   errorIf (embed? array rety);
   errorIf (fun.name in? domain state.storage.static);
   errorIf (fun.name in? domain state.typedefs);
   errorIf (fun.name in? domain state.functions);
   tparams <- execParameterList (state, fun.parameters);
   let funinfo = {return = rety, parameters = tparams, body = fun.body} in
   ok (state << {functions = update state.functions fun.name funinfo})}

(* Executing, in a state that satisfies the invariants, a function definition
that satisfies the compile-time constraints w.r.t. the symbol table of the
state, does not yield an error. Furthermore, if a normal outcome occurs, the new
state satisfies the invariants and the symbol table of the new state is the one
inferred by the compile-time constraints. *)

theorem function_definition_execution is
  fa (state:State, fun:FunctionDefinition, symtab:SymbolTable)
    invariants? state &&
    checkFunctionDefinition (symbolTableOfState state, fun) = Some symtab =>
    (case execFunctionDefinition (state, fun) of
    | ok state' -> invariants? state' && symtab = symbolTableOfState state'
    | error -> false
    | nonstd -> true
    | nonterm -> true)


%subsection (* Translation units *)

(* We execute an external declaration as follows. *)

op execExternalDeclaration (state:State, xdecl:ExternalDeclaration) : OC State =
  case xdecl of
  | function fdef -> execFunctionDefinition (state, fdef)
  | declaration decl -> execDeclaration (state, decl)

(* Executing, in a state that satisfies the invariants, an external declaration
that satisfies the compile-time constraints w.r.t. the symbol table of the
state, does not yield an error. Furthermore, if a normal outcome occurs, the new
state satisfies the invariants and the symbol table of the new state is the one
inferred by the compile-time constraints. *)

theorem external_declaration_execution is
  fa (state:State, xdecl:ExternalDeclaration, symtab:SymbolTable)
    invariants? state &&
    checkExternalDeclaration (symbolTableOfState state, xdecl) = Some symtab =>
    (case execExternalDeclaration (state, xdecl) of
    | ok state' -> invariants? state' && symtab = symbolTableOfState state'
    | error -> false
    | nonstd -> true
    | nonterm -> true)

(* We execute a translation unit by executing its external declarations in
order. *)

op execTranslationUnit (state:State, tunit:TranslationUnit) : OC State =
  case tunit of
  | [] -> ok state
  | xdecl::xdecls ->
    {state' <- execExternalDeclaration (state, xdecl);
     execTranslationUnit (state', xdecls)}

(* Executing, in a state that satisfies the invariants, a translation unit that
satisfies the compile-time constraints w.r.t. the symbol table of the state,
does not yield an error. Furthermore, if a normal outcome occurs, the new state
satisfies the invariants and the symbol table of the new state is the one
inferred by the compile-time constraints. *)

theorem translation_unit_execution is
  fa (state:State, tunit:TranslationUnit, symtab:SymbolTable)
    invariants? state &&
    checkTranslationUnit (symbolTableOfState state, tunit) = Some symtab =>
    (case execTranslationUnit (state, tunit) of
    | ok state' -> invariants? state' && symtab = symbolTableOfState state'
    | error -> false
    | nonstd -> true
    | nonterm -> true)


%subsection (* Programs *)

(* Starting from the empty state, processing the translation unit of the program
yields the initial state of the program. *)

op emptyState : State =
  {storage    = {static = empty, automatic = [], outside = empty},
   typedefs   = empty,
   structures = empty,
   functions  = empty}

op initState (prg:Program) : OC State =
  execTranslationUnit (emptyState, prg)

theorem initState_no_outside_objects is
  fa (prg:Program, state:State)
    initState prg = ok state => empty? state.storage.outside

(* If a program satisfies all the compile-time constraints, executing its
translation unit does not yield an error. If an initial state is returned, it
satisfies the invariants and its symbol table is the one inferred by the
compile-time constraints. *)

theorem initial_state_invariants is
  fa (prg:Program, symtab:SymbolTable, state:State)
    checkProgram prg = Some symtab =>
    (case initState prg of
    | ok state' -> invariants? state && symtab = symbolTableOfState state'
    | error -> false
    | nonstd -> true
    | nonterm -> true)


%section (* Conclusion *)

(* We have formalized the syntax, constraints, and semantics of a subset of C.
This subset will be extended in the future. *)


%section (* Appendix: Isabelle proofs and lemmas *)

(* This appendix collects all the Isabelle proofs and lemmas for the theorems
and proofs obligations in the Specware formalization developed above. *)

proof Isa -verbatim
(*******************************************************************************
 There are at least 100 translation issues, some of them involving ambiguities
 that are very time-consuming to fix. Avoid running this file through the 
 translator until a significant number of new theorems has been proven. 

 After translation, it is best to copy the corrected versions of defs and
 theorems from the last C.thy-vxx file

******************************************************************************)
end-proof

% -------------------- section (* Environment *) --------------------------

proof Isa CHAR_BIT      [simp] end-proof
proof Isa UCHAR_MAX_VAL [simp]
  by (simp add: C__UCHAR_MAX_def)  
end-proof
proof Isa SCHAR_MAX     [simp] end-proof
proof Isa SCHAR_MIN     [simp] end-proof

proof Isa min_sizeof_short [simp] end-proof
proof Isa min_sizeof_int   [simp] end-proof
proof Isa min_sizeof_long  [simp] end-proof
proof Isa min_sizeof_llong [simp] end-proof

proof Isa min_short_bits  [simp]
  by (simp add: C__short_bits_def)
end-proof
proof Isa min_int_bits    [simp]
  by (simp add: C__int_bits_def)
end-proof
proof Isa min_long_bits   [simp]
  by (simp add: C__long_bits_def)
end-proof
proof Isa min_llong_bits  [simp]
  by (simp add: C__llong_bits_def)
end-proof

proof Isa min_USHRT_MAX [simp] 
  by (simp add: C__USHRT_MAX_def, 
      rule_tac y="2 ^ (2 * 8)" in less_le_trans, simp,
      simp only:  power_increasing_iff, simp)
end-proof 
proof Isa min_UINT_MAX [simp] 
  by (simp add: C__UINT_MAX_def, 
      rule_tac y="2 ^ (2 * 8)" in less_le_trans, simp,
      simp only:  power_increasing_iff, simp)
end-proof 
proof Isa min_ULONG_MAX [simp] 
  by (simp add: C__ULONG_MAX_def, 
      rule_tac y="2 ^ (4 * 8)" in less_le_trans, simp,
      simp only:  power_increasing_iff, simp)
end-proof 
proof Isa min_ULLONG_MAX [simp] 
   by (simp add: C__ULLONG_MAX_def,
       rule_tac y="2 ^ (8 * 8)" in less_le_trans, simp,
       simp only:  power_increasing_iff, simp)
end-proof 

proof Isa SHRT_MIN_Obligation_subtype  
  by (cut_tac C__min_short_bits, arith)
end-proof 
proof Isa INT_MIN_Obligation_subtype  
  by (cut_tac C__min_int_bits, arith)
end-proof 
proof Isa LONG_MIN_Obligation_subtype  
  by (cut_tac C__min_long_bits, arith)
end-proof 
proof Isa LLONG_MIN_Obligation_subtype  
  by (cut_tac C__min_llong_bits, arith)
end-proof 

proof Isa SHRT_MAX_Obligation_subtype  
  by (rule C__SHRT_MIN_Obligation_subtype)
end-proof 
proof Isa INT_MAX_Obligation_subtype  
  by (rule C__INT_MIN_Obligation_subtype)
end-proof 
proof Isa LONG_MAX_Obligation_subtype  
  by (rule C__LONG_MIN_Obligation_subtype)
end-proof 
proof Isa LLONG_MAX_Obligation_subtype  
  by (rule C__LLONG_MIN_Obligation_subtype)
end-proof 

proof Isa min_SHRT_MIN [simp]
  apply (simp add: C__SHRT_MIN_def, rule_tac y="2 ^ 15" in order_trans, simp)
  apply (simp only: power_increasing_iff)
  apply (cut_tac C__min_short_bits, arith)
end-proof
proof Isa min_INT_MIN [simp]
  apply (simp add: C__INT_MIN_def, rule_tac y="2 ^ 15" in order_trans, simp)
  apply (simp only: power_increasing_iff)
  apply (cut_tac C__min_int_bits, arith)
end-proof
proof Isa min_LONG_MIN [simp]
  apply (simp add: C__LONG_MIN_def, rule_tac y="2 ^ 31" in order_trans, simp)
  apply (simp only: power_increasing_iff)
  apply (cut_tac C__min_long_bits, arith)
end-proof
proof Isa min_LLONG_MIN [simp] 
  apply (simp add: C__LLONG_MIN_def, rule_tac y="2 ^ 63" in order_trans, simp)
  apply (simp only: power_increasing_iff)
  apply (cut_tac C__min_llong_bits, arith)
end-proof

proof Isa min_SHRT_MAX [simp]
  apply (simp add: C__SHRT_MAX_def, rule_tac y="2 ^ 15" in less_le_trans, simp)
  apply (simp only: power_increasing_iff)
  apply (cut_tac C__min_short_bits, arith)
end-proof
proof Isa min_INT_MAX [simp] 
  apply (simp add: C__INT_MAX_def, rule_tac y="2 ^ 15" in less_le_trans, simp)
  apply (simp only: power_increasing_iff)
  apply (cut_tac C__min_int_bits, arith)
end-proof
proof Isa min_LONG_MAX [simp] 
  apply (simp add: C__LONG_MAX_def, rule_tac y="2 ^ 31" in less_le_trans, simp)
  apply (simp only: power_increasing_iff)
  apply (cut_tac C__min_long_bits, arith)
end-proof
proof Isa min_LLONG_MAX [simp] 
  apply (simp add: C__LLONG_MAX_def, rule_tac y="2 ^ 63" in less_le_trans, simp)
  apply (simp only: power_increasing_iff)
  apply (cut_tac C__min_llong_bits, arith)
done

theorem C__min_USHRT_MAX2 [simp]:    "C__USHRT_MAX \<ge> 2 ^ 16 - 1"
  by (cut_tac C__min_USHRT_MAX, simp)
theorem C__min_UINT_MAX2 [simp]:     "C__UINT_MAX \<ge> 2 ^ 16 - 1"
  by (cut_tac C__min_UINT_MAX, simp)
theorem C__min_ULONG_MAX2 [simp]:    "C__ULONG_MAX \<ge> 2 ^ 32 - 1"
  by (cut_tac C__min_ULONG_MAX, simp)
theorem C__min_ULLONG_MAX2 [simp]:   "C__ULLONG_MAX \<ge> 2 ^ 64 - 1"
  by (cut_tac C__min_ULLONG_MAX, simp)

(******************* I need these often ***************************************)
lemmas C__Consts = C__short_bits_def C__int_bits_def
                   C__long_bits_def C__llong_bits_def                    

lemmas C__MinMax = C__CHAR_MIN_def C__CHAR_MAX_def 
                   C__SHRT_MIN_def C__INT_MIN_def 
                   C__LONG_MIN_def C__LLONG_MIN_def
                   C__SHRT_MAX_def C__INT_MAX_def 
                   C__LONG_MAX_def C__LLONG_MAX_def
                   C__USHRT_MAX_def C__UINT_MAX_def 
                   C__ULONG_MAX_def C__ULLONG_MAX_def
                   C__plainCharsAreUnsigned_def
(******************************************************************************)

lemma C__CHAR_MIN_alt [simp]: 
  "C__CHAR_MIN = (if C__plainCharsAreUnsigned then 0 else C__SCHAR_MIN)"
  apply (simp add: C__plainCharsAreUnsigned_def C__CHAR_MIN_def)

(******************************************************************************)
end-proof


proof Isa sizeof_short_int   [simp] end-proof
proof Isa sizeof_int_long    [simp] end-proof
proof Isa sizeof_long_llong  [simp] 

(******************************************************************************)
(** need more mix and match lemmas - the axioms alone aren't sufficient **)

lemma C__bits_short_int [simp]:   "C__short_bits \<le> C__int_bits"
  by (simp add: C__Consts)
lemma C__bits_int_long [simp]:    "C__int_bits \<le> C__long_bits"
  by (simp add: C__Consts)
lemma C__bits_long_llong [simp]:  "C__long_bits \<le> C__llong_bits"
  by (simp add: C__Consts)
lemma C__bits_int_llong [simp]:   "C__int_bits \<le> C__llong_bits"
  by (rule_tac j="C__long_bits" in le_trans, simp_all)
lemma C__bits_short_long [simp]:  "C__int_bits \<le> C__long_bits"
  by (rule_tac j="C__int_bits" in le_trans, simp_all)
lemma C__bits_short_llong [simp]: "C__int_bits \<le> C__llong_bits"
  by (rule_tac j="C__int_bits" in le_trans, simp_all)
lemma C__bits_byte_short [simp]:  "8 \<le> C__short_bits"
  by (rule_tac j=16 in le_trans, simp_all)
lemma C__bits_byte_int [simp]:    "8 \<le> C__int_bits"
  by (rule_tac j=16 in le_trans, simp_all)
lemma C__bits_byte_long [simp]:   "8 \<le> C__long_bits"
  by (rule_tac j=32 in le_trans, simp_all)
lemma C__bits_byte_llong [simp]:  "8 \<le> C__llong_bits"
  by (rule_tac j=64 in le_trans, simp_all)

lemma C__bits_byte_neq_short [simp]:  "8 \<noteq> C__short_bits"
  by (cut_tac C__min_short_bits, simp (no_asm_simp))
lemma C__bits_byte_neq_int [simp]:    "8 \<noteq> C__int_bits"
  by (cut_tac C__min_int_bits, simp (no_asm_simp))
lemma C__bits_byte_neq_long [simp]:   "8 \<noteq> C__long_bits"
  by (cut_tac C__min_long_bits, simp (no_asm_simp))
lemma C__bits_byte_neq_llong [simp]:  "8 \<noteq> C__llong_bits"
  by (cut_tac C__min_llong_bits, simp (no_asm_simp))


lemma C__sizeof_short_pos [simp]:           "0 < C__sizeof_short"
  by (cut_tac C__min_sizeof_short, arith)
lemma C__sizeof_int_pos [simp]:             "0 < C__sizeof_int"
  by (cut_tac C__min_sizeof_int, arith)
lemma C__sizeof_long_pos [simp]:            "0 < C__sizeof_long"
  by (cut_tac C__min_sizeof_long, arith)
lemma C__sizeof_llong_pos [simp]:           "0 < C__sizeof_llong"
  by (cut_tac C__min_sizeof_llong, arith)
 
lemma C__short_bits_gt_1 [simp]:            "1 <  C__short_bits"
  by (cut_tac C__min_short_bits, simp (no_asm_simp))
lemma C__int_bits_gt_1 [simp]:              "1 <  C__int_bits"
  by (cut_tac C__min_int_bits, simp (no_asm_simp))
lemma C__long_bits_gt_1 [simp]:             "1 <  C__long_bits"
  by (cut_tac C__min_long_bits, simp (no_asm_simp))
lemma C__llong_bits_gt_1 [simp]:            "1 <  C__llong_bits"
  by (cut_tac C__min_llong_bits, simp (no_asm_simp))

lemma C__short_bits_pos [simp]:             "0 < C__short_bits"
  by (cut_tac C__min_short_bits, simp (no_asm_simp))
lemma C__int_bits_pos [simp]:               "0 < C__int_bits"
  by (cut_tac C__min_int_bits, simp (no_asm_simp))
lemma C__long_bits_pos [simp]:              "0 < C__long_bits"
  by (cut_tac C__min_long_bits, simp (no_asm_simp))
lemma C__llong_bits_pos [simp]:             "0 < C__llong_bits"
 by (cut_tac C__min_llong_bits, simp (no_asm_simp))

lemma C__short_bits_neq0 [simp]:             "C__short_bits \<noteq> 0"
  by (cut_tac C__min_short_bits, simp (no_asm_simp))
lemma C__int_bits_neq0 [simp]:               "C__int_bits \<noteq> 0"
  by (cut_tac C__min_int_bits, simp (no_asm_simp))
lemma C__long_bits_neq0 [simp]:              "C__long_bits \<noteq> 0"
  by (cut_tac C__min_long_bits, simp (no_asm_simp))
lemma C__llong_bits_neq0 [simp]:             "C__llong_bits \<noteq> 0"
 by (cut_tac C__min_llong_bits, simp (no_asm_simp))


(******************************************************************************)

theorem C__SHRT_USHRT_MAX_eq [simp]:  "2 * C__SHRT_MAX + 1 = C__USHRT_MAX"
  by (subgoal_tac "2 * C__SHRT_MAX = C__USHRT_MAX - 1",
      cut_tac C__min_USHRT_MAX2, simp,
      simp add: C__MinMax nat_diff_distrib nat_power_eq diff_mult_distrib2 
                power_Suc[symmetric])
theorem C__INT_UINT_MAX_eq [simp]:  "2 * C__INT_MAX + 1 = C__UINT_MAX"
  by (subgoal_tac "2 * C__INT_MAX = C__UINT_MAX - 1",
      cut_tac C__min_UINT_MAX2, simp,
      simp add: C__MinMax nat_diff_distrib nat_power_eq diff_mult_distrib2 
                power_Suc[symmetric])
theorem C__LONG_ULONG_MAX_eq [simp]:  "2 * C__LONG_MAX + 1 = C__ULONG_MAX"
  by (subgoal_tac "2 * C__LONG_MAX = C__ULONG_MAX - 1",
      cut_tac C__min_ULONG_MAX2, simp,
      simp add: C__MinMax nat_diff_distrib nat_power_eq diff_mult_distrib2 
                power_Suc[symmetric])
theorem C__LLONG_ULLONG_MAX_eq [simp]:  "2 * C__LLONG_MAX + 1 = C__ULLONG_MAX"
  by (subgoal_tac "2 * C__LLONG_MAX = C__ULLONG_MAX - 1",
      cut_tac C__min_ULLONG_MAX2, simp,
      simp add: C__MinMax nat_diff_distrib nat_power_eq diff_mult_distrib2 
                power_Suc[symmetric])

(******************************************************************************)


theorem C__SHRT_USHRT_MAX [simp]:        "C__SHRT_MAX < C__USHRT_MAX"
  by (simp add:  C__SHRT_USHRT_MAX_eq [symmetric])
theorem C__INT_UINT_MAX [simp]:          "C__INT_MAX < C__UINT_MAX"
  by (simp add:  C__INT_UINT_MAX_eq [symmetric])
theorem C__LONG_ULONG_MAX [simp]:        "C__LONG_MAX < C__ULONG_MAX"
  by (simp add:  C__LONG_ULONG_MAX_eq [symmetric])
theorem C__LLONG_ULLONG_MAX [simp]:      "C__LLONG_MAX < C__ULLONG_MAX"
  by (simp add:  C__LLONG_ULLONG_MAX_eq [symmetric])

theorem C__USHRT_UINT_MAX [simp]:        "C__USHRT_MAX \<le> C__UINT_MAX"
  by (simp add: C__MinMax, subst nat_le_eq_zle, simp, simp del: zle_diff1_eq)
theorem C__SHRT_INT_MAX [simp]:          "C__SHRT_MAX \<le> C__INT_MAX"
  by (simp add: C__MinMax, subst nat_le_eq_zle, simp, 
      simp del: zle_diff1_eq  add: diff_le_mono)
theorem C__SHRT_UINT_MAX [simp]:          "C__SHRT_MAX < C__UINT_MAX"
  by (rule_tac y=C__INT_MAX in le_less_trans, simp_all)

theorem C__UINT_ULONG_MAX [simp]:        "C__UINT_MAX \<le> C__ULONG_MAX"
  by (simp add: C__MinMax, subst nat_le_eq_zle, simp, simp del: zle_diff1_eq)
theorem C__INT_LONG_MAX [simp]:          "C__INT_MAX \<le> C__LONG_MAX"
  by (simp add: C__MinMax, subst nat_le_eq_zle, simp, 
      simp del: zle_diff1_eq  add: diff_le_mono)
theorem C__INT_ULONG_MAX [simp]:         "C__INT_MAX < C__ULONG_MAX"
  by (rule_tac y=C__LONG_MAX in le_less_trans, simp_all)
theorem C__USHRT_ULONG_MAX [simp]:       "C__USHRT_MAX \<le> C__ULONG_MAX"
  by (rule_tac j=C__UINT_MAX in le_trans, simp_all)
theorem C__SHRT_LONG_MAX [simp]:         "C__SHRT_MAX \<le> C__LONG_MAX"
  by (rule_tac j=C__INT_MAX in le_trans, simp_all)
theorem C__SHRT_ULONG_MAX [simp]:        "C__SHRT_MAX < C__ULONG_MAX"
  by (rule_tac y=C__LONG_MAX in le_less_trans, simp_all)

theorem C__ULONG_ULLONG_MAX [simp]:      "C__ULONG_MAX \<le> C__ULLONG_MAX"
  by (simp add: C__MinMax, subst nat_le_eq_zle, simp, simp del: zle_diff1_eq)
theorem C__LONG_LLONG_MAX [simp]:        "C__LONG_MAX \<le> C__LLONG_MAX"
  by (simp add: C__MinMax, subst nat_le_eq_zle, simp, 
      simp del: zle_diff1_eq  add: diff_le_mono)
theorem C__LONG_ULLONG_MAX [simp]:       "C__LONG_MAX < C__ULLONG_MAX"
  by (rule_tac y=C__LLONG_MAX in le_less_trans, simp_all)

theorem C__UINT_ULLONG_MAX [simp]:       "C__UINT_MAX \<le> C__ULLONG_MAX"
  by (rule_tac j=C__ULONG_MAX in le_trans, simp_all)
theorem C__INT_LLONG_MAX [simp]:         "C__INT_MAX \<le> C__LLONG_MAX"
  by (rule_tac j=C__LONG_MAX in le_trans, simp_all)
theorem C__INT_ULLONG_MAX [simp]:        "C__INT_MAX < C__ULLONG_MAX"
  by (rule_tac y=C__LLONG_MAX in le_less_trans, simp_all)
theorem C__USHRT_ULLONG_MAX [simp]:      "C__USHRT_MAX \<le> C__ULLONG_MAX"
  by (rule_tac j=C__ULONG_MAX in le_trans, simp_all)
theorem C__SHRT_LLONG_MAX [simp]:        "C__SHRT_MAX \<le> C__LLONG_MAX"
  by (rule_tac j=C__LONG_MAX in le_trans, simp_all)
theorem C__SHRT_ULLONG_MAX [simp]:       "C__SHRT_MAX < C__ULLONG_MAX"
  by (rule_tac y=C__LLONG_MAX in le_less_trans, simp_all)


lemma C__INT_SHRT_MIN [simp]:            "C__INT_MIN \<le> C__SHRT_MIN"
  by (simp add: C__MinMax diff_le_mono)
theorem C__LONG_INT_MIN [simp]:          "C__LONG_MIN \<le> C__INT_MIN"
  by (simp add: C__MinMax diff_le_mono)
theorem C__LLONG_LONG_MIN [simp]:        "C__LLONG_MIN \<le> C__LONG_MIN"
  by (simp add: C__MinMax diff_le_mono)
lemma C__LONG_SHRT_MIN [simp]:            "C__LONG_MIN \<le> C__SHRT_MIN"
  by (rule_tac y=C__INT_MIN in order_trans, simp_all)
lemma C__LLONG_SHRT_MIN [simp]:           "C__LLONG_MIN \<le> C__SHRT_MIN"
  by (rule_tac y=C__LONG_MIN in order_trans, simp_all)
lemma C__LLONG_INT_MIN [simp]:            "C__LLONG_MIN \<le> C__INT_MIN"
  by (rule_tac y=C__LONG_MIN in order_trans, simp_all)

(******************************************************************************)

end-proof


% -------------------- section (* Syntax *) --------------------------------

proof Isa Identifier -typedef 
  by (rule_tac x="''a''" in exI, 
      simp add: C__identifier_p_def C__ppIdentifier_p_def C__keywords_def 
                C__identifierNonDigit_p_def C__digit_p_def C__nonDigit_p_def
                mem_def Un_def Collect_def  nat_of_char_def,
      auto simp only: insert_def, auto) 
end-proof

theorem Identifier_identifier is   fa (cid:Identifier) identifier? cid

proof Isa Identifier_identifier [simp]
  by (case_tac "cid", 
      simp add: Abs_C__Identifier_inverse C__Identifier_def 
                Collect_def mem_def)

(******************************************************************************)
lemmas Identifier_defs = C__identifier_p_def C__ppIdentifier_p_def 
                         C__keywords_def C__digit_p_def
                         C__identifierNonDigit_p_def C__nonDigit_p_def
                         mem_def Un_def Collect_def nat_of_char_def

declare Rep_C__Identifier_inverse [simp add]
declare Abs_C__Identifier_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_C__Identifier_simp [simp]:
  "\<lbrakk>C__identifier_p y\<rbrakk> \<Longrightarrow>  (Rep_C__Identifier x = y) = (x = Abs_C__Identifier y)"
by (subst Abs_C__Identifier_inject [symmetric],
    simp add: Rep_C__Identifier,
    simp add: C__Identifier_def Collect_def mem_def,
    simp add: Rep_C__Identifier_inverse)

lemma Abs_C__Identifier_not_in_singleton [simp]:
  "\<lbrakk>C__identifier_p id1; C__identifier_p id2\<rbrakk> \<Longrightarrow> 
   (Abs_C__Identifier id1 \<in> dom (Map__update Map.empty (Abs_C__Identifier id2) val))
    = (id1 = id2)"
by (simp add: Map__update_def dom_if Abs_C__Identifier_inject C__Identifier_def)

lemma C__Identifiers__Order__linearOrder_p [simp]:
  "Order__linearOrder_p  
    (\<lambda>(x, y). Rep_C__Identifier x <=_s Rep_C__Identifier y)"
 apply (cut_tac Order__linearOrder_p_le_s)
 apply (auto simp add: Order__linearOrder_p_def Order__partialOrder_p_def 
                       Order__preOrder_p_def mem_def)
 apply (rotate_tac -1, thin_tac ?P, thin_tac ?P, thin_tac ?P,
        simp add: refl_on_def mem_def)
 (* Trans *)
 apply (thin_tac ?P, thin_tac ?P, thin_tac ?P,
        simp add: trans_def, clarify)
 apply (drule_tac x="Rep_C__Identifier x" in spec, rotate_tac -1)
 apply (drule_tac x="Rep_C__Identifier y" in spec, rotate_tac -1)
 apply (drule mp, simp add: mem_def)
 apply (drule_tac x="Rep_C__Identifier z" in spec, rotate_tac -1)
 apply (drule mp, simp_all add: mem_def)
 (* Antisym *)
 apply (rotate_tac -2, thin_tac ?P, thin_tac ?P, thin_tac ?P,
        simp add: antisym_def mem_def, clarify)
 apply (drule_tac x="Rep_C__Identifier x" in spec, rotate_tac -1)
 apply (drule_tac x="Rep_C__Identifier y" in spec, rotate_tac -1)
 apply auto
(******************************************************************************)

end-proof

proof Isa IntegerConstant -typedef
  by (rule_tac x="''1''" in exI, simp add: C__integerConstant_p_def 
                                           Collect_def mem_def,
      rule_tac x="''1''" in exI, rule_tac exI,
      auto simp add: C__decimalConstant_p_def C__digit_p_def nat_of_char_def
                     C__integerSuffixOpt_p_def C__lengthSuffix_p_def
                     C__signSuffix_p_def C__unsignedSuffix_p_def  )
end-proof

theorem IntegerConstant_constant is   fa (c:IntegerConstant) integerConstant? c

proof Isa IntegerConstant_constant [simp]
  by (case_tac "c", 
      simp add: Abs_C__IntegerConstant_inverse C__IntegerConstant_def 
                Collect_def mem_def)

(******************************************************************************)
declare Rep_C__IntegerConstant_inverse [simp add]
declare Abs_C__IntegerConstant_inverse [simp add]

lemmas C__IntConsts = C__decimalConstant_p_def C__digit_p_def 
                      C__octalConstant_p_def   C__octalDigit_p_def 
                      C__hexadecimalConstant_p_def C__hexadecimalDigit_p_def
                      C__integerConstant_p_def nat_of_char_def
     
lemmas C__IntSuffix = C__integerSuffixOpt_p_def 
                      C__lengthSuffix_p_def C__signSuffix_p_def
                      C__unsignedSuffix_p_def C__longLongSuffix_p_def 
                      C__longSuffix_p_def 
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_C__IntegerConstant_simp [simp]:
  "\<lbrakk>C__integerConstant_p y\<rbrakk> \<Longrightarrow>  (Rep_C__IntegerConstant x = y) = (x = Abs_C__IntegerConstant y)"
apply (subst Abs_C__IntegerConstant_inject [symmetric],
       simp add: Rep_C__IntegerConstant,
       simp add: C__IntegerConstant_def Collect_def mem_def,
       simp add: Rep_C__IntegerConstant_inverse)
(******************************************************************************)

end-proof

proof Isa unsuffixedIntegerConstant_Obligation_the
  apply (case_tac "c", 
         simp add: C__IntegerConstant_def C__integerConstant_p_def 
                   Collect_def mem_def,
         clarify)
  apply (rule_tac a=const in ex1I, simp, clarify)
  apply (simp add:  C__integerSuffixOpt_p_def C__lengthSuffix_p_def
                    C__signSuffix_p_def C__unsignedSuffix_p_def 
                    C__longSuffix_p_def C__longLongSuffix_p_def,
        clarify)
  (* in principle auto could do this but there are way too many cases
     ... need a lemma *)
  apply (rotate_tac 5, erule disjE, simp_all)
  apply (thin_tac "suffix = ?t")
  apply (rotate_tac 1, erule disjE, simp_all)
  apply (thin_tac "suffixa = ?t")
  apply (rotate_tac 3, erule disjE, simp_all)
  apply (erule disjE, simp_all)
  apply (erule disjE, erule disjE, simp)
  sorry
end-proof

% ------------------- section (* Constraints *) --------------------------------

% ------------------- section (* Types *)       --------------------------------



proof Isa minOfIntegerType_Obligation_exhaustive 
  by (auto simp add: C__integerType_p_def 
           C__signedIntegerType_p_def 
           C__unsignedIntegerType_p_def
           C__standardSignedIntegerType_p_def 
           C__standardUnsignedIntegerType_p_def)
end-proof

proof Isa maxOfIntegerType_Obligation_exhaustive 
  by (simp add: C__minOfIntegerType_Obligation_exhaustive)
end-proof


% ------------------------------------------------------------

% ----------------------------------------------------------------------------
% Right now we cannot translate the parameterized type of FiniteSet
% As a temporary fix I introduce an instantiated Version 

type FiniteSetInt = (Set Int | finite?)
proof Isa -typedef 
  by  (rule_tac x="{}" in exI, simp add: Collect_def mem_def)
end-proof

theorem FiniteSetInt_finite is   fa (ints:FiniteSetInt) finite? ints

% ----------------------------------------------------------------------------

proof Isa FiniteSetInt_finite [simp]
  by (case_tac "ints", 
      simp add: Abs_C__FiniteSetInt_inverse C__FiniteSetInt_def 
                Collect_def mem_def)


(*****************************************************************************)
(********* I may need these later but they're tedious to prove ***************
 ********* Move after  C__unsuffixedIntegerConstant            ***************

lemma C__unsuffixedIntegerConstant_nonnil [simp]:
  "C__unsuffixedIntegerConstant c = unsuffixed
  \<Longrightarrow> unsuffixed \<noteq>  []"
  apply (drule sym, simp add: C__unsuffixedIntegerConstant_def, thin_tac ?P)
  apply (rule the1I2, rule C__unsuffixedIntegerConstant_Obligation_the, auto)
  apply (induct c, 
         simp add: mem_def C__IntegerConstant_def Collect_def 
                           C__integerConstant_p_def)
  apply clarify

**** too tedious **

lemma C__unsuffixedIntegerConstant_digits [simp]:
  "C__unsuffixedIntegerConstant c = unsuffixed
  \<Longrightarrow> \<forall>x\<in>set unsuffixed. C__digit_p x"
  apply (drule sym, simp add: C__unsuffixedIntegerConstant_def, thin_tac ?P)
  apply (rule the1I2, rule C__unsuffixedIntegerConstant_Obligation_the, auto)
  apply (induct c, 
         simp add: mem_def C__IntegerConstant_def Collect_def 
                           C__integerConstant_p_def)
  apply clarify
*******************************************************************************)


(*******************************************************************************
  Ideally the following should come right after C__typeBits_def
   but we lack the means to place it there, so it comes at the earliest
   possible position after that
*******************************************************************************)

(******************* I need these often ***************************************)

lemmas C__BitTypes = C__typeBits_def 
                     C__characterType_p_def 
                     C__shortType_p_def 
                     C__intType_p_def 
                     C__longType_p_def

lemmas C__IntTypes = C__integerType_p_def 
                     C__signedIntegerType_p_def 
                     C__standardSignedIntegerType_p_def
                     C__unsignedIntegerType_p_def
                     C__standardUnsignedIntegerType_p_def
                     C__arithmeticType_p_def 
(******************************************************************************)

lemma C__typeBits_ge_8 [simp]:    "8 \<le> C__typeBits ty"
 by (cut_tac C__min_short_bits, cut_tac C__min_int_bits,
     cut_tac C__min_long_bits, cut_tac C__min_llong_bits,
     auto simp add: C__typeBits_def)

lemma C__typeBits_pos [simp]:     "0 < C__typeBits ty"
 by (simp add: C__typeBits_def)

lemma C__typeBits_char [simp]:    "C__typeBits C__Type__char = 8"
 by (simp add: C__BitTypes) 
lemma C__typeBits_schar [simp]:   "C__typeBits C__Type__schar = 8"
 by (simp add: C__BitTypes) 
lemma C__typeBits_uchar [simp]:   "C__typeBits C__Type__uchar = 8"
 by (simp add: C__BitTypes) 

lemma C__typeBits_sshort [simp]:  "C__typeBits C__Type__sshort = C__short_bits"
 by (simp add: C__BitTypes) 
lemma C__typeBits_ushort [simp]:  "C__typeBits C__Type__ushort = C__short_bits"
 by (simp add: C__BitTypes) 

lemma C__typeBits_sint [simp]:    "C__typeBits C__Type__sint = C__int_bits"
 by (simp add: C__BitTypes) 
lemma C__typeBits_uint [simp]:    "C__typeBits C__Type__uint = C__int_bits"
 by (simp add: C__BitTypes) 

lemma C__typeBits_slong [simp]:   "C__typeBits C__Type__slong = C__long_bits"
 by (simp add: C__BitTypes) 
lemma C__typeBits_ulong [simp]:   "C__typeBits C__Type__ulong = C__long_bits"
 by (simp add: C__BitTypes) 
 
lemma C__typeBits_sllong [simp]:  "C__typeBits C__Type__sllong = C__llong_bits"
 by (simp add: C__BitTypes) 
lemma C__typeBits_ullong [simp]:  "C__typeBits C__Type__ullong = C__llong_bits"
 by (simp add: C__BitTypes) 

lemma C__integerType_char [simp]:   "C__integerType_p C__Type__char"
 by (simp add: C__IntTypes) 
lemma C__integerType_schar [simp]:  "C__integerType_p C__Type__schar"
 by (simp add: C__IntTypes) 
lemma C__integerType_uchar [simp]:  "C__integerType_p C__Type__uchar"
 by (simp add: C__IntTypes) 

lemma C__integerType_sshort [simp]: "C__integerType_p C__Type__sshort"
 by (simp add: C__IntTypes) 
lemma C__integerType_ushort [simp]: "C__integerType_p C__Type__ushort"
 by (simp add: C__IntTypes) 

lemma C__integerType_sint [simp]:   "C__integerType_p C__Type__sint"
 by (simp add: C__IntTypes) 
lemma C__integerType_uint [simp]:   "C__integerType_p C__Type__uint"
 by (simp add: C__IntTypes) 

lemma C__integerType_slong [simp]:  "C__integerType_p C__Type__slong"
 by (simp add: C__IntTypes) 
lemma C__integerType_ulong [simp]:  "C__integerType_p C__Type__ulong"
 by (simp add: C__IntTypes) 
 
lemma C__integerType_sllong [simp]: "C__integerType_p C__Type__sllong"
 by (simp add: C__IntTypes) 
lemma C__integerType_ullong [simp]: "C__integerType_p C__Type__ullong"
 by (simp add: C__IntTypes) 

theorem C__integerType_cases:
  "\<lbrakk>C__integerType_p ty\<rbrakk> \<Longrightarrow> 
   ty = C__Type__char 
     \<or> (ty = C__Type__uchar 
      \<or> (ty = C__Type__schar 
       \<or> (ty = C__Type__ushort 
        \<or> (ty = C__Type__sshort 
         \<or> (ty = C__Type__uint 
          \<or> (ty = C__Type__sint 
           \<or> (ty = C__Type__ulong 
            \<or> (ty = C__Type__slong 
             \<or> (ty = C__Type__ullong
               \<or> ty = C__Type__sllong)))))))))"
  by (auto simp add: C__IntTypes)

theorem C__unsigned_cases:
  "\<lbrakk>C__unsignedIntegerType_p ty \<or>
    ty = C__Type__char \<and> C__plainCharsAreUnsigned \<rbrakk> \<Longrightarrow> 
    ty = C__Type__char \<and> C__plainCharsAreUnsigned 
     \<or> (ty = C__Type__uchar 
      \<or> (ty = C__Type__ushort 
        \<or> (ty = C__Type__uint 
          \<or> (ty = C__Type__ulong 
            \<or> ty = C__Type__ullong))))"
   by (auto simp add: C__IntTypes)  

theorem C__unsigned_cases2:
  "\<lbrakk>C__unsignedIntegerType_p ty \<or>
    C__plainCharsAreUnsigned \<and> ty = C__Type__char\<rbrakk> \<Longrightarrow> 
    ty = C__Type__char \<and> C__plainCharsAreUnsigned 
     \<or> (ty = C__Type__uchar 
      \<or> (ty = C__Type__ushort 
        \<or> (ty = C__Type__uint 
          \<or> (ty = C__Type__ulong 
            \<or> ty = C__Type__ullong))))"
   by (auto simp add: C__IntTypes)  


theorem C__signed_cases:
  "\<lbrakk>C__signedIntegerType_p ty \<or>
    ty = C__Type__char \<and> C__plainCharsAreSigned \<rbrakk> \<Longrightarrow> 
    ty = C__Type__char \<and> C__plainCharsAreSigned 
     \<or> (ty = C__Type__schar 
      \<or> (ty = C__Type__sshort 
        \<or> (ty = C__Type__sint 
          \<or> (ty = C__Type__slong 
            \<or> ty = C__Type__sllong))))"
   by (auto simp add: C__IntTypes)  

theorem C__signed_cases2:
  "\<lbrakk>C__integerType_p ty; \<not>C__unsignedIntegerType_p ty;
    C__plainCharsAreUnsigned \<longrightarrow> ty \<noteq> C__Type__char\<rbrakk> \<Longrightarrow> 
    ty = C__Type__char \<and> C__plainCharsAreSigned 
     \<or> (ty = C__Type__schar 
      \<or> (ty = C__Type__sshort 
        \<or> (ty = C__Type__sint 
          \<or> (ty = C__Type__slong 
            \<or> ty = C__Type__sllong))))"
   by (auto simp add: C__IntTypes C__plainCharsAreUnsigned_def)


theorem C__unsigned_cases_int [simp]:
  "\<lbrakk>C__unsignedIntegerType_p ty \<or>
    C__plainCharsAreUnsigned \<and> ty = C__Type__char\<rbrakk> \<Longrightarrow> 
    C__integerType_p ty"
 by (auto simp add: C__integerType_p_def)

theorem C__unsigned_cases_int2 [simp]:
  "\<lbrakk>C__unsignedIntegerType_p ty \<or>
    ty = C__Type__char \<and> C__plainCharsAreUnsigned\<rbrakk> \<Longrightarrow> 
    C__integerType_p ty"
 by (auto simp add: C__integerType_p_def)

lemma C__Type__char_not_signedIntegerType [simp]:
   "C__signedIntegerType_p C__Type__char = False"
   by (simp add: C__IntTypes)

lemma C__Type__char_not_unsignedIntegerType [simp]:
   "C__unsignedIntegerType_p C__Type__char = False"
   by (simp add: C__IntTypes)


(******************************************************************************)

lemma C__IntegerType_min_le_zero:
  "\<lbrakk>C__integerType_p ty\<rbrakk> \<Longrightarrow>  C__minOfIntegerType ty \<le> 0"
 by (cases ty, simp_all add: C__MinMax C__IntTypes)

lemma C__IntegerType_min_le_of_nat [simp]:
   "\<lbrakk>C__integerType_p ty\<rbrakk> \<Longrightarrow> C__minOfIntegerType ty \<le> int i"
  by (drule C__IntegerType_min_le_zero, simp add: le_trans)

lemma C__IntegerType_max_gt_zero:
  "\<lbrakk>C__integerType_p ty\<rbrakk> \<Longrightarrow>  C__maxOfIntegerType ty > 0"
 apply (cases ty, simp_all add: C__IntTypes)
 apply (simp add: C__MinMax) 
 apply (cut_tac C__min_INT_MAX, simp)
 apply (cut_tac C__min_LLONG_MAX, simp)
 apply (cut_tac C__min_LONG_MAX, simp)
 apply (cut_tac C__min_SHRT_MAX, simp)
 apply (cut_tac C__min_UINT_MAX, simp)
 apply (cut_tac C__min_ULLONG_MAX, simp)
 apply (cut_tac C__min_ULONG_MAX, simp)
 apply (cut_tac C__min_USHRT_MAX, simp)
done

lemma C__IntegerType_max_suc_ge_zero [simp]:
  "\<lbrakk>C__integerType_p ty\<rbrakk> \<Longrightarrow>  0 \<le> C__maxOfIntegerType ty + 1"
 by (frule C__IntegerType_max_gt_zero, simp)


lemma C__minOfIntegerType_unsigned [simp]:
 "\<lbrakk>C__unsignedIntegerType_p ty \<or>
   ty = C__Type__char \<and> C__plainCharsAreUnsigned \<rbrakk>
   \<Longrightarrow> C__minOfIntegerType ty = 0"
  by (cases ty, simp_all add: C__IntTypes C__MinMax)


lemma C__minOfIntegerType_signed [simp]:
  "\<lbrakk>C__integerType_p ty; \<not>C__unsignedIntegerType_p ty;
    C__plainCharsAreUnsigned \<longrightarrow> ty \<noteq> C__Type__char\<rbrakk>
    \<Longrightarrow> C__minOfIntegerType ty = - (2 ^ (C__typeBits ty - 1))"
  by (cases ty, simp_all add: C__IntTypes C__MinMax)

lemma C__minOfIntegerType_signed2 [simp]:
  "\<lbrakk>C__signedIntegerType_p ty \<or>
    ty = C__Type__char \<and> C__plainCharsAreSigned\<rbrakk>
    \<Longrightarrow> C__minOfIntegerType ty = - (2 ^ (C__typeBits ty - 1))"
  by (cases ty, simp_all add: C__IntTypes C__MinMax)


lemma C__maxOfIntegerType_unsigned [simp]:
  "\<lbrakk>C__unsignedIntegerType_p ty \<or>
   ty = C__Type__char \<and> C__plainCharsAreUnsigned \<rbrakk> \<Longrightarrow> 
   C__maxOfIntegerType ty = 2 ^ C__typeBits ty - 1"
  by (cases ty, simp_all add: C__IntTypes C__MinMax)

lemma C__maxOfIntegerType_signed [simp]:
  "\<lbrakk>C__integerType_p ty; \<not>C__unsignedIntegerType_p ty;
    C__plainCharsAreUnsigned \<longrightarrow> ty \<noteq> C__Type__char\<rbrakk>
    \<Longrightarrow> C__maxOfIntegerType ty = 2 ^ (C__typeBits ty - 1) - 1"
  by (cases ty, simp_all add: C__IntTypes C__MinMax)

lemma C__maxOfIntegerType_signed2 [simp]:
  "\<lbrakk>C__signedIntegerType_p ty \<or>
    ty = C__Type__char \<and> C__plainCharsAreSigned\<rbrakk>
    \<Longrightarrow> C__maxOfIntegerType ty = 2 ^ (C__typeBits ty - 1) - 1"
  by (cases ty, simp_all add: C__IntTypes C__MinMax)


(******************************************************************************)
declare Rep_C__FiniteSetInt_inverse [simp add]
declare Abs_C__FiniteSetInt_inverse [simp add]
(******************************************************************************)

(* Here is a very specific form that I need *)

lemma Rep_C__FiniteSetInt_simp [simp]:
  "\<lbrakk>finite y\<rbrakk> \<Longrightarrow>  (Rep_C__FiniteSetInt x = y) = (x = Abs_C__FiniteSetInt y)"
  by (subst Abs_C__FiniteSetInt_inject [symmetric],
      simp add: Rep_C__FiniteSetInt,
      simp add: C__FiniteSetInt_def Collect_def mem_def,
      simp add: Rep_C__FiniteSetInt_inverse)

lemma C__FiniteSetInt_union [simp]: 
  "Rep_C__FiniteSetInt (Abs_C__FiniteSetInt 
           (Rep_C__FiniteSetInt types1 \<union> Rep_C__FiniteSetInt types2))
     = (Rep_C__FiniteSetInt types1 \<union> Rep_C__FiniteSetInt types2)"
  by (simp add: Abs_C__FiniteSetInt_inverse C__FiniteSetInt_def mem_def)

lemma C__FiniteSetInt_single [simp]: 
  "Rep_C__FiniteSetInt (Abs_C__FiniteSetInt {t}) = {t}"
  by (simp add: Abs_C__FiniteSetInt_inverse C__FiniteSetInt_def mem_def)

lemma C__FiniteSetInt_insert [simp]: 
  "Abs_C__FiniteSetInt (Rep_C__FiniteSetInt types \<union>  Rep_C__FiniteSetInt (Abs_C__FiniteSetInt {t}))
     = Abs_C__FiniteSetInt (insert t (Rep_C__FiniteSetInt types))"
  by auto

lemma C__FiniteSetInt_insert2 [simp]: 
  " Rep_C__FiniteSetInt (Abs_C__FiniteSetInt 
        (insert t (Rep_C__FiniteSetInt types)))
    = insert t (Rep_C__FiniteSetInt types)"
  apply auto
(******************************************************************************)


(******************************************************************************)

end-proof

proof Isa rangeOfIntegerType_Obligation_subtype
  by (rule_tac t="\<lambda>x. ?l \<le> x \<and> x \<le> ?u"
          and  s="{?l..?u}" in subst, simp_all, 
      auto simp add: atLeastAtMost_def atLeast_def atMost_def mem_def)
end-proof

proof Isa correspondingUnsignedOf_Obligation_exhaustive
  by (simp add: C__IntTypes)

(******************************************************************************)

lemma C__rangeOfIntegerType_unsigned:
  "\<lbrakk>C__unsignedIntegerType_p ty \<or>
   ty = C__Type__char \<and> C__plainCharsAreUnsigned \<rbrakk> \<Longrightarrow> 
   (i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty))
   = (0 \<le> i \<and> i < 2 ^ C__typeBits ty)"
   by (simp add: C__rangeOfIntegerType_def  
                 C__rangeOfIntegerType_Obligation_subtype
                 C__FiniteSetInt_def,
       simp add: mem_def)

lemma C__rangeOfIntegerType_unsigned1:
  "\<lbrakk>C__unsignedIntegerType_p ty \<or>
   C__plainCharsAreUnsigned \<and> ty = C__Type__char\<rbrakk> \<Longrightarrow> 
   (i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty))
   = (0 \<le> i \<and> i < 2 ^ C__typeBits ty)"
   by (auto simp add: C__rangeOfIntegerType_unsigned)

lemma C__rangeOfIntegerType_unsigned2:
  "\<lbrakk>C__unsignedIntegerType_p ty \<or>
   ty = C__Type__char \<and> C__plainCharsAreUnsigned \<rbrakk> \<Longrightarrow> 
   (int i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty))
   = (i < 2 ^ C__typeBits ty)"
   by (simp add:  C__rangeOfIntegerType_unsigned)

lemma C__rangeOfIntegerType_unsigned3:
  "\<lbrakk>C__unsignedIntegerType_p ty \<or>
    C__plainCharsAreUnsigned \<and> ty = C__Type__char\<rbrakk> \<Longrightarrow> 
   (int i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty))
   = (i < 2 ^ C__typeBits ty)"
   by (simp add:  C__rangeOfIntegerType_unsigned1)

lemma C__rangeOfIntegerType_signed:
  "\<lbrakk>C__integerType_p ty; \<not>C__unsignedIntegerType_p ty;
    C__plainCharsAreUnsigned \<longrightarrow> ty \<noteq> C__Type__char\<rbrakk>   \<Longrightarrow> 
   (i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty))
   = (- (2 ^ (C__typeBits ty - 1)) \<le> i \<and> i < 2 ^ (C__typeBits ty - 1))"
   by (simp add: C__rangeOfIntegerType_def  
                 C__rangeOfIntegerType_Obligation_subtype
                 C__FiniteSetInt_def,
       simp add: mem_def)

lemma C__rangeOfIntegerType_signed0:
  "\<lbrakk>C__integerType_p ty; 
    \<not>(C__unsignedIntegerType_p ty \<or> 
       C__plainCharsAreUnsigned \<and> ty = C__Type__char)\<rbrakk>   \<Longrightarrow> 
   (i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty))
   = (- (2 ^ (C__typeBits ty - 1)) \<le> i \<and> i < 2 ^ (C__typeBits ty - 1))"
   by (simp add: C__rangeOfIntegerType_def  
                 C__rangeOfIntegerType_Obligation_subtype
                 C__FiniteSetInt_def,
       simp add: mem_def)

lemma C__rangeOfIntegerType_signed1:
  "\<lbrakk>C__integerType_p ty; \<not>C__unsignedIntegerType_p ty;
    ty = C__Type__char \<longrightarrow> \<not>C__plainCharsAreUnsigned\<rbrakk>   \<Longrightarrow> 
   (i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty))
   = (- (2 ^ (C__typeBits ty - 1)) \<le> i \<and> i < 2 ^ (C__typeBits ty - 1))"
   by (auto simp add: C__rangeOfIntegerType_signed)

lemma C__rangeOfIntegerType_signed2:
  "\<lbrakk>C__signedIntegerType_p ty \<or>
    ty = C__Type__char \<and> C__plainCharsAreSigned\<rbrakk> \<Longrightarrow>
   (i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty))
   = (- (2 ^ (C__typeBits ty - 1)) \<le> i \<and> i < 2 ^ (C__typeBits ty - 1))"
   by (simp add: C__rangeOfIntegerType_def  
                 C__rangeOfIntegerType_Obligation_subtype
                 C__FiniteSetInt_def,
       simp add: mem_def)

lemma C__rangeOfIntegerType_signed3:
  "\<lbrakk>C__signedIntegerType_p ty \<or>
    C__plainCharsAreSigned \<and> ty = C__Type__char \<rbrakk> \<Longrightarrow>
   (i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty))
   = (- (2 ^ (C__typeBits ty - 1)) \<le> i \<and> i < 2 ^ (C__typeBits ty - 1))"
   by (auto simp add: C__rangeOfIntegerType_signed2)

lemmas C__Range = C__rangeOfIntegerType_unsigned
                  C__rangeOfIntegerType_unsigned1
                  C__rangeOfIntegerType_unsigned2
                  C__rangeOfIntegerType_unsigned3
                  C__rangeOfIntegerType_signed
                  C__rangeOfIntegerType_signed0
                  C__rangeOfIntegerType_signed1
                  C__rangeOfIntegerType_signed2
                  C__rangeOfIntegerType_signed3



lemma C__rangeOfIntegerType_extend [simp]:
  "\<lbrakk>C__integerType_p ty; i < 2 ^x ; x < len; C__typeBits ty = len\<rbrakk>
    \<Longrightarrow> int i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)"
  apply (cases "C__unsignedIntegerType_p ty \<or>
                  C__plainCharsAreUnsigned \<and> ty = C__Type__char ")
  apply (simp add: C__Range power_strict_increasing less_trans)
  apply (simp add: C__Range less_le_trans power_increasing)
done

lemma C__rangeOfIntegerType_extend_TC [simp]:
  "\<lbrakk>C__signedIntegerType_p ty 
      \<or> ty = C__Type__char \<and> C__plainCharsAreSigned; 
    0 < x; i < 2 ^x ; x < len; C__typeBits ty = len\<rbrakk>
    \<Longrightarrow> TwosComplement__toInt (toBits (i, x))
         \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)"
  apply (simp add: C__Range TwosComplementInt)
  apply (thin_tac ?P, thin_tac "?x = len")
  apply (auto simp add: less_le_trans power_increasing)
  apply (simp add: algebra_simps,
         rule_tac y="2 ^ (len - 1)" in order_trans, simp_all)
  apply (rule_tac y="int i" in less_trans, 
         simp_all add: less_le_trans power_increasing)
done 


lemma C__rangeOfIntegerType_TC2 [simp]:
  "\<lbrakk>C__signedIntegerType_p ty \<or>
    ty = C__Type__char \<and> C__plainCharsAreSigned;
    i \<in> TwosComplement__rangeForLength len; C__typeBits ty = len\<rbrakk>
    \<Longrightarrow> i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)"
  by (simp add: C__Range, simp add: TwosComplement_tcN)


lemma C__rangeOfIntegerType_int: 
   "\<lbrakk>C__integerType_p ty; len < C__typeBits ty; i < 2 ^ len\<rbrakk>
     \<Longrightarrow> int i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)"
  by auto

lemma C__rangeOfIntegerType_char [simp]:
  "\<lbrakk>i < 2 ^ 7\<rbrakk>
  \<Longrightarrow> int i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__char)"
  by (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def C__MinMax,
      simp add: mem_def)

lemma C__rangeOfIntegerType_char2 [simp]:
  "\<lbrakk>0 \<le> i; i < 2 ^ 7\<rbrakk> \<Longrightarrow>
  i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__char)"  
  by (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def C__MinMax,
      simp add: mem_def)

lemma C__rangeOfIntegerType_uchar [simp]:
  "\<lbrakk>i < 2 ^ 8\<rbrakk>
  \<Longrightarrow> int i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__uchar)"
  by (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
      simp add: mem_def)

lemma C__rangeOfIntegerType_uchar2 [simp]:
  "\<lbrakk>0 \<le> i; i < 2 ^ 8\<rbrakk> \<Longrightarrow>
  i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__uchar)"
  by (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
      simp add: mem_def)

lemma C__rangeOfIntegerType_sint [simp]:
  "\<lbrakk>i < 2 ^ 8\<rbrakk>
   \<Longrightarrow> int i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint)"
  apply (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
         simp add: mem_def)
  apply (cut_tac C__min_INT_MIN, simp, cut_tac C__min_INT_MAX, simp)
done

lemma C__rangeOfIntegerType_sint2 [simp]:
  "\<lbrakk>0 \<le> i; i < 2 ^ 8\<rbrakk>
   \<Longrightarrow> i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint)"
  apply (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
         simp add: mem_def)
  apply (cut_tac C__min_INT_MIN, simp, cut_tac C__min_INT_MAX, simp)
done

lemma C__rangeOfIntegerType_0 [simp]:
  "\<lbrakk>C__integerType_p ty\<rbrakk>
   \<Longrightarrow> 0 \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)"
 by (simp add: C__IntTypes C__rangeOfIntegerType_def C__FiniteSetInt_def, 
     auto simp add: mem_def C__MinMax)
 
lemma C__rangeOfIntegerType_1 [simp]:
  "\<lbrakk>C__integerType_p ty\<rbrakk>
   \<Longrightarrow> 1 \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)"
  apply (cases "C__unsignedIntegerType_p ty \<or>
                  C__plainCharsAreUnsigned \<and> ty = C__Type__char ")
  apply (simp add: C__Range, clarsimp simp add: C__Range)
  apply (cut_tac C__min_SHRT_MIN, cut_tac C__min_INT_MIN,  
         cut_tac C__min_LONG_MIN,  cut_tac C__min_LLONG_MIN)
  apply (drule C__signed_cases2, simp_all, cases ty, auto simp add: C__MinMax)
done
  
lemma C__rangeOfIntegerType_subset_char_sint [simp]:
  "   Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__char) 
   \<subseteq> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint)"
  by (cut_tac C__min_INT_MIN, cut_tac C__min_INT_MAX, 
      simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
      auto simp add: subset_iff mem_def C__CHAR_MAX_def)

lemma C__rangeOfIntegerType_subset_uchar_sint [simp]:
  "   Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__uchar) 
   \<subseteq> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint)"
  by (cut_tac C__min_INT_MIN, cut_tac C__min_INT_MAX, 
      simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
      auto simp add: subset_iff mem_def C__CHAR_MAX_def)

lemma C__rangeOfIntegerType_subset_schar_sint [simp]:
  "   Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__schar) 
   \<subseteq> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint)"
  by (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
      cut_tac C__min_INT_MIN, cut_tac C__min_INT_MAX, 
      auto simp add: subset_iff mem_def)

lemma C__rangeOfIntegerType_subset_sshort_sint [simp]:
  "   Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sshort) 
   \<subseteq> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint)"
  apply (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
         auto simp add: subset_iff mem_def C__MinMax)
  apply (rule_tac y="- (2 ^ (C__short_bits - Suc 0))" in order_trans,
         simp_all add: power_increasing diff_le_mono)
  apply (erule less_le_trans, simp add: power_increasing diff_le_mono)
done

lemma C__rangeOfIntegerType_subset_ushort_sint1:
  "\<lbrakk>C__sizeof_short < C__sizeof_int\<rbrakk>  \<Longrightarrow> 
      Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__ushort) 
   \<subseteq> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint)"
  apply (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
         auto simp add: subset_iff mem_def C__MinMax)
  apply (rule_tac y="0" in order_trans, simp_all)
  apply (erule less_le_trans, 
         simp add: power_increasing diff_le_mono C__Consts)
done

lemma C__rangeOfIntegerType_subset_ushort_sint2:
  "\<lbrakk>C__sizeof_short = C__sizeof_int\<rbrakk>  \<Longrightarrow> 
   \<not> ( Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__ushort) 
      \<subseteq> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint))"
  apply (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
         auto simp add: subset_iff mem_def C__MinMax C__Consts not_less)
  apply (rule_tac x="2 ^ (C__sizeof_int * 8 - Suc 0)" in exI, auto)
done

lemma C__rangeOfIntegerType_subset_ushort_sint [simp]:
  "   Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__ushort) 
   \<subseteq> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint)
  = (C__sizeof_short < C__sizeof_int)"
  apply (rule iffI)
  apply (rule classical, 
         simp add:  C__rangeOfIntegerType_subset_ushort_sint2 eq_iff)
  apply (simp add: C__rangeOfIntegerType_subset_ushort_sint1)
done

lemma C__rangeOfIntegerType_subset_uint_sint [simp]:
  "\<not> ( Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__uint) 
      \<subseteq> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint))"
  apply (simp add: C__rangeOfIntegerType_def C__FiniteSetInt_def,
         auto simp add: subset_iff mem_def C__MinMax not_less)
  apply (rule_tac x="2 ^ (C__int_bits - Suc 0)" in exI, auto)
done

lemma C__rangeOfIntegerType_subset_sint_sint [simp]:
  "   Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint) 
   \<subseteq> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint)"
 by simp

(******************************************************************************)


lemma C__TwosComplement__toInt_in_sint_range [simp]:
 "\<lbrakk>length y = C__int_bits\<rbrakk> \<Longrightarrow>
  TwosComplement__toInt y
  \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__sint)"  
  apply (cut_tac x=y in TwosComplement__integer_range,
         simp add: length_0_conv [symmetric])
  apply (simp add: C__rangeOfIntegerType_def
                   TwosComplement__rangeForLength_def
                   TwosComplement__minForLength_def 
                   TwosComplement__maxForLength_def
                   C__MinMax C__FiniteSetInt_def)
done
 
(** Should generalize this ***)

lemma C__TwosComplement__range_int_bits [simp]:
 "\<lbrakk>-32768 \<le> i; i \<le> 32767\<rbrakk> \<Longrightarrow> 
  i \<in> TwosComplement__rangeForLength C__int_bits"
  apply (cut_tac C__min_INT_MIN, cut_tac C__min_INT_MAX, 
      simp add: C__MinMax TwosComplement__rangeForLength_def
                   TwosComplement__minForLength_def 
                   TwosComplement__maxForLength_def mem_def)




(******************************************************************************)

end-proof

proof Isa correspondingSignedOf_Obligation_exhaustive
  by (simp add: C__IntTypes)
end-proof

proof Isa C__digitValue_Obligation_subtype
  by (simp add: nat_of_char_def C__digit_p_def)
end-proof

proof Isa hexDigitValue_Obligation_subtype0
  by (auto simp add: C__hexadecimalDigit_p_def nat_of_char_def)
end-proof

proof Isa decimalConstantValue_Obligation_subtype
  by (simp add: C__decimalConstant_p_def)
end-proof

proof Isa decimalConstantValue_Obligation_subtype0
  by (simp add: C__decimalConstant_p_def)
end-proof

proof Isa decimalConstantValue_Obligation_subtype1
  by (auto simp add: C__decimalConstant_p_def member_def list_all_iff 
                     C__digit_p_def C__digitValue_def  nat_of_char_def)
end-proof

proof Isa octalConstantValue_Obligation_subtype
  by (simp add: C__octalConstant_p_def C__octalDigit_p_def list_all_iff)
end-proof

proof Isa octalConstantValue_Obligation_subtype0
  by (simp add: C__octalConstant_p_def)
end-proof

proof Isa  octalConstantValue_Obligation_subtype1
  apply (simp add: C__octalConstant_p_def member_def list_all_iff 
                   C__octalDigit_p_def, safe)
  apply (subgoal_tac "nat_of_char CHR ''0'' = 48 
                    \<and> nat_of_char CHR ''8'' = 56
                    \<and> nat_of_char CHR ''9'' = 57", clarsimp) 
  defer apply (simp add: nat_of_char_def)
  apply (drule bspec, auto)
  apply (simp_all add: C__digit_p_def C__digitValue_def, safe)
  apply (subgoal_tac "nat_of_char x \<noteq> 56
               \<and> nat_of_char x \<noteq> 57", auto)
  apply (rotate_tac -1, drule_tac f="char_of_nat" in arg_cong,
         cut_tac c="CHR ''8''" in char_of_nat_of_char,
         simp add: char_of_nat_of_char)
  apply (rotate_tac -1, drule_tac f="char_of_nat" in arg_cong,
         cut_tac c="CHR ''9''" in char_of_nat_of_char,
         simp add: char_of_nat_of_char)
end-proof


proof Isa hexadecimalConstantValue_Obligation_subtype
  by (auto simp add: C__hexadecimalConstant_p_def)
end-proof

proof Isa hexadecimalConstantValue_Obligation_subtype0
  by (auto simp add: C__hexadecimalConstant_p_def
                     C__hexadecimalDigit_p_def list_all_iff)
end-proof

proof Isa hexadecimalConstantValue_Obligation_subtype1
  by (auto simp add: C__hexadecimalConstant_p_def)
end-proof

proof Isa hexadecimalConstantValue_Obligation_subtype2
  apply (simp add: C__hexadecimalConstant_p_def C__hexadecimalDigit_p_def 
                   list_all_iff, clarify)
  apply (subgoal_tac "nat_of_char CHR ''0'' = 48 
                    \<and> nat_of_char CHR ''9'' = 57
                    \<and> nat_of_char CHR ''A'' = 65 
                    \<and> nat_of_char CHR ''F'' = 70
                    \<and> nat_of_char CHR ''Z'' = 90
                    \<and> nat_of_char CHR ''a'' = 97
                    \<and> nat_of_char CHR ''f'' = 102", clarsimp) 
  defer apply (simp add: nat_of_char_def)
  apply (auto simp add: member_def image_iff)
  apply (drule bspec, auto) prefer 4 apply (drule bspec, auto)   
  apply (simp_all add: C__digit_p_def C__digitValue_def 
                       C__hexDigitValue_def not_le)
  apply (safe, arith, arith) 
end-proof

proof Isa integerConstantValue_Obligation_subtype
  apply (subgoal_tac "\<exists>suffix.
            Rep_C__IntegerConstant c = unsuffixed @ suffix \<and>
            C__integerSuffixOpt_p suffix")
  defer
  apply (clarify, simp add: C__unsuffixedIntegerConstant_def,
         rule the1I2, 
         simp add: C__unsuffixedIntegerConstant_Obligation_the, simp)
  apply (thin_tac ?p, cases c, 
         simp add: C__IntegerConstant_def C__integerConstant_p_def
                   C__integerSuffixOpt_p_def C__lengthSuffix_p_def
                    C__signSuffix_p_def C__unsignedSuffix_p_def 
                    C__longSuffix_p_def C__longLongSuffix_p_def,
         clarsimp)
  apply (erule disjE, clarsimp)+
  apply (simp add: C__hexadecimalConstant_p_def C__hexadecimalDigit_p_def
                   C__octalConstant_p_def       C__octalDigit_p_def
                   C__decimalConstant_p_def
                   list_all_iff     
                   )
 (* too many cases -- later *)
sorry
end-proof 

proof Isa C__promoteType_Obligation_subtype
 apply (auto simp add: C__rank__lt_eq_def C__rank__lt_def C__rank__eq_def 
                       C__rankedTypes_def member_def C__IntTypes)
 apply (subgoal_tac "i2=1 \<or> i2=2 \<or> i2=3 \<or> i2=4") defer 
 apply (arith, safe, simp_all add: One_nat_def)
 apply (subgoal_tac "i1=0 \<or> i1=1", safe, simp_all add: One_nat_def)
done

(******************************************************************************)

lemmas C__IntValues = C__integerConstantValue_def  C__decimalConstantValue_def 
                      C__hexadecimalConstantValue_def C__octalConstantValue_def 
                      C__digitValue_def C__hexDigitValue_def

(******************************************************************************)

(********************************************************************************)

lemma C__rank__lt_eq_char_sint [simp]:
  "C__Type__char rank_<= C__Type__sint"
  by (simp add: C__rank__lt_eq_def C__rank__lt_def,
      rule disjI1, rule_tac x=0 in exI, rule_tac x=2 in exI, 
      simp add: C__rankedTypes_def)

lemma C__rank__lt_eq_uchar_sint [simp]:
  "C__Type__uchar rank_<= C__Type__sint"
  by (simp add: C__rank__lt_eq_def C__rank__lt_def,
      rule disjI1, rule_tac x=0 in exI, rule_tac x=2 in exI, 
      simp add: C__rankedTypes_def)

lemma C__rank__lt_eq_schar_sint [simp]:
  "C__Type__schar rank_<= C__Type__sint"
  by (simp add: C__rank__lt_eq_def C__rank__lt_def,
      rule disjI1, rule_tac x=0 in exI, rule_tac x=2 in exI, 
      simp add: C__rankedTypes_def)

lemma C__rank__lt_eq_ushort_sint [simp]:
  "C__Type__ushort rank_<= C__Type__sint"
  by (simp add: C__rank__lt_eq_def C__rank__lt_def,
      rule disjI1, rule_tac x=1 in exI, rule_tac x=2 in exI, 
      simp add: C__rankedTypes_def)

lemma C__rank__lt_eq_sshort_sint [simp]:
  "C__Type__sshort rank_<= C__Type__sint"
  by (simp add: C__rank__lt_eq_def C__rank__lt_def,
      rule disjI1, rule_tac x=1 in exI, rule_tac x=2 in exI, 
      simp add: C__rankedTypes_def)

lemma C__rank__lt_eq_uint_sint [simp]:
  "C__Type__uint rank_<= C__Type__sint"
  by (simp add: C__rank__lt_eq_def C__rank__eq_def,
      rule disjI2, rule_tac x="C__rankedTypes ! 2" in exI, 
      simp add: C__rankedTypes_def)

lemma C__rank__lt_eq_sint_sint [simp]:
  "C__Type__sint rank_<= C__Type__sint"
  by (simp add: C__rank__lt_eq_def C__rank__eq_def,
      rule disjI2, rule_tac x="C__rankedTypes ! 2" in exI, 
      simp add: C__rankedTypes_def)

(*******************************************************************************
 * The general theorem is too complex to prove *

lemma C__rank__not_lt_eq_is_rank_lt [simp]:
  "\<lbrakk>C__integerType_p ty1; C__integerType_p ty2\<rbrakk>
   \<Longrightarrow> (\<not> (ty1 rank_<= ty2))  = (ty2 rank_< ty1)"
  apply (auto simp add: C__rank__lt_eq_def C__rank__lt_def 
                                  C__rank__eq_def)
  apply (drule C__integerType_cases, cases ty1, auto)
  apply (drule C__integerType_cases, cases ty2, auto)
  apply (drule_tac x=0 in spec)
  apply (simp add: C__rankedTypes_def)
 
 * for now I'll only discuss the specific cases we need **
*******************************************************************************)

lemma C__rank__not_lt_eq_ulong_sint [simp]:
  "\<not> (C__Type__ulong rank_<= C__Type__sint)"
  apply (auto simp add: C__rank__lt_eq_def C__rank__lt_def C__rank__eq_def
                        C__rankedTypes_def)
  apply (subgoal_tac "i2=1 \<or> i2=2 \<or> i2=3 \<or> i2=4")
  defer
  apply (arith, safe, simp_all)
  apply (subgoal_tac "i1=0 \<or> i1=1", safe, simp_all)
done
  
lemma C__rank__not_lt_eq_slong_sint [simp]:
  "\<not> (C__Type__slong rank_<= C__Type__sint)"
  apply (auto simp add: C__rank__lt_eq_def C__rank__lt_def C__rank__eq_def
                        C__rankedTypes_def)
  apply (subgoal_tac "i2=1 \<or> i2=2 \<or> i2=3 \<or> i2=4")
  defer
  apply (arith, safe, simp_all)
  apply (subgoal_tac "i1=0 \<or> i1=1", safe, simp_all)
done
  
lemma C__rank__not_lt_eq_ullong_sint [simp]:
  "\<not> (C__Type__ullong rank_<= C__Type__sint)"
  apply (auto simp add: C__rank__lt_eq_def C__rank__lt_def C__rank__eq_def
                        C__rankedTypes_def)
  apply (subgoal_tac "i2=1 \<or> i2=2 \<or> i2=3 \<or> i2=4")
  defer
  apply (arith, safe, simp_all)
  apply (subgoal_tac "i1=0 \<or> i1=1", safe, simp_all)
done
  
lemma C__rank__not_lt_eq_sllong_sint [simp]:
  "\<not> (C__Type__sllong rank_<= C__Type__sint)"
  apply (auto simp add: C__rank__lt_eq_def C__rank__lt_def C__rank__eq_def
                        C__rankedTypes_def)
  apply (subgoal_tac "i2=1 \<or> i2=2 \<or> i2=3 \<or> i2=4")
  defer
  apply (arith, safe, simp_all)
  apply (subgoal_tac "i1=0 \<or> i1=1", safe, simp_all)

(******************************************************************************)

end-proof  


proof Isa arithConvertTypes_Obligation_subtype
 by (simp add:  C__promoteType_def C__IntTypes split: split_if_asm)

(******************************************************************************)

lemma C__promoteType_char [simp]: 
  "C__promoteType C__Type__char = C__Type__sint"
  by (simp add: C__promoteType_def)

lemma C__promoteType_uchar [simp]: 
  "C__promoteType C__Type__uchar = C__Type__sint"
  by (simp add: C__promoteType_def)

lemma C__promoteType_schar [simp]: 
  "C__promoteType C__Type__schar = C__Type__sint"
  by (simp add: C__promoteType_def)

lemma C__promoteType_ushort [simp]: 
  "C__promoteType C__Type__ushort = (if C__sizeof_short < C__sizeof_int 
                                        then C__Type__sint 
                                        else C__Type__uint)"
  by (simp add: C__promoteType_def)

lemma C__promoteType_sshort [simp]: 
  "C__promoteType C__Type__sshort = C__Type__sint"
  by (simp add: C__promoteType_def)

lemma C__promoteType_uint [simp]:
  "C__promoteType C__Type__uint = C__Type__uint"
  by (simp add: C__promoteType_def)

lemma C__promoteType_sint [simp]:
  "C__promoteType C__Type__sint = C__Type__sint"
  by (simp add: C__promoteType_def)

lemma C__promoteType_ulong [simp]:
  "C__promoteType C__Type__ulong = C__Type__ulong"
  by (simp add: C__promoteType_def)

lemma C__promoteType_slong [simp]:
  "C__promoteType C__Type__slong = C__Type__slong"
  by (simp add: C__promoteType_def)

lemma C__promoteType_ullong [simp]:
  "C__promoteType C__Type__ullong = C__Type__ullong"
  by (simp add: C__promoteType_def)

lemma C__promoteType_sllong [simp]:
  "C__promoteType C__Type__sllong = C__Type__sllong"
  by (simp add: C__promoteType_def)


lemma  C__promoteType_not_char_type:
  "\<lbrakk>C__integerType_p ty\<rbrakk> \<Longrightarrow>    \<not> C__characterType_p (C__promoteType ty)"
  by (auto simp add: C__characterType_p_def C__IntTypes split: split_if_asm)

lemma  C__promoteType_not_char:
  "\<lbrakk>C__integerType_p ty\<rbrakk> \<Longrightarrow> C__promoteType ty \<noteq> C__Type__char"
  by (drule C__promoteType_not_char_type, simp add: C__characterType_p_def)

lemma  C__promoteType_int:
  "\<lbrakk>C__integerType_p ty\<rbrakk>    \<Longrightarrow>  C__integerType_p (C__promoteType ty)"
  by (simp add:  C__promoteType_def C__IntTypes)

lemma  C__promoteType_int2:
  "\<lbrakk>C__arithmeticType_p ty\<rbrakk> \<Longrightarrow>  C__integerType_p (C__promoteType ty)"
  by (simp add:  C__promoteType_def C__IntTypes)

lemma  C__promoteType_int3:
  "\<lbrakk>C__integerType_p ty\<rbrakk> \<Longrightarrow> 
      C__signedIntegerType_p (C__promoteType ty) 
   \<or>  C__unsignedIntegerType_p (C__promoteType ty) "
  by (frule C__promoteType_int, drule C__promoteType_not_char,
      simp add: C__integerType_p_def)

lemma  C__promoteType_int4:
  "\<lbrakk>C__arithmeticType_p ty\<rbrakk> \<Longrightarrow> 
      C__signedIntegerType_p (C__promoteType ty) 
   \<or>  C__unsignedIntegerType_p (C__promoteType ty) "
  apply (rule C__promoteType_int3, simp add: C__arithmeticType_p_def)
(********************************************************************************)


end-proof 

proof Isa arithConvertTypes_Obligation_subtype0
 by (simp add:  C__promoteType_def C__IntTypes split: split_if_asm)
end-proof 

proof Isa arithConvertTypes_Obligation_subtype1
  by (drule C__promoteType_int4, drule C__promoteType_int4,
      simp  split: split_if_asm)
end-proof 

% ------------------------------------------------------------

% ----------------------------------------------------------------------------
% Did I put this in here ????
% 
% type      FiniteMap(a,b) = (Map(a,b) | finite?)
% proof Isa -typedef 
%  by (rule_tac x="empty" in exI, simp add: mem_def Map__finite_p_def Collect_def)
% end-proof

% ----------------------------------------------------------------------------
% Right now we cannot translate the parameterized type of FiniteMaps
% As a temporary fix I introduce an instantiated Version 

type FMapIdType = (Map (Identifier,Type) |  finite? )
proof Isa -typedef 
   by (rule_tac x="empty" in exI, simp add: mem_def  Collect_def)
end-proof

theorem FMapIdType_finite is  fa (m:FMapIdType) finite? m
theorem FMapIdType_finite1 is fa (m:FMapIdType) finite? (domain m)

% ----------------------------------------------------------------------------

proof Isa FMapIdType_finite [simp]
  by (case_tac "m", 
      simp add: Abs_C__FMapIdType_inverse C__FMapIdType_def Collect_def mem_def)
end-proof

proof Isa FMapIdType_finite1  [simp]
  by (cut_tac C__FMapIdType_finite, simp)

(******************************************************************************)
declare Rep_C__FMapIdType_inverse [simp add]
declare Abs_C__FMapIdType_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_C__FMapIdType_simp [simp]:
  "\<lbrakk>Map__finite_p y\<rbrakk> \<Longrightarrow>  (Rep_C__FMapIdType x = y) = (x = Abs_C__FMapIdType y)"
apply (subst Abs_C__FMapIdType_inject [symmetric],
       simp add: Rep_C__FMapIdType,
       simp add: C__FMapIdType_def Collect_def mem_def,
       simp add: Rep_C__FMapIdType_inverse)
(******************************************************************************)

end-proof

% ------------------------------------------------------------

% ----------------------------------------------------------------------------
% Right now we cannot translate the parameterized type of FiniteMaps
% As a temporary fix I introduce an instantiated Version 

type FMapIdTypedM = (Map (Identifier,TypedMembers) | finite?)
proof Isa -typedef 
   by (rule_tac x="empty" in exI, simp add: mem_def  Collect_def)
end-proof

theorem FMapIdTypedM_finite is  fa (m:FMapIdTypedM) finite? m
theorem FMapIdTypedM_finite1 is fa (m:FMapIdTypedM) finite? (domain m)

% ----------------------------------------------------------------------------

proof Isa FMapIdTypedM_finite [simp]
  by (case_tac "m", 
      simp add: Abs_C__FMapIdTypedM_inverse C__FMapIdTypedM_def Collect_def mem_def)
end-proof

proof Isa FMapIdTypedM_finite1  [simp]
  by (cut_tac C__FMapIdTypedM_finite, simp)

(******************************************************************************)
declare Rep_C__FMapIdTypedM_inverse [simp add]
declare Abs_C__FMapIdTypedM_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_C__FMapIdTypedM_simp [simp]:
  "\<lbrakk>Map__finite_p y\<rbrakk> \<Longrightarrow>  (Rep_C__FMapIdTypedM x = y) = (x = Abs_C__FMapIdTypedM y)"
apply (subst Abs_C__FMapIdTypedM_inject [symmetric],
       simp add: Rep_C__FMapIdTypedM,
       simp add: C__FMapIdTypedM_def Collect_def mem_def,
       simp add: Rep_C__FMapIdTypedM_inverse)
(******************************************************************************)

end-proof

% ------------------------------------------------------------

% ----------------------------------------------------------------------------
% Right now we cannot translate the parameterized type of FiniteMaps
% As a temporary fix I introduce an instantiated Version 

type FMapIdTypedP = (Map (Identifier,Type * TypedParameters) |  finite?)
proof Isa -typedef 
   by (rule_tac x="empty" in exI, simp add: mem_def  Collect_def)
end-proof

theorem FMapIdTypedP_finite is  fa (m:FMapIdTypedP) finite? m
theorem FMapIdTypedP_finite1 is fa (m:FMapIdTypedP) finite? (domain m)

% ----------------------------------------------------------------------------

proof Isa FMapIdTypedP_finite [simp]
  by (case_tac "m", 
      simp add: Abs_C__FMapIdTypedP_inverse C__FMapIdTypedP_def Collect_def mem_def)
end-proof

proof Isa FMapIdTypedP_finite1  [simp]
  by (cut_tac C__FMapIdTypedP_finite, simp)

(******************************************************************************)
declare Rep_C__FMapIdTypedP_inverse [simp add]
declare Abs_C__FMapIdTypedP_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_C__FMapIdTypedP_simp [simp]:
  "\<lbrakk>Map__finite_p y\<rbrakk> \<Longrightarrow>  (Rep_C__FMapIdTypedP x = y) = (x = Abs_C__FMapIdTypedP y)"
apply (subst Abs_C__FMapIdTypedP_inject [symmetric],
       simp add: Rep_C__FMapIdTypedP,
       simp add: C__FMapIdTypedP_def Collect_def mem_def,
       simp add: Rep_C__FMapIdTypedP_inverse)
(******************************************************************************)

end-proof

proof Isa FunctionTable -typedef
sorry
end-proof

proof Isa objectTypeInSymTab__aux () 
 by auto
termination
 by (relation "measure (\<lambda>(scopes, name). size scopes)", 
     auto simp add: List__empty_p_length)
end-proof

proof Isa checkIntegerConstant_Obligation_subtype
  (* Another brute-force proof - should have a special tactic *)
  apply (clarsimp simp add: C__integerConstantCandidateTypes_def Let_def
                  split: split_if_asm)
  apply (drule Nat_to_2_cases, auto)
  apply (drule Nat_to_5_cases, auto)
  apply (drule Nat_to_2_cases, auto)
  apply (drule Nat_to_1_cases, auto)
  apply (drule Nat_to_3_cases, auto)
  apply (drule Nat_to_1_cases, auto)
  apply (drule Nat_to_1_cases, auto)
end-proof 

proof Isa  checkIntegerConstant_Obligation_the
  apply (erule exE,
         rotate_tac -1, drule_tac k=i and m=id in  ex_has_least_nat, 
         clarsimp)
  apply (rule_tac a=x in ex1I, auto)
  apply (drule_tac x="x - 1" in spec, simp)
  apply (drule_tac x="xa" in spec, simp)
  apply (rule classical, drule le_neq_implies_less, auto, erule notE)
  (* the argument now is that the C__integerConstantCandidateTypes
     are increasing in size ... quite complex *)
sorry
end-proof

proof Isa checkIntegerConstant_Obligation_subtype0
  by (simp add: C__checkIntegerConstant_Obligation_subtype)
end-proof

proof Isa checkIntegerConstant_Obligation_subtype3
  by (simp add: C__checkIntegerConstant_Obligation_subtype)
end-proof

proof Isa checkIntegerConstant_Obligation_subtype4
  by (rule the1I2, rule C__checkIntegerConstant_Obligation_the, simp_all)
end-proof

proof Isa checkExpression_Obligation_subtype [simp]
  by (simp add: C__arithmeticType_p_def)
end-proof


proof Isa checkExpression ()
  by (pat_completeness, auto)
termination
  by (relation "measure (\<lambda>(symtab,expr). size expr)", auto)
end-proof


proof Isa checkObjectDeclaration_Obligation_subtype
  by auto
end-proof

proof Isa checkObjectDeclaration_Obligation_subtype0
  by (rule C__checkObjectDeclaration_Obligation_subtype)
end-proof

proof C__checkMemberDeclarations_Obligation_subtype0
  (********************************************************************
   C__checkStructSpecifier_def misses an Abs_C__FMapIdTypedM
   C__checkTypeDefinition_def  misses an Abs_C__FMapIdType
   --- see saved versions for correct def ---
  *********************************************************************)
  by auto
end-proof

proof Isa checkStatement_Obligation_exhaustive
 by (cases stmt, auto simp add: Let_def split: option.split)
end-proof


proof Isa checkBlockItem ()
  by (pat_completeness, auto)
termination
  apply (relation "measure  (\<lambda>x. case x of 
                   Inl (symtab,block) \<Rightarrow> size block
                 | Inr (Inl (symtab,blocks)) \<Rightarrow> list_size size blocks
                 | Inr (Inr (symtab, stmt)) \<Rightarrow> size stmt
                 )", auto)
  (* almost - may need  stmt_size *)
  sorry  
end-proof

proof Isa checkFunctionDefinition_Obligation_subtype0
  apply (rotate_tac -1, thin_tac ?P, thin_tac ?P, thin_tac ?P, 
                        thin_tac ?P, thin_tac ?P, thin_tac ?P,
         simp add: distinct_map)
  apply (subgoal_tac "\<forall>parms z.  C__checkParameterList (symtab, parms) = Some z
                      \<longrightarrow> distinct z \<and> inj_on C__TypedParameter__name (set z)")
  apply (drule spec, drule spec, erule mp, simp)
  apply (thin_tac ?P, rule allI)
  apply (induct_tac parms, simp add: empty_false)
  apply (auto split: option.split_asm split_if_asm)
  (********************************************************************
    C__checkFunctionDefinition_def misses an Abs_C__FMapIdTypedP
   --- see saved versions for correct def ---
  *********************************************************************)
end-proof

% ------------------------------------------------------------

% ----------------------------------------------------------------------------
theorem ShortWord_length is      fa (bs:ShortWord)    ofLength? short_bits bs
theorem ShortWord_length1 is     fa (bs:ShortWord)    length bs = short_bits
theorem IntWord_length is        fa (bs:IntWord)      ofLength? int_bits bs
theorem IntWord_length1 is       fa (bs:IntWord)      length bs = int_bits
theorem LongWord_length is       fa (bs:LongWord)     ofLength? long_bits bs
theorem LongWord_length1 is      fa (bs:LongWord)     length bs = long_bits
theorem LongLongWord_length is   fa (bs:LongLongWord) ofLength? llong_bits bs
theorem LongLongWord_length1 is  fa (bs:LongLongWord) length bs = llong_bits
% ----------------------------------------------------------------------------

proof Isa ShortWord -typedef
  by (rule_tac x="replicate C__short_bits B0" in exI, simp)
end-proof

proof Isa ShortWord_length [simp]
  by (cut_tac x=bs in Rep_C__ShortWord, 
      simp add: C__ShortWord_def Collect_def mem_def)
end-proof

proof Isa ShortWord_length1 [simp]
  by (cut_tac C__ShortWord_length, simp)

(******************************************************************************)
declare Rep_C__ShortWord_inverse [simp add]
declare Abs_C__ShortWord_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_C__ShortWord_simp [simp]:
  "\<lbrakk>length y = C__short_bits\<rbrakk> \<Longrightarrow>  (Rep_C__ShortWord x = y) = (x = Abs_C__ShortWord y)"
apply (subst Abs_C__ShortWord_inject [symmetric],
       simp add: Rep_C__ShortWord,
       simp add: C__ShortWord_def Collect_def mem_def,
       simp)
(******************************************************************************)

end-proof

proof Isa IntWord -typedef
  by (rule_tac x="replicate C__int_bits B0" in exI, simp)
end-proof

proof Isa IntWord_length [simp]
  by (cut_tac x=bs in Rep_C__IntWord, 
      simp add: C__IntWord_def Collect_def mem_def)
end-proof

proof Isa IntWord_length1 [simp]
  by (cut_tac C__IntWord_length, simp)

(******************************************************************************)
declare Rep_C__IntWord_inverse [simp add]
declare Abs_C__IntWord_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_C__IntWord_simp [simp]:
  "\<lbrakk>length y = C__int_bits\<rbrakk> \<Longrightarrow>  (Rep_C__IntWord x = y) = (x = Abs_C__IntWord y)"
apply (subst Abs_C__IntWord_inject [symmetric],
       simp add: Rep_C__IntWord,
       simp add: C__IntWord_def Collect_def mem_def,
       simp)
(******************************************************************************)

end-proof

proof Isa LongWord -typedef
  by (rule_tac x="replicate C__long_bits B0" in exI, simp)
end-proof

proof Isa LongWord_length [simp]
  by (cut_tac x=bs in Rep_C__LongWord, 
      simp add: C__LongWord_def Collect_def mem_def)
end-proof

proof Isa LongWord_length1 [simp]
  by (cut_tac C__LongWord_length, simp)

(******************************************************************************)
declare Rep_C__LongWord_inverse [simp add]
declare Abs_C__LongWord_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_C__LongWord_simp [simp]:
  "\<lbrakk>length y = C__long_bits\<rbrakk> \<Longrightarrow>  (Rep_C__LongWord x = y) = (x = Abs_C__LongWord y)"
apply (subst Abs_C__LongWord_inject [symmetric],
       simp add: Rep_C__LongWord,
       simp add: C__LongWord_def Collect_def mem_def,
       simp)
(******************************************************************************)

end-proof

proof Isa -typedef
  by (rule_tac x="replicate C__llong_bits B0" in exI, simp)
end-proof

proof Isa LongLongWord_length [simp]
  by (cut_tac x=bs in Rep_C__LongLongWord, 
      simp add: C__LongLongWord_def Collect_def mem_def)
end-proof

proof Isa LongLongWord_length1 [simp]
  by (cut_tac C__LongLongWord_length, simp)

(******************************************************************************)

lemmas C__WordLengths = 
                Bits__Byte_length C__ShortWord_length C__IntWord_length 
                C__LongWord_length C__LongLongWord_length

lemmas C__Words = 
                Bits__Byte_def C__ShortWord_def C__IntWord_def 
                C__LongWord_def C__LongLongWord_def

(******************************************************************************)

declare Bits__nonempty_eqlength [simp del] 

theorem C__ShortWord_nonempty [simp]: "Rep_C__ShortWord bs \<noteq> []"
   by (cases bs, simp add: C__Words length_greater_0_iff)
theorem C__IntWord_nonempty [simp]:   "Rep_C__IntWord bs \<noteq> []"
   by (cases bs, simp add: C__Words length_greater_0_iff)
theorem C__LongWord_nonempty [simp]: "Rep_C__LongWord bs \<noteq> []"
   by (cases bs, simp add: C__Words length_greater_0_iff)
theorem C__LongLongWord_nonempty [simp]: "Rep_C__LongLongWord bs \<noteq> []"
   by (cases bs, simp add: C__Words length_greater_0_iff)

(******************************************************************************)
declare Rep_C__LongLongWord_inverse [simp add]
declare Abs_C__LongLongWord_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_C__LongLongWord_simp [simp]:
  "\<lbrakk>length y = C__llong_bits\<rbrakk> \<Longrightarrow> (Rep_C__LongLongWord x = y) = (x = Abs_C__LongLongWord y)"
apply (subst Abs_C__LongLongWord_inject [symmetric],
       simp add: Rep_C__LongLongWord,
       simp add: C__LongLongWord_def Collect_def mem_def,
       simp)
(******************************************************************************)

end-proof

% ------------------------------------------------------------

% ----------------------------------------------------------------------------
% Right now we cannot translate the parameterized type of FiniteMaps
% As a temporary fix I introduce an instantiated Version 
% that doesn't really work here because of the mutual recursion
% I'll keep the def for now but we must think of something else
% In the above definition we will get subtype constr issues again


type FMapIdVal = (Map (Identifier,Value) | finite?)
proof Isa -typedef 
    by (rule_tac x="empty" in exI, simp add: mem_def  Collect_def)
end-proof

theorem FMapIdVal_finite is   fa (m:FMapIdVal) finite? m
theorem FMapIdVal_finite1 is  fa (m:FMapIdVal) finite? (domain m)
% ----------------------------------------------------------------------------

proof Isa FMapIdVal_finite [simp]
  by (case_tac "m", 
      simp add: Abs_C__FMapIdVal_inverse C__FMapIdVal_def Collect_def mem_def)
end-proof

proof Isa FMapIdVal_finite1  [simp]
  by (cut_tac C__FMapIdVal_finite, simp)

(******************************************************************************)
declare Rep_C__FMapIdVal_inverse [simp add]
declare Abs_C__FMapIdVal_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_C__FMapIdVal_simp [simp]:
  "\<lbrakk>Map__finite_p y\<rbrakk> \<Longrightarrow>  (Rep_C__FMapIdVal x = y) = (x = Abs_C__FMapIdVal y)"
apply (subst Abs_C__FMapIdVal_inject [symmetric],
       simp add: Rep_C__FMapIdVal,
       simp add: C__FMapIdVal_def Collect_def mem_def,
       simp add: Rep_C__FMapIdVal_inverse)
(******************************************************************************)
(** Below remove the type after zzz_25 - it's wrong                           *)
(******************************************************************************)
end-proof

proof Isa  valueOfBits_Obligation_the
  apply (simp add: C__IntTypes)
  (* Case 1 of 11*)
  apply (erule disjE, simp add: C__BitTypes)
  apply (rule_tac a="C__Value__char (Abs_Bits__Byte bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
  (* Case 2 *)
  apply (erule disjE, simp add: C__BitTypes)
  apply (rule_tac a="C__Value__schar (Abs_Bits__Byte bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
  (* Case 3 *)
  apply (erule disjE, simp add: C__BitTypes)
  apply (rule_tac a="C__Value__sshort (Abs_C__ShortWord bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
  (* Case 4 *)
  apply (erule disjE, simp add: C__BitTypes)
  apply (rule_tac a="C__Value__sint (Abs_C__IntWord bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
  (* Case 5 *)
  apply (erule disjE, simp add: C__BitTypes)
  apply (rule_tac a="C__Value__slong (Abs_C__LongWord bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
  (* Case 6 *)
  apply (erule disjE, simp add: C__BitTypes)
  apply (rule_tac a="C__Value__sllong (Abs_C__LongLongWord bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
  (* Case 7 *)
  apply (erule disjE, simp add: C__BitTypes)
  apply (rule_tac a="C__Value__uchar (Abs_Bits__Byte bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
  (* Case 8 *)
  apply (erule disjE, simp add: C__BitTypes)
  apply (rule_tac a="C__Value__ushort (Abs_C__ShortWord bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
  (* Case 9 *)
  apply (erule disjE, simp add: C__BitTypes)
  apply (rule_tac a="C__Value__uint (Abs_C__IntWord bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
  (* Case 10 *)
  apply (erule disjE, simp add: C__BitTypes)
  apply (rule_tac a="C__Value__ulong (Abs_C__LongWord bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
  (* Case 11 *)
  apply (rule_tac a="C__Value__ullong (Abs_C__LongLongWord bits)" in ex1I, simp)
  apply (clarify, case_tac x, simp_all add:  C__IntTypes)
done
(******************************************************************************)
(* Ideally these lemmas come before the above theorem - that would 
   simplify the proof - use a dummy theorem and the saved proof???            *)
(******************************************************************************)
theorem C___bitsOfIntegerValue_int_p:
  "\<lbrakk>C__bitsOfIntegerValue val = C__OC__ok bits\<rbrakk> \<Longrightarrow> 
   C__integerType_p (C__typeOfValue val)"
   by (cases val, auto split: split_if_asm)

lemma C___bitsOfIntegerValue_is_pos:
   "C__bitsOfIntegerValue val = C__OC__ok a  \<Longrightarrow> a \<noteq> []"
 by (cases val, auto split: split_if_asm)

lemma C__bitsOfIntegerValue_length:
  "\<lbrakk>C__typeBits (C__typeOfValue val) = len;
    C__bitsOfIntegerValue val = C__OC__ok bits\<rbrakk>
  \<Longrightarrow> length bits = len"
  by (cases val, auto split: split_if_asm)

lemma C__bitsOfIntegerValue_length2:
  "\<lbrakk>C__typeOfValue val = ty; 
    C__bitsOfIntegerValue val = C__OC__ok bits\<rbrakk> \<Longrightarrow> 
     length bits = C__typeBits ty"
  by (cases val, auto split: split_if_asm)

lemma C__bitsOfIntegerValue_length3:
  "\<lbrakk>C__bitsOfIntegerValue val = C__OC__ok bits\<rbrakk> \<Longrightarrow> 
    length bits = C__typeBits (C__typeOfValue val)"
  by (cases val, auto split: split_if_asm)

lemma C___bitsOfIntegerValue_is_defined:
   "C__bitsOfIntegerValue val = C__OC__ok a
      \<Longrightarrow> val \<noteq>  C__Value__undefined ty"
 by (cases val, simp_all split: split_if_asm)

lemmas C__bitsOfIntV =  C___bitsOfIntegerValue_int_p
                        C__bitsOfIntegerValue_length
                        C__bitsOfIntegerValue_length2
                        C__bitsOfIntegerValue_length3
                        C___bitsOfIntegerValue_is_defined
(******************************************************************************)


lemma C__toNat_in_range_char [simp]:
   "\<lbrakk>C__typeBits (C__typeOfValue val) = 8;
     C__bitsOfIntegerValue val = C__OC__ok a;
     C__unsignedIntegerType_p (C__typeOfValue val) \<or>
        C__typeOfValue val = C__Type__char;
     C__plainCharsAreUnsigned\<rbrakk>
     \<Longrightarrow> int (toNat a)
          \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__char)"
  by (frule C__bitsOfIntegerValue_length, simp,
      cut_tac bs=a in Bits__toNat_bound, auto simp add: C__Range)


lemma C__toNat_in_range_uchar [simp]:
  "\<lbrakk>C__typeBits (C__typeOfValue val) = 8;
    C__bitsOfIntegerValue val = C__OC__ok a;
    C__unsignedIntegerType_p (C__typeOfValue val) \<or>
       C__plainCharsAreUnsigned \<and> C__typeOfValue val = C__Type__char\<rbrakk>
    \<Longrightarrow> int (toNat a)
           \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__uchar)"
  by (frule C__bitsOfIntegerValue_length, simp,
      cut_tac bs=a in Bits__toNat_bound, auto simp add: C__Range)

lemma C__toNat_in_range_ushort [simp]:
  "\<lbrakk>C__typeBits (C__typeOfValue val) = C__short_bits;
    C__bitsOfIntegerValue val = C__OC__ok a;
    C__unsignedIntegerType_p (C__typeOfValue val) \<or>
       C__plainCharsAreUnsigned \<and> C__typeOfValue val = C__Type__char\<rbrakk>
    \<Longrightarrow> int (toNat a)
           \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__ushort)"
  by (subst C__rangeOfIntegerType_unsigned3, simp add: C__IntTypes,
      frule C__bitsOfIntegerValue_length, simp,
      cut_tac bs=a in Bits__toNat_bound, auto)

lemma C__toNat_in_range_uint [simp]:
  "\<lbrakk>C__typeBits (C__typeOfValue val) = C__int_bits;
    C__bitsOfIntegerValue val = C__OC__ok a;
    C__unsignedIntegerType_p (C__typeOfValue val) \<or>
       C__plainCharsAreUnsigned \<and> C__typeOfValue val = C__Type__char\<rbrakk>
    \<Longrightarrow> int (toNat a)
           \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__uint)"
  by (subst C__rangeOfIntegerType_unsigned3, simp add: C__IntTypes,
      frule C__bitsOfIntegerValue_length, simp,
      cut_tac bs=a in Bits__toNat_bound, auto)


lemma C__toNat_in_range_ulong [simp]:
  "\<lbrakk>C__typeBits (C__typeOfValue val) = C__long_bits;
    C__bitsOfIntegerValue val = C__OC__ok a;
    C__unsignedIntegerType_p (C__typeOfValue val) \<or>
       C__plainCharsAreUnsigned \<and> C__typeOfValue val = C__Type__char\<rbrakk>
    \<Longrightarrow> int (toNat a)
           \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__ulong)"
  by (subst C__rangeOfIntegerType_unsigned3, simp add: C__IntTypes,
      frule C__bitsOfIntegerValue_length, simp,
      cut_tac bs=a in Bits__toNat_bound, auto)


lemma C__toNat_in_range_ullong [simp]:
  "\<lbrakk>C__typeBits (C__typeOfValue val) = C__llong_bits;
    C__bitsOfIntegerValue val = C__OC__ok a;
    C__unsignedIntegerType_p (C__typeOfValue val) \<or>
       C__plainCharsAreUnsigned \<and> C__typeOfValue val = C__Type__char\<rbrakk>
    \<Longrightarrow> int (toNat a)
           \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType C__Type__ullong)"
  apply (subst C__rangeOfIntegerType_unsigned3, simp add: C__IntTypes,
      frule C__bitsOfIntegerValue_length, simp,
      cut_tac bs=a in Bits__toNat_bound, auto)

(******************************************************************************)

end-proof

proof Isa mathIntOfValue_Obligation_subtype
  by (drule sym, case_tac val, 
      auto simp add: length_greater_0_conv [symmetric] 
           simp del: length_greater_0_conv
           split: split_if_asm)
(******************************************************************************)
(* The following lemmas should come earlier                                   *)
(******************************************************************************)



(******************************************************************************)
(** Value of Bits **)
(******************************************************************************)


lemma C__valueOfBits_type [simp]:
  "\<lbrakk>C__integerType_p ty; length bits = C__typeBits ty\<rbrakk>
  \<Longrightarrow> C__typeOfValue (C__valueOfBits (bits, ty)) = ty"
 by (simp add: C__valueOfBits_def, rule the1I2, 
     rule C__valueOfBits_Obligation_the, auto)

lemma C__valueOfBits_val [simp]:
  "\<lbrakk>C__integerType_p ty; length bits = C__typeBits ty\<rbrakk>
  \<Longrightarrow> C__bitsOfIntegerValue (C__valueOfBits (bits, ty)) = C__OC__ok bits"
 by (simp add: C__valueOfBits_def, rule the1I2, 
     rule C__valueOfBits_Obligation_the, auto)

lemma C__valueOfBits_unique: 
  "\<lbrakk>length bits = C__typeBits ty; C__typeOfValue val = ty; 
     C__bitsOfIntegerValue val = C__OC__ok bits
   \<rbrakk> \<Longrightarrow>  val = C__valueOfBits(bits,ty)"
  by (simp add: C__valueOfBits_def,
       rule the_equality [symmetric], simp,
       cut_tac C__valueOfBits_Obligation_the, 
       auto simp add: C__bitsOfIntV)

lemma C__valueOfBits_inv [simp]: 
  "\<lbrakk>length bits = C__typeBits ty; C__typeOfValue val = ty; 
     C__bitsOfIntegerValue val = C__OC__ok bits
   \<rbrakk> \<Longrightarrow>  C__valueOfBits(bits, ty) = val"
  by (simp add: C__valueOfBits_unique [symmetric])

(********** this is a very important theorem about defs with THE
            try to prove for all such defs where possible 
 *************************************************************************)

(********* now individual cases C__valueOfBits ***********)

lemma C__valueOfBits_char [simp]:
  "\<lbrakk>length bs = C__CHAR_BIT\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__char) = C__Value__char (Abs_Bits__Byte bs)"
 by simp

lemma C__valueOfBits_schar [simp]:
  "\<lbrakk>length bs = C__CHAR_BIT\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__schar) = C__Value__schar (Abs_Bits__Byte bs)"
 by simp

lemma C__valueOfBits_sshort [simp]:
  "\<lbrakk>length bs = C__short_bits\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__sshort) = C__Value__sshort (Abs_C__ShortWord bs)"
by simp

lemma C__valueOfBits_sint [simp]:
  "\<lbrakk>length bs = C__int_bits\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__sint) = C__Value__sint (Abs_C__IntWord bs)"
by simp

lemma C__valueOfBits_slong [simp]:
  "\<lbrakk>length bs = C__long_bits\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__slong) = C__Value__slong (Abs_C__LongWord bs)"
by simp

lemma C__valueOfBits_sllong [simp]:
  "\<lbrakk>length bs = C__llong_bits\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__sllong) = C__Value__sllong (Abs_C__LongLongWord bs)"
by simp

lemma C__valueOfBits_uchar [simp]:
  "\<lbrakk>length bs = C__CHAR_BIT\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__uchar) = C__Value__uchar (Abs_Bits__Byte bs)"
by simp

lemma C__valueOfBits_ushort [simp]:
  "\<lbrakk>length bs = C__short_bits\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__ushort) = C__Value__ushort (Abs_C__ShortWord bs)"
by simp

lemma C__valueOfBits_uint [simp]:
  "\<lbrakk>length bs = C__int_bits\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__uint) = C__Value__uint (Abs_C__IntWord bs)"
by simp

lemma C__valueOfBits_ulong [simp]:
  "\<lbrakk>length bs = C__long_bits\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__ulong) = C__Value__ulong (Abs_C__LongWord bs)"
by simp

lemma C__valueOfBits_ullong [simp]:
  "\<lbrakk>length bs = C__llong_bits\<rbrakk> \<Longrightarrow>
     C__valueOfBits (bs, C__Type__ullong) = C__Value__ullong (Abs_C__LongLongWord bs)"
apply simp

(******************************************************************************)


end-proof

proof Isa mathIntOfValue_Obligation_subtype0
  by (drule sym, case_tac val, 
      auto simp add: length_greater_0_conv [symmetric] 
           simp del: length_greater_0_conv
           split: split_if_asm)
end-proof

(* Dummy theorem to allow inserting lemmas *)

theorem mathIntOfValue_props is 0 = 0

proof Isa C__mathIntOfValue_props 
  by auto
(******************************************************************************)
lemma C__mathIntOfValue_char_u [simp]:
  "C__plainCharsAreUnsigned  \<Longrightarrow> 
     C__mathIntOfValue (C__Value__char bits)
   = C__OC__ok (int (toNat (Rep_Bits__Byte bits)))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_char_s [simp]:
  "C__plainCharsAreSigned  \<Longrightarrow> 
     C__mathIntOfValue (C__Value__char bits)
   = C__OC__ok (TwosComplement__toInt (Rep_Bits__Byte bits))"
  by (simp add: C__mathIntOfValue_def C__IntTypes C__plainCharsAreUnsigned_def)

lemma C__mathIntOfValue_uchar [simp]:
  "C__mathIntOfValue (C__Value__uchar bits)
   = C__OC__ok (int (toNat (Rep_Bits__Byte bits)))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_schar [simp]:
  "C__mathIntOfValue (C__Value__schar bits)
   = C__OC__ok (TwosComplement__toInt (Rep_Bits__Byte bits))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_ushort [simp]:
  "C__mathIntOfValue (C__Value__ushort bits)
   = C__OC__ok (int (toNat (Rep_C__ShortWord bits)))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_sshort [simp]:
  "C__mathIntOfValue (C__Value__sshort bits)
   = C__OC__ok (TwosComplement__toInt (Rep_C__ShortWord bits))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_uint [simp]:
  "C__mathIntOfValue (C__Value__uint bits)
   = C__OC__ok (int (toNat (Rep_C__IntWord bits)))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_sint [simp]:
  "C__mathIntOfValue (C__Value__sint bits)
   = C__OC__ok (TwosComplement__toInt (Rep_C__IntWord bits))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_ulong [simp]:
  "C__mathIntOfValue (C__Value__ulong bits)
   = C__OC__ok (int (toNat (Rep_C__LongWord bits)))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_slong [simp]:
  "C__mathIntOfValue (C__Value__slong bits)
   = C__OC__ok (TwosComplement__toInt (Rep_C__LongWord bits))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_ullong [simp]:
  "C__mathIntOfValue (C__Value__ullong bits)
   = C__OC__ok (int (toNat (Rep_C__LongLongWord bits)))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_sllong [simp]:
  "C__mathIntOfValue (C__Value__sllong bits)
   = C__OC__ok (TwosComplement__toInt (Rep_C__LongLongWord bits))"
  by (simp add: C__mathIntOfValue_def C__IntTypes)

lemma C__mathIntOfValue_is_defined [simp]:
   "C__mathIntOfValue val = C__OC__ok a
      \<Longrightarrow> val \<noteq>  C__Value__undefined ty"
  by (simp add: C__mathIntOfValue_def C__bitsOfIntV split: C__OC.split_asm)

lemma C__mathIntOfValue_int_p:
   "C__mathIntOfValue val = C__OC__ok a
    \<Longrightarrow> C__integerType_p (C__typeOfValue val)"
  by (simp add: C__mathIntOfValue_def C__bitsOfIntV split: C__OC.split_asm)


lemma C__mathIntOfValue_bits:
  "\<lbrakk>C__mathIntOfValue x = C__OC__ok i\<rbrakk>
    \<Longrightarrow> \<exists>bs. C__bitsOfIntegerValue x = C__OC__ok bs
             \<and> length bs = C__typeBits (C__typeOfValue x)"
   by (simp add: C__mathIntOfValue_def split: C__OC.split_asm,
       rule C__bitsOfIntegerValue_length2, simp_all)


lemma C__mathIntOfValue_type:
  "\<lbrakk>C__mathIntOfValue val = C__OC__ok i\<rbrakk>
   \<Longrightarrow> i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType (C__typeOfValue val))"
 apply (frule_tac C__mathIntOfValue_bits, auto,
        frule C___bitsOfIntegerValue_is_pos,
        frule C__mathIntOfValue_int_p,  drule sym,
        simp add: C__mathIntOfValue_def C__Range
                split: C__OC.split_asm split_if_asm)
 apply (drule Bits__toNat_bound, simp)
 apply (frule TwosComplement__integer_range, simp add: TwosComplement_tcN)
done

lemma C__mathIntOfValue_inject_rule:
  "\<lbrakk>C__mathIntOfValue x = C__OC__ok i; 
    C__mathIntOfValue y = C__OC__ok i; 
    C__typeOfValue x =  C__typeOfValue y\<rbrakk>
    \<Longrightarrow> x = y"
 apply (case_tac x, 
        auto simp add: C__mathIntOfValue_def C__BitTypes C__IntTypes
                split: C__OC.split_asm split_if_asm)
 apply (case_tac y, auto simp add: C__IntTypes)
 apply (case_tac y, auto simp add: C__IntTypes)
 apply (case_tac y, auto simp add: C__IntTypes)
 apply (case_tac y, auto simp add: C__IntTypes, 
        drule TwosComplement__toInt_inject_rule, 
        simp_all add:  C__bitsOfIntegerValue_length)+
 apply (case_tac y, auto simp add: C__IntTypes)
 apply (case_tac y, auto simp add: C__IntTypes,
        drule Bits__toNat_inject_rule, 
        simp_all add:  C__bitsOfIntegerValue_length)+
 apply (case_tac y, auto simp add: C__IntTypes)
done  


lemma C__mathIntOfValue_inject_bits:
   "\<lbrakk>C__bitsOfIntegerValue val = C__OC__ok bits;
     C__integerType_p (C__typeOfValue x);
     C__typeBits (C__typeOfValue x) =
     C__typeBits (C__typeOfValue val);
     C__mathIntOfValue val = C__OC__ok a;
     C__mathIntOfValue x = C__OC__ok a;
     a \<in> Rep_C__FiniteSetInt
              (C__rangeOfIntegerType (C__typeOfValue x))\<rbrakk>
     \<Longrightarrow> C__bitsOfIntegerValue x = C__OC__ok bits"
 apply (frule_tac x=x in C__mathIntOfValue_bits, auto)
 apply (frule C___bitsOfIntegerValue_is_pos,
        frule_tac val=x in C___bitsOfIntegerValue_is_pos,
        drule C__bitsOfIntegerValue_length, simp,
        cut_tac C__bitsOfIntegerValue_length2 [symmetric], 
        simp_all, rotate_tac -1, thin_tac "?P")
 apply (simp add: C__mathIntOfValue_def
                split: C__OC.split_asm split_if_asm)
 apply clarsimp
 apply (clarsimp, cut_tac TwosComplement__toInt_nat, simp_all)
 apply (clarsimp, cut_tac i="toNat bs" in TwosComplement__toInt_nat, 
                  simp_all, simp)
 apply clarsimp
done

lemma C__mathIntOfValue_extend:
  "\<lbrakk>C__mathIntOfValue x = C__OC__ok i; 
    C__mathIntOfValue y = C__OC__ok i; 
    C__typeBits (C__typeOfValue x) < len;
    C__typeBits (C__typeOfValue y) = len;
    C__bitsOfIntegerValue x = C__OC__ok bs;
    C__bitsOfIntegerValue y = C__OC__ok bs2\<rbrakk>
    \<Longrightarrow> bs2 = List__extendLeft (bs, hd bs2, len)"
   apply (frule C___bitsOfIntegerValue_is_pos,
          drule C__bitsOfIntegerValue_length, simp,
          cut_tac C__bitsOfIntegerValue_length2 [symmetric], 
          simp_all, rotate_tac -1, thin_tac "?P")
   apply (clarsimp simp add: C__mathIntOfValue_def 
                      split: C__OC.split_asm split_if_asm)
   apply (cut_tac bs=bs2 in Bits__toNat_small_hd, simp_all,
          erule Bits__extendLeft_toNat, simp_all)
   apply (cut_tac TwosComplement__toInt_nat, simp_all del: length_greater_0_conv,
          cut_tac bs=bs2 in Bits__toNat_small_hd, simp_all,
          erule Bits__extendLeft_toNat, simp_all)
   apply (cut_tac i="toNat bs2" in TwosComplement__toInt_nat, simp_all,
          rotate_tac -2, thin_tac ?P, drule sym,
          cut_tac bs=bs2 in Bits__toNat_small_hd, simp_all,
          erule Bits__extendLeft_toNat, simp_all)
   apply (cases "hd bs2", simp_all)
   apply (rule TwosComplement_extendLeft_tcInt_pos, simp_all, simp add: TwosComplementInt)
   apply (rule TwosComplement_extendLeft_tcInt_neg, simp_all, 
          simp add: TwosComplementInt split: split_if_asm,
          cut_tac bs=bs2 in Bits_bound_neg, simp_all del: length_greater_0_conv)
done

(******************************************************************************)
end-proof 

proof Isa valueOfMathInt_Obligation_the
  apply (cases "C__unsignedIntegerType_p ty \<or>
                   C__plainCharsAreUnsigned \<and> ty = C__Type__char",
         simp_all add: C__Range)  
  apply (rule_tac a="C__valueOfBits(toBits (nat i, C__typeBits ty), ty)" in ex1I)
  apply (clarsimp, 
         drule_tac C__unsigned_cases2, cases ty, 
         simp_all add:  C__Words C__plainCharsAreUnsigned_def)
  apply (rule C__valueOfBits_unique, simp_all,
         clarsimp simp add: C__mathIntOfValue_def  C__plainCharsAreUnsigned_def
                            C__bitsOfIntV
                     split: C__OC.split_asm)
  apply (rule_tac a="C__valueOfBits 
                     (TwosComplement__tcNumber (i, C__typeBits ty), ty)" in ex1I)
  apply (drule_tac C__signed_cases2, 
         simp, simp add: C__plainCharsAreUnsigned_def,
         cases ty, simp_all add: C__Words, simp_all add: TwosComplement_tcN)
  apply (rule C__valueOfBits_unique, simp_all,
         auto simp add: C__mathIntOfValue_def  C__plainCharsAreUnsigned_def
                            C__bitsOfIntV
                     split: C__OC.split_asm)
end-proof


proof Isa C__valueOfMathInt_props 
  by auto
(******************************************************************************)

(******************************************************************************)
(** Value of MathInt **)
(******************************************************************************)

(* Dummy theorem to allow inserting lemmas *)

theorem valueOfMathInt_props is 0 = 0

lemma C__valueOfMathInt_type [simp]:
  "\<lbrakk>C__integerType_p ty; 
    i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)\<rbrakk> \<Longrightarrow> 
    C__typeOfValue (C__valueOfMathInt (i,ty)) = ty"
  by (simp add: C__valueOfMathInt_def, rule the1I2, 
      auto simp add: C__valueOfMathInt_Obligation_the)

lemma C__valueOfMathInt_val [simp]:
  "\<lbrakk>C__integerType_p ty; 
    i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)\<rbrakk> \<Longrightarrow> 
    C__mathIntOfValue (C__valueOfMathInt (i,ty)) =  C__OC__ok i"
  by (simp add: C__valueOfMathInt_def, rule the1I2, 
      auto simp add: C__valueOfMathInt_Obligation_the)

lemma C__valueOfMathInt_unique:
  "\<lbrakk>i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty);
    C__typeOfValue x = ty; C__mathIntOfValue x = C__OC__ok i\<rbrakk>
   \<Longrightarrow> x = C__valueOfMathInt (i, ty)"
 apply (simp add: C__valueOfMathInt_def, rule the1I2, 
        rule C__valueOfMathInt_Obligation_the, 
        auto simp add: C__mathIntOfValue_int_p)
 apply (drule C__mathIntOfValue_inject_rule, auto)
done
 
lemma C__valueOfMathInt_signed:
  "\<lbrakk>C__integerType_p ty; \<not> (C__unsignedIntegerType_p ty); 
    C__plainCharsAreUnsigned \<longrightarrow> ty \<noteq> C__Type__char; 
    i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)\<rbrakk>
  \<Longrightarrow> C__valueOfMathInt (i, ty) = 
      C__valueOfBits (TwosComplement__tcNumber (i, C__typeBits ty),ty)"
 by (simp add: C__valueOfMathInt_def, rule the1I2, 
     rule C__valueOfMathInt_Obligation_the, 
     auto simp add: C__mathIntOfValue_def C__Range  C__bitsOfIntV
           split: C__OC.split_asm)

 
lemma C__valueOfMathInt_unsigned:
  "\<lbrakk>C__unsignedIntegerType_p ty \<or>
    ty = C__Type__char \<and> C__plainCharsAreUnsigned; 
    i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)\<rbrakk>
  \<Longrightarrow> C__valueOfMathInt (i, ty) = 
       C__valueOfBits (toBits(nat i, C__typeBits ty),ty)"
 by (simp add: C__valueOfMathInt_def, rule the1I2, 
     rule C__valueOfMathInt_Obligation_the, 
     auto simp add: C__mathIntOfValue_def C__Range  C__bitsOfIntV
             split: C__OC.split_asm,
     case_tac x, auto) 


(********* now individual cases C__valueOfMathInt ****)

lemma C__valueOfMathInt_char_u [simp]:
  "\<lbrakk>C__plainCharsAreUnsigned;  C__CHAR_MIN \<le> i; i \<le> int C__CHAR_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__char)
        = C__Value__char (Bits__byte (nat i))"
  by (subst C__valueOfMathInt_unsigned, 
      simp_all add: C__Range C__MinMax Bits__byte_def)

lemma C__valueOfMathInt_char_s [simp]:
  "\<lbrakk>C__plainCharsAreSigned;  C__CHAR_MIN \<le> i; i \<le> int C__CHAR_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__char)
      = C__Value__char (Abs_Bits__Byte (TwosComplement__tcNumber (i, 8)))"
  by (subst C__valueOfMathInt_signed, simp_all add: C__Range C__MinMax)

lemma C__valueOfMathInt_uchar [simp]:
  "\<lbrakk>0 \<le> i; i \<le> int C__UCHAR_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__uchar)
        = C__Value__uchar (Bits__byte (nat i))"
  by (subst C__valueOfMathInt_unsigned, 
      simp_all add: C__Range C__MinMax C__IntTypes Bits__byte_def)

lemma C__valueOfMathInt_schar [simp]:
  "\<lbrakk>C__SCHAR_MIN \<le> i; i \<le> int C__SCHAR_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__schar)
      = C__Value__schar (Abs_Bits__Byte (TwosComplement__tcNumber (i, 8)))"
  by (subst C__valueOfMathInt_signed, 
      simp_all add: C__Range C__MinMax C__IntTypes)

lemma C__valueOfMathInt_ushort [simp]:
  "\<lbrakk>0 \<le> i; i \<le> int C__USHRT_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__ushort)
        = C__Value__ushort (Abs_C__ShortWord (toBits (nat i, C__short_bits)))"
  by (subst C__valueOfMathInt_unsigned, 
      simp_all add: C__Range C__MinMax C__IntTypes)

lemma C__valueOfMathInt_sshort [simp]:
  "\<lbrakk>C__SHRT_MIN \<le> i; i \<le> int C__SHRT_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__sshort)
      = C__Value__sshort (Abs_C__ShortWord (TwosComplement__tcNumber (i, C__short_bits)))"
  by (subst C__valueOfMathInt_signed, 
      simp_all add: C__Range C__MinMax C__IntTypes)

lemma C__valueOfMathInt_uint [simp]:
  "\<lbrakk>0 \<le> i; i \<le> int C__UINT_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__uint)
        = C__Value__uint (Abs_C__IntWord (toBits (nat i, C__int_bits)))"
  by (subst C__valueOfMathInt_unsigned, 
      simp_all add: C__Range C__MinMax C__IntTypes)

lemma C__valueOfMathInt_sint [simp]:
  "\<lbrakk>C__INT_MIN \<le> i; i \<le> int C__INT_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__sint)
      = C__Value__sint (Abs_C__IntWord (TwosComplement__tcNumber (i, C__int_bits)))"
  by (subst C__valueOfMathInt_signed, 
      simp_all add: C__Range C__MinMax C__IntTypes)

lemma C__valueOfMathInt_ulong [simp]:
  "\<lbrakk>0 \<le> i; i \<le> int C__ULONG_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__ulong)
        = C__Value__ulong (Abs_C__LongWord (toBits (nat i, C__long_bits)))"
  by (subst C__valueOfMathInt_unsigned, 
      simp_all add: C__Range C__MinMax C__IntTypes)

lemma C__valueOfMathInt_slong [simp]:
  "\<lbrakk>C__LONG_MIN \<le> i; i \<le> int C__LONG_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__slong)
      = C__Value__slong (Abs_C__LongWord (TwosComplement__tcNumber (i, C__long_bits)))"
  by (subst C__valueOfMathInt_signed, 
      simp_all add: C__Range C__MinMax C__IntTypes)

lemma C__valueOfMathInt_ullong [simp]:
  "\<lbrakk>0 \<le> i; i \<le> int C__ULLONG_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__ullong)
        = C__Value__ullong (Abs_C__LongLongWord (toBits (nat i, C__llong_bits)))"
  by (subst C__valueOfMathInt_unsigned, 
      simp_all add: C__Range C__MinMax C__IntTypes)

lemma C__valueOfMathInt_sllong [simp]:
  "\<lbrakk>C__LLONG_MIN \<le> i; i \<le> int C__LLONG_MAX\<rbrakk>
   \<Longrightarrow> C__valueOfMathInt (i, C__Type__sllong)
      = C__Value__sllong (Abs_C__LongLongWord (TwosComplement__tcNumber (i, C__llong_bits)))"
  by (subst C__valueOfMathInt_signed, 
      simp_all add: C__Range C__MinMax C__IntTypes)

lemmas C__MathInt = C__valueOfMathInt_char_u     
                    C__valueOfMathInt_char_s     
                    C__valueOfMathInt_uchar      
                    C__valueOfMathInt_schar      
                    C__valueOfMathInt_ushort
                    C__valueOfMathInt_sshort    
                    C__valueOfMathInt_uint    
                    C__valueOfMathInt_sint    
                    C__valueOfMathInt_ulong    
                    C__valueOfMathInt_slong    
                    C__valueOfMathInt_ullong    
                    C__valueOfMathInt_sllong    

(******************************************************************************)
lemma C__MathInt_dummy: "True" 
  apply auto
(******************************************************************************)

end-proof


proof Isa zero_of_integer_type_is_all_zeros_Obligation_subtype
  by (simp add: C__scalarType_p_def  C__arithmeticType_p_def)
end-proof


proof Isa C__zero_of_integer_type_is_all_zeros
  apply (simp add: C__zeroOfScalarType_def C__valueOfMathInt_def) 
  apply (rule the1I2, rule C__valueOfMathInt_Obligation_the,
         simp_all add: C__zeroOfScalarType_Obligation_subtype 
                       C__scalarType_p_def  C__arithmeticType_p_def,
         erule conjE)
  apply (simp add: C__mathIntOfValue_def split: C__OC.split_asm)
  apply (frule C__bitsOfIntegerValue_length2, simp_all)
  apply (simp add: Bits__toNat_zero_val TwosComplement__toInt_zero_val
                  split: split_if_asm)
end-proof

proof Isa FunctionsInfo -typedef
sorry
end-proof

proof Isa updateStaticObject_Obligation_subtype
 (** Conclusion must be 
   Map__finite_p
      (Map__update (Rep_C__FMapIdVal (C__Storage__static (C__State__storage state))) name val) 
  **)
  by auto
(******************************************************************************)
(*********** move these up (dummy theorem) ************************************)

lemma C__zeroScalarValue_1 [simp]:
"C__zeroScalarValue_p C__int1 = C__OC__ok False"
  apply (cut_tac  C__min_INT_MIN, cut_tac C__min_INT_MAX, cut_tac C__min_UINT_MAX,
         simp add: C__int1_def C__zeroScalarValue_p_def C__scalarValue_p_def
                   C__zeroOfScalarType_def C__scalarType_p_def
                   C__arithmeticType_p_def C__valueOfMathInt_sint
                   int_power_simp)
  apply (rule allI, rule impI, 
         drule C__integerType_cases, case_tac ty,
         simp_all add: C__MinMax Abs_C__IntWord_inject C__Words int_power_simp)
  apply (cases C__plainCharsAreUnsigned, simp_all add: C__MinMax)
done

lemma C__zeroScalarValue_0 [simp]:
"C__zeroScalarValue_p C__int0 = C__OC__ok True"
  by (auto simp add: C__int0_def C__zeroScalarValue_p_def 
                     C__zeroOfScalarType_def C__scalarValue_p_def 
                     C__scalarType_p_def C__IntTypes
              split: C__Value.split_asm)


lemma C__typeOfValue_zero [simp]:
  "\<lbrakk>C__integerType_p ty\<rbrakk> \<Longrightarrow> C__typeOfValue (C__zeroOfScalarType ty) = ty" 
  by (simp add: C__zeroOfScalarType_def)

lemma C__zeroOfScalarType_uchar:
  "C__zeroOfScalarType C__Type__uchar = C__Value__uchar (Bits__byte 0)"
  by (simp add: C__zeroOfScalarType_def)

lemma C__typeOfValue_zero_uchar [simp]:
  "C__typeOfValue (C__zeroOfScalarType C__Type__uchar) = C__Type__uchar" 
  apply (simp add: C__zeroOfScalarType_uchar)
(******************************************************************************)
(** The definition below there misses conversions. The correct version is 

defs C__updateStaticObject_def: 
  "C__updateStaticObject
     \<equiv> (\<lambda> ((state::C__State), (name::C__Identifier), (val::C__Value)). 
          C__updateStaticStorage
            (state, 
             Abs_C__FMapIdVal
                (Map__update (Rep_C__FMapIdVal (C__Storage__static (C__State__storage state))) name
                    val)))"

**)
(******************************************************************************)
end-proof

proof Isa scopeOfObject_Obligation_subtype5
  by (simp add: null_def)
end-proof

proof Isa  scopeOfObject () 
 by auto
termination 
 apply (relation "measure (\<lambda>(state, name).  
                   size (C__Storage__automatic (C__State__storage state)) 
                 * (size (last (C__Storage__automatic (C__State__storage state)))
                 + 1))")
 apply (simp_all add: C__updateAutomaticFrame_def 
                      C__updateAutomaticStorage_def null_def domIff
                      last_list_update)
end-proof

proof Isa readTopObject_Obligation_subtype
  (* unprovable because something's missing in the translation *)
  sorry
end-proof

proof Isa readTopObject_Obligation_subtype0
  (* unprovable because something's missing in the translation *)
  sorry
end-proof

proof Isa writeTopObject_Obligation_subtype
 (* we're missing the same as above *)
 by (simp add: C__readTopObject_Obligation_subtype 
               C__readTopObject_Obligation_subtype0)

end-proof


proof Isa  readObject () 
 by (pat_completeness, auto)
termination
 (* eliminate the Rep_C__FMapIdVal  in "case Rep_C__FMapIdVal members mem__v" *)
 by (relation "measure (\<lambda>(state, obj).  size obj)", auto)
end-proof



proof Isa  writeObject () 
 by (pat_completeness, auto)
termination
 (* eliminate the two Rep_C__FMapIdVal  *)
 by (relation "measure (\<lambda>(state, obj, newval).  size obj)", auto)
end-proof


proof Isa objectTableOfNamedStorage_Obligation_subtype
 (****** Globally replace mapOption by Option.map  *******)
  by (simp add: comp_def dom_option_map)
end-proof

proof Isa functionTableOfFunctionsInfo_Obligation_subtype
 (* correct translation is 
  
   Map__finite_p
      (Option.map
          (\<lambda> (funinfo::C__FunctionInfo). 
             (C__FunctionInfo__return funinfo, 
              C__FunctionInfo__parameters funinfo)) 
         o Rep_Map__FiniteMap funsinfo)"

  similarly in subsequent def
  *******)
  by (simp add: comp_def dom_option_map)

end-proof

proof Isa  functionBodiesOK_p_Obligation_subtype0
  apply (simp add: distinct_map) (* unprovable, generated statement is wrong *)
  sorry
end-proof


proof Isa functionBodiesOK_p_Obligation_subtype1
  (* Globally replace (Rep_C__Identifier name) by name *)
  by (simp add: C__symbolTableOfState_def C__objectTableOfStorage_def)
end-proof


proof Isa functionBodiesOK_p_Obligation_subtype3
  (* remove Rep_C__Identifier *)
  by (simp only: C__functionBodiesOK_p_Obligation_subtype0)
end-proof


proof Isa C__convertInteger_Obligation_subtype
  by (drule C__maxOfIntegerType_Obligation_exhaustive, auto) 

(******************************************************************************)
theorem C__convertInteger_Obligation_the2: 
  "\<lbrakk>C__integerType_p ty;  
    \<not> (x \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)); 
    C__unsignedIntegerType_p ty 
      \<or> C__plainCharsAreUnsigned \<and> ty = C__Type__char\<rbrakk> \<Longrightarrow> 
   \<exists>!(i'::int). 
     i' \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty) 
       \<and> (\<exists>(k::int). 
            i' = x + k * (C__maxOfIntegerType ty + 1))"
   apply (drule C__unsigned_cases2, cases ty, 
          simp_all add: 
                   C__rangeOfIntegerType_def 
                   C__rangeOfIntegerType_Obligation_subtype
                   C__FiniteSetInt_def, 
          simp_all add: mem_def not_le)
   apply (cut_tac z="C__maxOfIntegerType ty" and x=x in zmod_unique,
          simp, simp add: C__plainCharsAreUnsigned_def C__MinMax)+
done

lemma C__convertInteger_THE_simp:
   "\<lbrakk>a \<notin> Rep_C__FiniteSetInt (C__rangeOfIntegerType newty);
     C__unsignedIntegerType_p newty \<or>
        C__plainCharsAreUnsigned \<and> newty = C__Type__char
    \<rbrakk>
    \<Longrightarrow> (THE i'.
            i' \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType newty) \<and>
            (\<exists>k. i' = a + k * (C__maxOfIntegerType newty + 1)))
           = a mod (2 ^ (C__typeBits newty))"
   apply (rule the1_equality,
          rule C__convertInteger_Obligation_the2, simp_all)
   apply (thin_tac ?P, subst C__maxOfIntegerType_unsigned, clarify)
   apply (simp add: C__Range, 
          rule_tac x="-(a div 2 ^ C__typeBits newty)" in exI, 
          simp add: zmod_zdiv_equality')
(******************************************************************************)

end-proof

proof Isa  C__convertInteger_Obligation_the
 by (simp add: C__convertInteger_Obligation_the2)
end-proof

proof Isa C__convertInteger_Obligation_subtype0
  by (rule the1I2, auto simp add: C__convertInteger_Obligation_the)
end-proof

proof Isa  C__convertInteger_zero_extension_Obligation_subtype
  by (auto simp add: C__integerType_p_def)
end-proof

proof Isa C__convertInteger_zero_extension_Obligation_subtype0
   by (simp add: C__bitsOfIntV)

(******************************************************************************)
lemma C__convertInteger_sint_sint [simp]:
  "C__convertInteger (C__Value__sint val, C__Type__sint)
                      = C__OC__ok (C__Value__sint val)"
  by (simp add: C__convertInteger_def C__valueOfMathInt_signed C__IntTypes)

lemma C__convertInteger_uchar_sint [simp]:
  "\<lbrakk>i < 2 ^ 8\<rbrakk> \<Longrightarrow> 
   C__convertInteger (C__Value__uchar (Bits__byte i), C__Type__sint)
   = 
   C__OC__ok (C__Value__sint (Abs_C__IntWord
                (TwosComplement__tcNumber (int i, C__int_bits))))"
  by (cut_tac C__min_INT_MIN, cut_tac C__min_INT_MAX, 
         simp add: C__convertInteger_def)

lemma C__convertInteger_uchar_uchar [simp]:
  "\<lbrakk>i < 2 ^ 8\<rbrakk> \<Longrightarrow> 
   C__convertInteger (C__Value__uchar (Bits__byte i), C__Type__uchar) 
                      = C__OC__ok (C__Value__uchar (Bits__byte i))"
  by (simp add: C__convertInteger_def)

lemma C__convertInteger_tcNumber_sint_uchar [simp]:
 "\<lbrakk>0 \<le> i; i < 2 ^ 8\<rbrakk> \<Longrightarrow>
   C__convertInteger (C__Value__sint (Abs_C__IntWord 
              (TwosComplement__tcNumber (i, C__int_bits))), C__Type__uchar)
   = C__OC__ok (C__Value__uchar (Bits__byte (nat i)))"
  by (cut_tac C__min_INT_MIN, cut_tac C__min_INT_MAX,
      simp add: C__convertInteger_def  C__Words C__MinMax 
                TwosComplement_toInt_bits_pos)

lemma  C__convertInteger_int_p:
     "C__convertInteger (val, newty) = C__OC__ok newval
      \<Longrightarrow> C__integerType_p (C__typeOfValue val)"
  by (simp add: C__convertInteger_def C__mathIntOfValue_int_p
           split: C__OC.split_asm)

lemma  C__convertInteger_is_defined [simp]:
     "C__convertInteger (val, newty) = C__OC__ok newval
      \<Longrightarrow> val \<noteq>  C__Value__undefined ty"
  by (simp add:  C__convertInteger_def split: C__OC.split_asm)

lemma C__convertInteger_type: 
  "\<lbrakk>C__integerType_p ty; C__convertInteger(val, ty) = C__OC__ok newval\<rbrakk>
    \<Longrightarrow> C__typeOfValue newval = ty"
   apply (clarsimp simp add: C__convertInteger_def not_le 
                      split: C__OC.split_asm split_if_asm)
   apply (rule C__valueOfMathInt_type, simp,
          rule the1I2, rule C__convertInteger_Obligation_the, simp_all)
done


lemma C__convertInteger_val1: 
  "\<lbrakk>C__integerType_p ty; C__convertInteger(val, ty) = C__OC__ok newval;
    C__mathIntOfValue val = C__OC__ok i;
    i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)\<rbrakk>
    \<Longrightarrow>  C__mathIntOfValue newval = C__OC__ok i"
   by (auto simp add: C__convertInteger_def)

lemma C__convertInteger_val2: 
  "\<lbrakk>C__integerType_p ty; C__convertInteger(val, ty) = C__OC__ok newval;
    C__mathIntOfValue val = C__OC__ok i;
    i \<notin> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)\<rbrakk>
    \<Longrightarrow>  C__mathIntOfValue newval = 
          C__OC__ok (THE z. z \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)
                      \<and> (\<exists>k. z = i + k * (C__maxOfIntegerType ty + 1)))"
   by (clarsimp simp add: C__convertInteger_def split: split_if_asm,
       rule the1I2, rule C__convertInteger_Obligation_the, simp_all)

lemma C__convertInteger_unique1: 
  "\<lbrakk>i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty);
    C__typeOfValue val = ty; C__mathIntOfValue val = C__OC__ok i\<rbrakk>
    \<Longrightarrow>   C__OC__ok val = C__convertInteger(val, ty)"
  by (auto simp add: C__valueOfMathInt_unique C__convertInteger_def)


lemma C__convertInteger_unique2: 
  "\<lbrakk>C__unsignedIntegerType_p ty 
      \<or> C__plainCharsAreUnsigned \<and> ty = C__Type__char;
     C__mathIntOfValue val = C__OC__ok i;
     i \<notin> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty);
     C__typeOfValue newval = ty; 
     C__mathIntOfValue newval = 
      C__OC__ok (THE z. z \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty)
                      \<and> (\<exists>k. z = i + k * (C__maxOfIntegerType ty + 1)))\<rbrakk>
    \<Longrightarrow>   C__OC__ok newval = C__convertInteger(val, ty)"
  apply (simp add: C__convertInteger_def split: split_if_asm)
  apply (subst C__valueOfMathInt_unique, simp_all)
  apply (rule the1I2, rule C__convertInteger_Obligation_the, simp_all)
done

lemmas C__Convert =  C__convertInteger_int_p
                     C__convertInteger_type
                     C__convertInteger_val1
                     C__convertInteger_val2
                     C__convertInteger_unique1 [symmetric]
                     C__convertInteger_unique2 [symmetric]


(******************************************************************************)

lemma  C__convertInteger_zero_ext_len_aux:
  "\<lbrakk>len > 0; i < 2 ^ len; len < len2; C__typeBits ty2 = len2;
    C__integerType_p ty2 \<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue (C__valueOfMathInt (int i, ty2)) =
         C__OC__ok (List__extendLeft (toBits (i, len), B0, len2))"
   apply (clarsimp simp add:  C__valueOfMathInt_def,
          rule the1I2, rule C__valueOfMathInt_Obligation_the, simp_all)
   apply (auto simp add: C__mathIntOfValue_def 
               split: C__OC.split_asm)
   apply (cut_tac C__bitsOfIntegerValue_length2, 
          simp_all split: split_if_asm)
   apply (rule Bits__extendLeft_to_len_nat, 
          simp_all add: TwosComplement__toInt_nat)+
done


lemma C__convertInteger_zero_ext_len_char:
  "\<lbrakk>C__plainCharsAreUnsigned; 8 < newlen;
     C__convertInteger (C__Value__char (Abs_Bits__Byte y), newty) =
     C__OC__ok newval;
     length y = 8; 
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, B0, newlen))"
   apply (cut_tac bs=y in Bits__bits_surjective, auto)
   apply (frule_tac i=i in C__rangeOfIntegerType_int, 
          auto simp add: C__convertInteger_zero_ext_len_aux [symmetric]
                    C__convertInteger_def C__Words )
done


lemma C__convertInteger_zero_ext_len_uchar:
  "\<lbrakk> 8 < newlen;
     C__convertInteger (C__Value__uchar (Abs_Bits__Byte y), newty) =
     C__OC__ok newval;
     length y = 8; 
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, B0, newlen))"
   apply (cut_tac bs=y in Bits__bits_surjective, auto)
   apply (frule_tac i=i in C__rangeOfIntegerType_int, 
          auto simp add: C__convertInteger_zero_ext_len_aux [symmetric]
                    C__convertInteger_def C__Words )
done

lemma C__convertInteger_zero_ext_len_ushort:
  "\<lbrakk> C__short_bits < newlen;
     C__convertInteger (C__Value__ushort (Abs_C__ShortWord y), newty) =
     C__OC__ok newval;
     length y =  C__short_bits; 
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, B0, newlen))"
   apply (cut_tac bs=y in Bits__bits_surjective, auto)
   apply (frule_tac i=i in C__rangeOfIntegerType_int, 
          auto simp add: C__convertInteger_zero_ext_len_aux [symmetric]
                    C__convertInteger_def C__Words )
done

lemma C__convertInteger_zero_ext_len_uint:
  "\<lbrakk> C__int_bits < newlen;
     C__convertInteger (C__Value__uint (Abs_C__IntWord y), newty) =
     C__OC__ok newval;
     length y =  C__int_bits; 
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, B0, newlen))"
   apply (cut_tac bs=y in Bits__bits_surjective, auto)
   apply (frule_tac i=i in C__rangeOfIntegerType_int, 
          auto simp add: C__convertInteger_zero_ext_len_aux [symmetric]
                    C__convertInteger_def C__Words )
done


lemma C__convertInteger_zero_ext_len_ulong:
  "\<lbrakk> C__long_bits < newlen;
     C__convertInteger (C__Value__ulong (Abs_C__LongWord y), newty) =
     C__OC__ok newval;
     length y =  C__long_bits; 
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, B0, newlen))"
   apply (cut_tac bs=y in Bits__bits_surjective, auto)
   apply (frule_tac i=i in C__rangeOfIntegerType_int, 
          auto simp add: C__convertInteger_zero_ext_len_aux [symmetric]
                    C__convertInteger_def C__Words )
done

lemma C__convertInteger_zero_ext_len_ullong:
  "\<lbrakk> C__llong_bits < newlen;
     C__convertInteger (C__Value__ullong (Abs_C__LongLongWord y), newty) =
     C__OC__ok newval;
     length y =  C__llong_bits; 
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, B0, newlen))"
   apply (cut_tac bs=y in Bits__bits_surjective, auto)
   apply (frule_tac i=i in C__rangeOfIntegerType_int, 
          auto simp add: C__convertInteger_zero_ext_len_aux [symmetric]
                    C__convertInteger_def C__Words )

(** try to simplify into general lemma - the proof is always the same 
    use the lemmas in C__Convert and look at the "truncate" proof **)
(******************************************************************************)


end-proof

proof Isa C__convertInteger_zero_extension
   apply (frule C__unsigned_cases, cases val, auto)
   (** 6 cases ***)
   apply (case_tac Bits__Byte, clarsimp simp add: C__Words,
          cases newty, simp_all add: C__convertInteger_zero_ext_len_char)
   apply (case_tac Bits__Byte, clarsimp simp add: C__Words,
          cases newty, simp_all add: C__convertInteger_zero_ext_len_uchar)
   apply (case_tac C__IntWord, clarsimp simp add: C__Words,
          cases newty, simp_all add: C__convertInteger_zero_ext_len_uint)
   apply (case_tac C__LongLongWord, clarsimp simp add: C__Words,
          cases newty, simp_all add: C__convertInteger_zero_ext_len_ullong)
   apply (case_tac C__LongWord, clarsimp simp add: C__Words,
          cases newty, simp_all add: C__convertInteger_zero_ext_len_ulong)
   apply (case_tac C__ShortWord, clarsimp simp add: C__Words,
          cases newty, simp_all add: C__convertInteger_zero_ext_len_ushort)
end-proof

proof Isa C__convertInteger_sign_extension_Obligation_subtype
 by (auto simp add: C__integerType_p_def)
end-proof

proof Isa C__convertInteger_sign_extension_Obligation_subtype0
  by (simp add: C__bitsOfIntV length_greater_0_iff)
end-proof

proof Isa C__convertInteger_sign_extension_Obligation_subtype2
  by (simp add: C__bitsOfIntV)


(******************************************************************************)

lemma  C__convertInteger_sign_ext_len_pos_aux:
  "\<lbrakk>len > 0; 0 \<le> i; len < len2; C__typeBits ty2 = len2;
    i \<in> TwosComplement__rangeForLength len; C__integerType_p ty2 \<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue (C__valueOfMathInt (i, ty2)) =
         C__OC__ok (List__extendLeft (TwosComplement__tcNumber (i, len), B0, len2))"
   by  (simp add: TwosComplement_TC,
        frule_tac i="nat i" in C__convertInteger_zero_ext_len_aux,
        simp_all add: TwosComplement_tcN)

lemma C__convertInteger_sign_ext_neg:
  "\<lbrakk>i \<in> TwosComplement__rangeForLength len; 0 < len;
    len < C__typeBits newty;
    i \<notin> Rep_C__FiniteSetInt (C__rangeOfIntegerType newty);
    C__unsignedIntegerType_p newty \<or>
    C__plainCharsAreUnsigned \<and> newty = C__Type__char\<rbrakk>
    \<Longrightarrow> i < 0"
   apply (simp only: C__Range de_Morgan_conj not_less not_le)
   apply (clarsimp simp add: TwosComplement_tcN, rotate_tac 1)
   apply (frule_tac a="(2::int)" in power_strict_increasing, simp,
          cut_tac int_power_sub_1, simp_all)
done

lemma C__convertInteger_sign_ext_bound:
  "\<lbrakk>i \<in> TwosComplement__rangeForLength len; 0 < len;
    len < C__typeBits newty;
    i \<notin> Rep_C__FiniteSetInt (C__rangeOfIntegerType newty);
    C__unsignedIntegerType_p newty \<or>
    C__plainCharsAreUnsigned \<and> newty = C__Type__char\<rbrakk>
    \<Longrightarrow> 0 \<le> i + 2 ^ C__typeBits newty"
   apply (simp only: C__Range de_Morgan_conj not_less not_le)
   apply (clarsimp simp add: TwosComplement_tcN, rotate_tac 1)
   apply (drule_tac a="(2::int)" in power_strict_increasing, simp)
   apply (rule_tac y="i+(2 ^ (len - Suc 0))" in order_trans, auto)
done

lemma C__convertInteger_sign_ext_range:
  "\<lbrakk>i \<in> TwosComplement__rangeForLength len; 0 < len;
    len < C__typeBits newty;
    i \<notin> Rep_C__FiniteSetInt (C__rangeOfIntegerType newty);
    C__unsignedIntegerType_p newty \<or>
    C__plainCharsAreUnsigned \<and> newty = C__Type__char\<rbrakk>
    \<Longrightarrow>  i + 2 ^ C__typeBits newty
       \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType newty)"
   by (frule C__convertInteger_sign_ext_neg, simp_all,
       frule C__convertInteger_sign_ext_bound, 
       simp_all add: C__Range )

lemma C__convertInteger_sign_ext_THE_aux:
  "\<lbrakk>i \<in> TwosComplement__rangeForLength len; 0 < len;
    len < C__typeBits newty;
    i \<notin> Rep_C__FiniteSetInt (C__rangeOfIntegerType newty);
    C__unsignedIntegerType_p newty \<or>
    C__plainCharsAreUnsigned \<and> newty = C__Type__char\<rbrakk>
    \<Longrightarrow> (THE i'.
           i' \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType newty) \<and>
           (\<exists>k. i' = i + k * (C__maxOfIntegerType newty + 1)))
         = i + 2 ^ (C__typeBits newty)"
   apply (rule the1_equality,
          rule C__convertInteger_Obligation_the2, simp_all)
   apply (frule C__convertInteger_sign_ext_range, simp_all,
          subst C__maxOfIntegerType_unsigned, auto)
done

(* some of these lemmas could be simplified given the lemmas 
   that I have now added *)

lemma  C__convertInteger_sign_ext_len_neg_aux:
  "\<lbrakk>0 < len; i < 0; len < len2; C__typeBits ty2 = len2;
    C__integerType_p ty2; i \<in> TwosComplement__rangeForLength len;
    i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty2) \<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue (C__valueOfMathInt (i, ty2)) =
         C__OC__ok (List__extendLeft (TwosComplement__tcNumber (i, len), B1, len2))"
   apply (clarsimp simp add:  C__valueOfMathInt_def,
          rule the1I2, rule C__valueOfMathInt_Obligation_the, simp_all)
   apply (auto simp add: C__mathIntOfValue_def split: C__OC.split_asm)
   apply (cut_tac C__bitsOfIntegerValue_length2, 
          simp_all split: split_if_asm)
   apply (simp add: TwosComplement_extendLeft_tcInt_neg2)
done

lemma C__convertInteger_sign_ext_len_neg_aux0:
  "\<lbrakk>i \<in> TwosComplement__rangeForLength len; 0 < len;
    len < len2; C__typeBits ty2 = len2;
    i \<notin> Rep_C__FiniteSetInt (C__rangeOfIntegerType ty2);
    C__unsignedIntegerType_p ty2 \<or>
    C__plainCharsAreUnsigned \<and> ty2 = C__Type__char\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue
            (C__valueOfMathInt (i + 2 ^ len2, ty2)) =
           C__OC__ok
            (List__extendLeft
              (TwosComplement__tcNumber (i, len),
               TwosComplement__sign (TwosComplement__tcNumber (i, len)),
               len2))"
   apply (simp add:  C__valueOfMathInt_def,
          rule the1I2, rule C__valueOfMathInt_Obligation_the, simp_all)
   apply (frule C__convertInteger_sign_ext_range, simp_all, clarsimp)
   apply (simp add: C__mathIntOfValue_def split: C__OC.split_asm split_if_asm)
   apply (frule C__convertInteger_sign_ext_neg, simp_all,
          simp only: TwosComplement_sign_TC_neg, simp add: TwosComplement_TC)
   apply (rule TwosComplement__extendLeft_to_len_neg, simp_all add: C__bitsOfIntV C__Range)
   apply (subgoal_tac "0 \<le> i + 2 ^ len", 
          simp add: TwosComplementInt C__bitsOfIntV)
   apply (rule_tac len=len2 in Bits__toNat_hd_1, simp_all add: C__bitsOfIntV)
   apply (simp add: zle_int [symmetric] power2_nat)
   apply (cut_tac x=len2 in power_sub_1_eq_int, simp_all add: algebra_simps)
   apply (erule order_trans, simp)
   apply (clarsimp simp add: TwosComplement_tcN  power_sub_1_eq_int)
done 

lemma C__convertInteger_sign_ext_len_char:
  "\<lbrakk>C__plainCharsAreSigned; 8 < newlen;
     C__convertInteger (C__Value__char (Abs_Bits__Byte y), newty) =
     C__OC__ok newval;
     length y = 8; 
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, TwosComplement__sign y, newlen))"
   apply (cut_tac bs=y in TwosComplement_surjective, auto,
          simp add: C__convertInteger_def C__Words split: split_if_asm)
   apply (case_tac "0 \<le> i",
          simp_all add: not_le TwosComplement_sign_TC_pos2
                               TwosComplement_sign_TC_neg
                          C__convertInteger_sign_ext_len_pos_aux [symmetric]
                          C__convertInteger_sign_ext_len_neg_aux [symmetric])
   apply (clarsimp simp add: C__convertInteger_sign_ext_THE_aux
                             C__convertInteger_sign_ext_len_neg_aux0)
done



lemma C__convertInteger_sign_ext_len_schar:
  "\<lbrakk> C__signedIntegerType_p C__Type__schar; 8 < newlen;
     C__convertInteger (C__Value__schar (Abs_Bits__Byte y), newty) =
     C__OC__ok newval;
     length y = 8; 
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, TwosComplement__sign y, newlen))"
   apply (cut_tac bs=y in TwosComplement_surjective, auto,
          simp add: C__convertInteger_def C__Words split: split_if_asm)
   apply (case_tac "0 \<le> i",
          simp_all add: not_le TwosComplement_sign_TC_pos2
                               TwosComplement_sign_TC_neg
                          C__convertInteger_sign_ext_len_pos_aux [symmetric]
                          C__convertInteger_sign_ext_len_neg_aux [symmetric])
   apply (clarsimp simp add: C__convertInteger_sign_ext_THE_aux
                             C__convertInteger_sign_ext_len_neg_aux0) 
done

lemma C__convertInteger_sign_ext_len_sint:
   "\<lbrakk>C__signedIntegerType_p C__Type__sint; 
     C__int_bits < C__typeBits newty;
     C__convertInteger (C__Value__sint (Abs_C__IntWord y), newty) =
       C__OC__ok newval;
     length y = C__int_bits;
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, TwosComplement__sign y, newlen))"
   apply (cut_tac bs=y in TwosComplement_surjective, auto,
          simp add: C__convertInteger_def C__Words split: split_if_asm)
   apply (case_tac "0 \<le> i",
          simp_all add: not_le TwosComplement_sign_TC_pos2
                               TwosComplement_sign_TC_neg
                          C__convertInteger_sign_ext_len_pos_aux [symmetric]
                          C__convertInteger_sign_ext_len_neg_aux [symmetric])
   apply (clarsimp simp add: C__convertInteger_sign_ext_THE_aux
                             C__convertInteger_sign_ext_len_neg_aux0) 
done


lemma C__convertInteger_sign_ext_len_slong:
   "\<lbrakk>C__signedIntegerType_p C__Type__slong; 
     C__long_bits < C__typeBits newty;
     C__convertInteger (C__Value__slong (Abs_C__LongWord y), newty) =
       C__OC__ok newval;
     length y = C__long_bits;
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, TwosComplement__sign y, newlen))"
   apply (cut_tac bs=y in TwosComplement_surjective, auto,
          simp add: C__convertInteger_def C__Words split: split_if_asm)
   apply (case_tac "0 \<le> i",
          simp_all add: not_le TwosComplement_sign_TC_pos2
                               TwosComplement_sign_TC_neg
                          C__convertInteger_sign_ext_len_pos_aux [symmetric]
                          C__convertInteger_sign_ext_len_neg_aux [symmetric])
   apply (clarsimp simp add: C__convertInteger_sign_ext_THE_aux
                             C__convertInteger_sign_ext_len_neg_aux0) 
done



lemma C__convertInteger_sign_ext_len_sshort:
   "\<lbrakk>C__signedIntegerType_p C__Type__sshort; 
     C__short_bits < C__typeBits newty;
     C__convertInteger (C__Value__sshort (Abs_C__ShortWord y), newty) =
       C__OC__ok newval;
     length y = C__short_bits;
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, TwosComplement__sign y, newlen))"
   apply (cut_tac bs=y in TwosComplement_surjective, auto,
          simp add: C__convertInteger_def C__Words split: split_if_asm)
   apply (case_tac "0 \<le> i",
          simp_all add: not_le TwosComplement_sign_TC_pos2
                               TwosComplement_sign_TC_neg
                          C__convertInteger_sign_ext_len_pos_aux [symmetric]
                          C__convertInteger_sign_ext_len_neg_aux [symmetric])
   apply (clarsimp simp add: C__convertInteger_sign_ext_THE_aux
                             C__convertInteger_sign_ext_len_neg_aux0) 
done


lemma C__convertInteger_sign_ext_len_sllong:
   "\<lbrakk>C__signedIntegerType_p C__Type__sllong; 
     C__llong_bits < C__typeBits newty;
     C__convertInteger (C__Value__sllong (Abs_C__LongLongWord y), newty) =
       C__OC__ok newval;
     length y = C__llong_bits;
     C__typeBits newty = newlen; C__integerType_p newty\<rbrakk>
    \<Longrightarrow> C__bitsOfIntegerValue newval =
       C__OC__ok (List__extendLeft (y, TwosComplement__sign y, newlen))"
   apply (cut_tac bs=y in TwosComplement_surjective, auto,
          simp add: C__convertInteger_def C__Words split: split_if_asm)
   apply (case_tac "0 \<le> i",
          simp_all add: not_le TwosComplement_sign_TC_pos2
                               TwosComplement_sign_TC_neg
                          C__convertInteger_sign_ext_len_pos_aux [symmetric]
                          C__convertInteger_sign_ext_len_neg_aux [symmetric])
   apply (clarsimp simp add: C__convertInteger_sign_ext_THE_aux
                             C__convertInteger_sign_ext_len_neg_aux0) 
(******************************************************************************)
end-proof

proof Isa C__convertInteger_sign_extension
   apply (frule C__signed_cases, cases val, 
          auto simp add: TwosComplement__signExtend_def)
   (** 6 cases ***)
   apply (case_tac Bits__Byte,
          clarsimp simp add: C__Words C__convertInteger_sign_ext_len_char)
   apply (case_tac Bits__Byte,
          clarsimp simp add: C__Words C__convertInteger_sign_ext_len_schar)
   apply (case_tac C__IntWord,
          clarsimp simp add: C__Words C__convertInteger_sign_ext_len_sint)
   apply (case_tac C__LongLongWord,
          clarsimp simp add: C__Words C__convertInteger_sign_ext_len_sllong)
   apply (case_tac C__LongWord,
          clarsimp simp add: C__Words C__convertInteger_sign_ext_len_slong)
   apply (case_tac C__ShortWord,
          clarsimp simp add: C__Words C__convertInteger_sign_ext_len_sshort)
end-proof

proof Isa  C__convertInteger_truncation_Obligation_subtype
  by (simp add: C__bitsOfIntV)

(******************************************************************************)

lemma C__convertInteger_truncate_range [simp]:
   "\<lbrakk>C__integerType_p newty; C__typeBits newty < len;
     i \<in> Rep_C__FiniteSetInt (C__rangeOfIntegerType newty)\<rbrakk>
   \<Longrightarrow> i \<in> TwosComplement__rangeForLength len"
   apply (cases " C__unsignedIntegerType_p newty \<or>
                  C__plainCharsAreUnsigned \<and> newty = C__Type__char",
         simp_all add: C__Range, simp_all add: TwosComplement_tcN)
   apply (thin_tac "?P \<or> ?Q", clarsimp, rule conjI)
   apply (rule order_trans, simp_all)
   apply (drule less_le_suc, 
          drule_tac a="(2::int)" in power_increasing, simp,
          erule less_le_trans, simp)
   apply (thin_tac "\<not> ?P \<and> ?Q", clarsimp, rule conjI)
   apply (rule order_trans, simp_all)
   apply (rule less_trans, simp_all, 
          cut_tac ty=newty in C__typeBits_pos, 
          simp (no_asm_simp) add: power_strict_increasing)
done
(******************************************************************************)
 
end-proof

proof Isa  C__convertInteger_truncation
   apply (simp add: C__convertInteger_def 
                   split: C__OC.split_asm split_if_asm)
   apply (clarsimp simp add:  C__valueOfMathInt_def, rule the1I2, 
          rule C__valueOfMathInt_Obligation_the, simp_all,
          cut_tac x=x in C__mathIntOfValue_bits, simp, clarsimp)
   apply (frule_tac x=x and bs="bs" in C__mathIntOfValue_extend, simp_all,
          rotate_tac -1, erule ssubst, simp)
   apply (clarsimp simp add: C__convertInteger_THE_simp)
   apply (clarsimp simp add:  C__valueOfMathInt_def, rule the1I2, 
          rule C__valueOfMathInt_Obligation_the, simp_all,
          rule the1I2,
          rule C__convertInteger_Obligation_the2, simp_all, erule conjE)
   apply (simp add: C__Range,
          cut_tac x=x in C__mathIntOfValue_bits, simp_all, clarsimp,
          cut_tac C__bitsOfIntegerValue_length2 [symmetric], simp_all,
          cut_tac ty="C__typeOfValue x" in C__typeBits_pos,
          drule_tac s="length bs" in sym, simp)
   apply (clarsimp simp add: C__mathIntOfValue_def 
                      split: C__OC.split_asm split_if_asm)
   apply (simp add: zmod_int [symmetric] power2_int, rule toBits_mod2, simp_all)
   apply (rule  TwosComplement_mod2, simp_all)
end-proof

proof Isa C__convertInteger_no_change_Obligation_subtype
   by (cases val, auto simp add:  C__IntTypes split: split_if_asm)
end-proof

proof Isa C__convertInteger_no_change
   apply (frule C__convertInteger_type, simp,
          simp add:  C__convertInteger_def 
             split: C__OC.split_asm split_if_asm)
   apply (drule_tac t="newval" in sym, rotate_tac -1, erule ssubst,
          clarsimp simp add:  C__valueOfMathInt_def, rule the1I2, 
          rule C__valueOfMathInt_Obligation_the, simp_all, clarify)
   apply (rule C__mathIntOfValue_inject_bits, simp_all)
   apply (clarsimp simp add: C__convertInteger_THE_simp)
   apply (drule_tac t="newval" in sym, rotate_tac -1, erule ssubst,
          clarsimp simp add:  C__valueOfMathInt_def, rule the1I2, 
          rule C__valueOfMathInt_Obligation_the, 
          simp_all, simp add: C__Range, clarsimp)
   apply (frule C__mathIntOfValue_type,
          frule C__mathIntOfValue_int_p,
          case_tac "C__unsignedIntegerType_p (C__typeOfValue val) \<or>
             C__plainCharsAreUnsigned \<and> C__typeOfValue val = C__Type__char",
          simp_all add: C__Range not_less not_le,
          clarsimp simp add: power_sub_1_eq_int,
          simp add: power_sub_1_eq_int [symmetric])
   apply (cut_tac x=x in C__mathIntOfValue_bits, simp_all, clarsimp,
          cut_tac C__bitsOfIntegerValue_length2 [symmetric], simp_all,
          cut_tac ty="C__typeOfValue x" in C__typeBits_pos,
          drule_tac s="length bs" in sym, simp)
   apply (clarsimp simp add: C__mathIntOfValue_def 
                      split: C__OC.split_asm split_if_asm)
   apply (cut_tac bs=bs and bits=bits and len="length bits"
          in TwosComplement_mod2,
          simp, simp, simp add: zmod_int [symmetric] power2_int, simp,
          erule_tac t=bs in ssubst, simp (no_asm))
end-proof

proof Isa C__promoteValue_Obligation_subtype
  by (simp add:  C__integerValue_p_def C__promoteType_def C__IntTypes)
end-proof

proof Isa C__arithConvertValues_Obligation_subtype
  by (simp add: C__arithmeticValue_p_def)

(******************************************************************************)
(*** Move this up ***)

lemma C__correspondingUnsignedOf_int_p [simp]:
  "\<lbrakk>C__signedIntegerType_p ty\<rbrakk>
    \<Longrightarrow> C__integerType_p (C__correspondingUnsignedOf ty)"
 by (cases ty, simp_all add: C__IntTypes )

lemma C__correspondingSignedOf_int_p [simp]:
  "\<lbrakk>C__unsignedIntegerType_p ty\<rbrakk>
    \<Longrightarrow> C__integerType_p (C__correspondingSignedOf ty)"
 apply (cases ty, simp_all add: C__IntTypes )
(******************************************************************************)
end-proof

proof Isa C__arithConvertValues_Obligation_subtype0
   apply (simp add: C__arithmeticValue_p_def C__arithmeticType_p_def)
   apply (drule C__promoteType_int,
          frule C__promoteType_int, drule C__promoteType_not_char)
   apply (auto simp add: C__arithConvertTypes_def Let_def)
   apply (erule rev_mp, subst C__integerType_p_def, auto)
end-proof

proof Isa  C__arithConvertValues_Obligation_subtype1
  by (drule sym, simp add: C__arithConvertValues_Obligation_subtype0)
end-proof

proof Isa C__convertForAssignment_Obligation_subtype
  by (simp add: C__arithmeticType_p_def)

(******************************************************************************)

lemma C__arithConvertValues_sint_sint [simp]:
  "C__arithConvertValues (C__Value__sint i1, C__Value__sint i2)
   = C__OC__ok (C__Value__sint i1, C__Value__sint i2)"
 by (simp add: C__arithConvertValues_def C__arithmeticValue_p_def 
               C__arithConvertTypes_def  C__IntTypes)

 
lemma C__arithConvertValues_uchar_sint [simp]:
  "\<lbrakk>i1 < 2 ^ 8\<rbrakk> \<Longrightarrow> 
   C__arithConvertValues (C__Value__uchar (Bits__byte i1), C__Value__sint i2)
   = C__OC__ok 
    (C__Value__sint (Abs_C__IntWord (TwosComplement__tcNumber (int i1, C__int_bits))),
     C__Value__sint i2)"
 by (simp add: C__arithConvertValues_def C__arithmeticValue_p_def 
               C__arithConvertTypes_def  C__IntTypes)

(******************************************************************************)

lemma  C__integerConstantCandidateTypes_int_p:
  "\<lbrakk>i < length (C__integerConstantCandidateTypes c); 
    ty = C__integerConstantCandidateTypes c ! i \<rbrakk>
    \<Longrightarrow> C__integerType_p ty"
  apply (cut_tac C__checkIntegerConstant_Obligation_subtype, simp_all)

(******************************************************************************)
end-proof

proof Isa C__evaluateIntegerConstant_Obligation_subtype
  apply (simp add: C__checkIntegerConstant_def Let_def split: split_if_asm)
  apply (clarify, rule the1I2, 
         cut_tac C__checkIntegerConstant_Obligation_the, simp_all,
         rule_tac x=i in exI, simp, clarsimp)
  apply (rule C__integerConstantCandidateTypes_int_p, simp_all)
end-proof

proof Isa C__operator_MINUS_Obligation_subtype
   by (simp add: C__IntTypes)
end-proof

proof Isa C__operator_MINUS_Obligation_subtype0
  by (auto simp add: C__IntTypes)
end-proof

proof Isa  C__operator_MINUS_Obligation_subtype1
  apply (frule  C__operator_MINUS_Obligation_subtype, simp_all)
  apply (frule C__rangeOfIntegerType_Obligation_subtype)
  apply (auto simp add: C__IntTypes C__rangeOfIntegerType_def)
  apply (simp add: Abs_C__FiniteSetInt_inverse C__FiniteSetInt_def, 
         simp add: mem_def C__Consts)+
end-proof

proof Isa C__operator_MINUS_Obligation_subtype2
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_MINUS_Obligation_subtype3
 (** In the def below add parentheses before the let **)
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa  C__operator_NOT_Obligation_subtype
  by (auto simp add: C___bitsOfIntegerValue_int_p C__bitsOfIntegerValue_length2)
end-proof

proof Isa C__operator_MUL_Obligation_subtype
  by (auto simp add: C__IntTypes)
end-proof


proof Isa C__operator_MUL_Obligation_subtype0
  by (auto simp add: C__IntTypes)
end-proof

proof Isa C__operator_MUL_Obligation_subtype1
  apply (frule  C__operator_MUL_Obligation_subtype, simp_all)
  apply (frule C__rangeOfIntegerType_Obligation_subtype)
  apply (auto simp add: C__IntTypes C__rangeOfIntegerType_def C__Consts)
  apply (simp add: Abs_C__FiniteSetInt_inverse C__FiniteSetInt_def, 
         simp add: mem_def)+ 
end-proof

proof Isa C__operator_MUL_Obligation_subtype2
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_MUL_Obligation_subtype3
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_DIV_Obligation_subtype0
  by (simp add: C__IntTypes)
end-proof

proof Isa C__operator_DIV_Obligation_subtype1
  by (auto simp add: C__IntTypes)
end-proof

proof Isa C__operator_DIV_Obligation_subtype2
  apply (frule  C__operator_DIV_Obligation_subtype0, simp_all)
  apply (frule C__rangeOfIntegerType_Obligation_subtype)
  apply (auto simp add: C__IntTypes C__rangeOfIntegerType_def C__Consts)
  apply (simp add: Abs_C__FiniteSetInt_inverse C__FiniteSetInt_def, 
         simp add: mem_def)+
end-proof

proof Isa C__operator_DIV_Obligation_subtype3
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_DIV_Obligation_subtype4
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_REM_Obligation_subtype0
  by (simp add: C__IntTypes)
end-proof

proof Isa C__operator_REM_Obligation_subtype1
  by (auto simp add: C__IntTypes)
end-proof

proof Isa C__operator_REM_Obligation_subtype2
  apply (frule  C__operator_REM_Obligation_subtype0, simp_all)
  apply (frule C__rangeOfIntegerType_Obligation_subtype)
  apply (auto simp add: C__IntTypes C__rangeOfIntegerType_def C__Consts)
  apply (simp add: Abs_C__FiniteSetInt_inverse C__FiniteSetInt_def, 
         simp add: mem_def)+
end-proof

proof Isa C__operator_REM_Obligation_subtype3
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_REM_Obligation_subtype4
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof


proof Isa C__operator_ADD_Obligation_subtype
  by (simp add: C__IntTypes)
end-proof

proof Isa C__operator_ADD_Obligation_subtype0
  by (auto simp add: C__IntTypes)
end-proof

proof Isa C__operator_ADD_Obligation_subtype1
  apply (frule  C__operator_ADD_Obligation_subtype, simp_all)
  apply (frule C__rangeOfIntegerType_Obligation_subtype)
  apply (auto simp add: C__IntTypes C__rangeOfIntegerType_def C__Consts)
  apply (simp add: Abs_C__FiniteSetInt_inverse C__FiniteSetInt_def, 
         simp add: mem_def)+
end-proof

proof Isa C__operator_ADD_Obligation_subtype2
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_ADD_Obligation_subtype3
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_SUB_Obligation_subtype
  by (simp add: C__IntTypes)
end-proof

proof Isa C__operator_SUB_Obligation_subtype0
  by (auto simp add: C__IntTypes)
end-proof

proof Isa C__operator_SUB_Obligation_subtype1
  apply (frule  C__operator_SUB_Obligation_subtype, simp_all)
  apply (frule C__rangeOfIntegerType_Obligation_subtype)
  apply (auto simp add: C__IntTypes C__rangeOfIntegerType_def C__Consts)
  apply (simp add: Abs_C__FiniteSetInt_inverse C__FiniteSetInt_def, 
         simp add: mem_def)+
end-proof

proof Isa C__operator_SUB_Obligation_subtype2
  
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_SUB_Obligation_subtype3  
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof


proof Isa C__operator_SHL_Obligation_subtype1
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_SHL_Obligation_subtype3
  by (simp add: C__IntTypes)
end-proof

proof Isa C__operator_SHL_Obligation_subtype4
  by (auto simp add: C__IntTypes)
end-proof

proof Isa C__operator_SHL_Obligation_subtype5
  apply (frule  C__operator_SHL_Obligation_subtype3, simp_all)
  apply (frule C__rangeOfIntegerType_Obligation_subtype)
  apply (auto simp add: C__IntTypes C__rangeOfIntegerType_def  C__Consts)
  apply (simp add: Abs_C__FiniteSetInt_inverse C__FiniteSetInt_def, 
         simp add: mem_def)+
end-proof

proof Isa C__operator_SHL_Obligation_subtype6
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_SHL_Obligation_subtype7
  by (auto simp add: C__mathIntOfValue_int_p)
end-proof

proof Isa C__operator_SHL_Obligation_subtype
  by (simp add: C___bitsOfIntegerValue_is_pos)
end-proof

proof Isa C__operator_SHL_Obligation_subtype0
  apply (subst C__bitsOfIntegerValue_length2, simp_all)
  apply (simp add: C__operator_SHL_def Let_def not_le not_less
            split: C__OC.split_asm split_if_asm)
  apply (simp add: C__mathIntOfValue_def split: split_if_asm)
  apply (simp add: C__mathIntOfValue_def split: split_if_asm)
  defer defer
  (* need more lemmas **)
end-proof

proof Isa C__operator_SHL
  sorry
end-proof

proof Isa C__operator_SHR_Obligation_subtype1
  by (auto simp add: C__mathIntOfValue_int_p) 
end-proof


proof Isa C__operator_SHR_Obligation_subtype4
  apply (frule C__mathIntOfValue_type)
  apply (auto simp add: C__mathIntOfValue_int_p not_less not_le)
  apply (rotate_tac 4, erule rev_mp,
         subst C__rangeOfIntegerType_unsigned, auto,
         subst C__rangeOfIntegerType_unsigned, auto)
  apply (rule divT_pos_pos_le, simp_all)
  apply (simp add: divT_pos, rule le_less_trans, simp_all,
         subst nat_le_eq_zle [symmetric], simp, simp add: nat_div_distrib)
  apply (rotate_tac 4, erule rev_mp,
         subst C__rangeOfIntegerType_signed2, auto,
         subst C__rangeOfIntegerType_signed2, auto)
  apply (cut_tac a=x1 and b="2 ^ nat x2" in divT_pos_pos_le, simp_all)
  apply (simp add: divT_pos, rule le_less_trans, simp_all,
         subst nat_le_eq_zle [symmetric], simp, simp add: nat_div_distrib)
end-proof

proof Isa C__operator_SHR_Obligation_subtype
  by (erule C__operator_SHL_Obligation_subtype, auto) 
end-proof

proof Isa C__operator_SHR_Obligation_subtype0
  by (erule C__operator_SHL_Obligation_subtype0, auto) 
end-proof

proof Isa C__operator_SHR
  sorry
end-proof

proof Isa  C__operator_AND_Obligation_subtype
  apply (auto simp add: C__arithConvertValues_def C__bitsOfIntV Let_def
                 split: split_if_asm C__OC.split_asm)
  apply (frule C__arithConvertValues_Obligation_subtype0, rotate_tac 3, simp)
  apply (frule_tac val=val1 in C__convertInteger_type, simp)
  apply (frule_tac val=val2 in C__convertInteger_type, simp)
  apply simp
end-proof

proof Isa  C__operator_AND_Obligation_subtype0
 by (frule C__operator_AND_Obligation_subtype, auto simp add: C__bitsOfIntV)
end-proof

proof Isa  C__operator_XOR_Obligation_subtype
  by (erule C__operator_AND_Obligation_subtype, auto)
end-proof

proof Isa  C__operator_XOR_Obligation_subtype0
 by (frule C__operator_AND_Obligation_subtype, auto simp add: C__bitsOfIntV)
end-proof

proof Isa  C__operator_IOR_Obligation_subtype
  by (erule C__operator_AND_Obligation_subtype, auto)
end-proof

proof Isa  C__operator_IOR_Obligation_subtype0
 by (frule C__operator_AND_Obligation_subtype, auto simp add: C__bitsOfIntV)
end-proof


proof Isa C__expressionValues ()
  by  (pat_completeness, auto)
termination
 by (relation "measure (\<lambda>(state, ress). size ress)", auto)
end-proof

% ------------------------------------------------------------
proof Isa  C__evaluate_Obligation_exhaustive
 (** the next epression needs about 100 parentheses !! *)
  by (case_tac bop, auto)
end-proof

proof Isa evaluate ()
  by auto
termination
  by (relation "measure (\<lambda>(store,expr). size expr)", auto)

(** prevent the function from being unfolded automatically **)
declare C__evaluate.simps [simp del]

(** provide a gazillion explicit simplifications instead **)

lemma C__evaluate_simp1 [simp]: 
  "\<lbrakk>Map__finite_p (Rep_Map__FiniteMap (C__State__functions state));
    C__designatorOfObject(state, var) =  C__OC__ok x\<rbrakk>
   \<Longrightarrow> 
    C__evaluate(state, C__Expression__ident var)
    = C__OC__ok (C__ExpressionResult__object x)"
 apply (simp add:  C__evaluate.simps)
end-proof


% ----------------------------------

proof Isa  C__evaluate_Obligation_subtype
  (** remove Rep_C__FMapIdVal before members **)
  sorry
end-proof

proof Isa C__evaluate_Obligation_exhaustive0
  (** remove C__FMapIdVal type of members **)
  by (cases x0_3, auto)
end-proof


proof Isa C__evaluate_Obligation_exhaustive1
  sorry
end-proof


proof Isa  expression_evaluation
  apply (case_tac "C__evaluate (state, expr)", simp_all)
  (*** This has become a lot more complex - need simp lemmas *****
  apply (fold Map__finite_p_def)
  apply (induct expr, auto simp add:  C__checkExpression_def)
  apply (case_tac C__BinaryOp, auto, case_tac "y=ya", auto)
  apply (simp add: C__readStorage_def C__storageMatchesSymbolTable_p_def, auto)
  ********************************************************************)
  sorry
end-proof 


proof Isa evaluateAll ()
  by (pat_completeness, auto)
termination
  by (relation "measure (\<lambda>(state,exprs). size exprs)", auto)
end-proof 


proof Isa expandTypeName ()
  by (pat_completeness, auto)
termination
  by (relation "measure (\<lambda>(state,tyn). size tyn)", auto)
end-proof 

% ------------------------------------------------------------
% ------------------------------------------------------------


proof Isa C__zeroOfType_Obligation_subtype2
  by (cases ty, auto simp add: C__scalarType_p_def C__IntTypes)
end-proof


proof Isa zeroOfType ()
 (** Add  (map (\<lambda> (x,y). (Abs_C__Identifier x,y)) before List__toAssocList
     Drop Abs_C__FMapIdVal before Rep_Map__FiniteMap
  -- more problems ... see saved file for solution --
  *)
  by (pat_completeness, auto)
termination
  apply (relation "measure  (\<lambda>x. case x of 
                   Inl (state, tys) \<Rightarrow> list_size size tys
                 | Inr (state, ty)  \<Rightarrow> size ty
                 )", auto)
  sorry

(** prevent the function from being unfolded automatically **)
declare C__zeroOfType.simps   [simp del]
declare C__zerosOfTypes.simps [simp del]
declare C__expandTypeName.simps     [simp del] (** move this **)
(** provide a gazillion explicit simplifications instead **)

lemma C__zeroOfType_simp1 [simp]: 
  "\<lbrakk>Map__finite_p (Rep_Map__FiniteMap (C__State__functions state));
    \<not> (C__invariants_p state) \<rbrakk>
   \<Longrightarrow> 
    C__zeroOfType(state, ty)
    = C__OC__error"
 apply (simp add:  C__zeroOfType.simps)
end-proof

proof Isa C__zeroOfType_Obligation_subtype1
  (*** difficult to fix assumption - for now comment it out **)
  sorry
end-proof

proof Isa C__zeroOfType_Obligation_subtype0
  (*** difficult to fix assumption - for now comment it out **)
  sorry
end-proof

proof Isa C__execObjectDeclaration_Obligation_subtype3
  by (simp add: last_conv_nth null_def)
end-proof

proof Isa C__object_declaration_execution
  (** many cases **)
  sorry
end-proof

proof Isa execMemberDeclarations ()
  by (pat_completeness, auto)
termination
  by (relation "measure (\<lambda>(state,decls). size decls)", auto)
end-proof

proof Isa C__structure_specifier_execution
  (** Above add Abs_C__FMapIdTypedM before Map__update *)
  sorry
end-proof

proof Isa C__type_definition_execution
  (** Above add Abs_C__FMapIdTypedM before Map__update *)
  sorry
end-proof

proof Isa C__declaration_execution
 by (cases decl, 
     simp_all add: C__object_declaration_execution
                   C__structure_specifier_execution
                   C__type_definition_execution)
end-proof

proof Isa C__undefinePointersInValue_Obligation_subtype0
  by (simp add: C__zeroOfType_Obligation_subtype0)
end-proof

proof Isa undefinePointersInValue ()
(** Above remove Rep_C__FMapIdVal before members
  -- more problems ... see saved file for solution -- **)
apply (pat_completeness, auto)
sorry
termination
  apply (relation "measure  (\<lambda>x. case x of 
                   Inl (vals, f, b_p) \<Rightarrow> list_size (\<lambda>val. 1) vals 
                 | Inr (val, f, b_p)  \<Rightarrow> 1
                 )",
         auto)
  (* we have a nested recursion with arrows here ... **)
  sorry
end-proof

proof Isa  C__undefinePointersInValue_Obligation_subtype1
  (*** difficult to fix assumption - for now comment it out **)
  sorry
end-proof

proof Isa  C__undefinePointersInValue_Obligation_subtype0
  (*** difficult to fix assumption - for now comment it out **)
  sorry
end-proof

proof Isa C__undefinePointersInNamedStorage_Obligation_subtype0
  (*** difficult to fix assumption - for now comment it out **)
  by (rule C__undefinePointersInValue_Obligation_subtype0)
end-proof

proof Isa C__undefinePointersInNamedStorage_Obligation_subtype1
  (*** difficult to fix assumption - for now comment it out **)
  (*** fix def below as in saved file ... this is probably also the solution 
       for all the past lemmas ***)
  by (rule C__undefinePointersInValue_Obligation_subtype1)
end-proof

proof Isa assignArgumentsToParameters ()
  by (pat_completeness, auto)
termination
  by (relation "measure (\<lambda>(state, tparams, args). size tparams)", auto)
end-proof

proof Isa execStatement_Obligation_subtype3
  by (simp add: null_def)
end-proof

proof Isa execStatement_Obligation_exhaustive
 (** Definition below misses many parentheses -- use stored version **)
  by (cases stmt, auto simp add: Let_def split: option.split)
end-proof


proof Isa execStatement ()
  by (pat_completeness, safe)
termination
  (* need some form of lexicographic order in mutual recursion
     also, for Isabelle I must add auxiliary functions that are pared 
     instead of curried *)
  apply (relation "measure  (\<lambda>x. case x of 
                   Inl y \<Rightarrow> (case y of 
                                  Inl (state, item)  \<Rightarrow> size item
                                | Inr (state, items) \<Rightarrow> list_size size items)
                 | Inr z \<Rightarrow> (case z of 
                                  Inl (state, name, args) \<Rightarrow> size  
                                      (Rep_Map__FiniteMap (C__State__functions state) name)
                                | Inr (state,stmt) \<Rightarrow> size stmt)
                 )", auto)
  sorry
end-proof

proof Isa C__execStatement_Obligation_subtype8
  sorry
end-proof

proof Isa execStatement_Obligation_subtype6
  by (simp add: C__readTopObject_Obligation_subtype)
end-proof

proof Isa C__execStatement_Obligation_subtype5
  by (drule C__execStatement_Obligation_subtype8, auto)
end-proof


proof Isa statement_execution
  (** There is an old proof in _SAVED/CK_C that may provide some hints **)
 sorry
end-proof

proof Isa C__block_items_execution
  sorry
end-proof

proof Isa C__block_item_execution
  sorry
end-proof

proof Isa C__function_call
   (*** replace (Rep_C__Identifier name) by name **)
  sorry
end-proof

proof Isa  C__execParameterList ()
  by  (pat_completeness, auto)
termination
  by (relation "measure (\<lambda>(state, plist). size plist)", auto)
end-proof

proof Isa  C__function_definition_execution
 (** Definition above has problems -- use stored version **)
  sorry
end-proof

proof Isa C__external_declaration_execution
  sorry
end-proof

proof Isa C__execTranslationUnit ()
  by (pat_completeness, auto)
termination
  by (relation "measure (\<lambda>(state, tunit). size tunit)", auto)
end-proof

proof Isa C__translation_unit_execution
  sorry
end-proof

proof Isa emptyState_Obligation_subtype
  (* drop the typing of xz and Abs_C__Identifier -- 
     also in the def below - record field names are wrong too
     see stored def  **)
  by auto
end-proof
 
proof Isa C__initial_state_invariants
  sorry
end-proof



% ------------------------------------------------------------

% ------------------------------------------------------------------------------
% ---------- Part 6: verbatim Isabelle lemmas             ----------------------
% ----------         that cannot be expressed in SpecWare ----------------------
% ------------------------------------------------------------------------------

proof Isa -verbatim
(*****************************************************************************)

declare C__callFunction.simps [simp del]
declare C__execBlockItems.simps [simp del]
declare C__execBlockItem.simps [simp del]

declare C__execStatement.simps [simp del]
declare C__expressionValue.simps [simp del]
declare C__expressionValues.simps [simp del]

lemmas C_exec_simps =   C__execBlockItems.simps 
                        C__execBlockItem.simps 
                        C__execStatement.simps 
                        C__expressionValue.simps 
                        C__expressionValues.simps 
                        C__evaluate.simps 
       

(******************************************************************************)
end-proof


endspec
