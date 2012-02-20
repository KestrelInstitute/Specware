C qualifying spec

import CTargetParameters


%section (* Introduction *)

(* We formalize types and ops that may be useful to target C from Metaslang.
This spec captures C concepts (e.g. C types) that (1) can be targeted by
refinements and (2) can be mapped to corresponding C code by a suitable code
generator. This spec can be viewed as a shallow embedding of (a subset of) C
into Metaslang.

Our formalization is based on the ANSI C99 standard, ISO/IEC 9899, "Programming
languages - C", Second edition (1999-12-01). Note that the Second edition of
Brian Kernighan and Dennis Ritchie's "The C Programming Language", published in
1988, refers to an earlier version of the standard.

In the comments in this spec, we reference the ISO standard as "[ISO]", possibly
including (dotted) (sub)section numbers (e.g. "[ISO 6.5.9]") and paragraph
numbers separated by "/" (e.g. "[ISO 6.5.9/2]"). We also reference the ISO 9899
Corrigenda 1, 2, and 3 as "[ISO C1]", "[ISO C2]", and "[ISO C3]", possibly
including the numeric indices of the corrections separated by "." (e.g. "[ISO
C2.32]"). We use "," to indicate multiple sub-references (e.g. "[ISO 6.5.4/3,
5.2.1]") and we use "-" to indicate ranges of contiguous sub-references (e.g.
"[ISO 6.5.4-6.5.6]" is the same as "[ISO 6.5.4, 6.5.5, 6.5.6]").

The comments in this spec are structured into sections and subsections,
following a literate programming style. Even though there are currently no tools
to process these structured comments (e.g. to produce PDF documents), the
structuring is valuable per se. The following formats are used for the
structured comments:

- each (sub)section starts with "%section", "%subsection", "%subsubsection",
etc. (recall that "%" starts a line comment) in column 0, followed by a title
between the Metaslang symbols for block comments (which we do not repeat here
otherwise we would be closing this comment!);

- each paragraph of comments is a single block comment in Metaslang, with each
line starting at column 0 and the opening and closing symbols of the block
comments in line with the text (i.e. not in separate lines);

- no comment line exceeds 80 columns;

- each new (sub)section is preceded by exactly two blank lines.

Formal Metaslang text (i.e. not comments) always starts at column 0 and never
exceeds 80 columns. This and the previous comment formats should be followed by
anybody editing this file, to ensure uniformity, ease of text search, no line
wrapping if the spec is printed, and support for several side-by-side editors
without line wrapping. *)


%section (* Parameterization *)

(* Some aspects of the C language depend on the environment [ISO 5], i.e. on the
implementation. Prime examples are the sizes of the integer types. These aspects
are "parameters" of the C language.

The parameters needed by our formalization are all defined by our formalization,
either implicitly or explicitly. The implicitly defined parameters are described
in the comments in this spec. The explicitly defined parameters are collected in
spec CTargetParameters. The definitions in that spec can be easily changed to
accommodate different target C implementations. Constraints over those
parameters are expressed as theorems in this spec. If the definitions of the
parameters in spec CTargetParameters are changed, it must be ensured that such
theorems still hold.

The explicitly defined parameters and their constraining theorems are explained
in this spec. We keep spec CTargetParameters as simple and short as possible, to
ease the management of different versions of the explicitly defined parameters.

An alternative approach is to not define the explicitly defined parameters but
just declare them, along with axioms that constrain their possible definitions.
Those parameters could be then instantiated via a spec substitution, whose proof
obligations would ensure that the definitions of the parameters satisfy the
constraining axioms. This approach may be cleaner in Specware itself, but may
not work well with the Isabelle translator. In contrast, the approach described
above that we are following works well with the Isabelle translator. *)


%section (* Types *)

(* We introduce Metaslang types that correspond to C types. If a Metaslang spec
is refined to use the types defined here, the code generator can map the types
used by the refined spec to the corresponding C types. *)


%subsection (* The unsigned char type *)

(* The number of bits that comprise a byte [ISO 3.6] is expressed by CHAR_BIT
[ISO 5.2.4.2.1/1], which must be at least 8. (Note that the notion of byte in C
may not coincide, although it often does, with the notion of byte in the
Specware library, which defines a byte to always consist of 8 bits. However,
given our definition of CHAR_BIT as 8, the two notions coincide.) *)

% In spec CTargetParameters:
%
% op CHAR_BIT : Nat

theorem min_CHAR_BIT is CHAR_BIT >= 8

(* [ISO 5.2.4.2.1/2] constrains UCHAR_MAX [ISO 5.2.4.2.1/1] to be
2^CHAR_BIT-1. *)

op UCHAR_MAX : Nat = 2 ** CHAR_BIT - 1

(* [ISO 6.2.6.1/3] constrains unsigned char objects to be represented using a
pure binary notation, i.e. to range from 0 to 2^CHAR_BIT-1. Thus, unsigned char
objects are always bytes in C, and every object (of any type) consists of one or
more bytes [ISO 6.2.6.1/4]. This leads to the following type definition. We
"interpose" the uchar constructor between the list of CHAR_BIT bits and the
corresponding value of type Uchar in order to keep all the C types separate
(i.e. with no values in common) -- we use such constructors for the other C
types below. This may ease refinements, but experience will tell. *)

type Uchar = | uchar (Bits | ofLength? CHAR_BIT)

(* The bits that constitute an unsigned char can be interpreted in big endian or
little endian, to denote a "mathematical integer". Since a byte is always
addressed as a unit, the exact choice is unimportant. We choose big endian (as
implied by the use of toNat). *)

op mathIntOfUchar (uchar bs : Uchar) : Nat = toNat bs

op rangeOfUchar : FiniteSet Int = fn i:Int -> 0 <= i && i <= UCHAR_MAX

theorem uchar_range is fa(x:Uchar) mathIntOfUchar x in? rangeOfUchar

op ucharOfMathInt (i:Int | i in? rangeOfUchar) : Uchar =
  the(x:Uchar) mathIntOfUchar x = i


%subsection (* The signed char type *)

(* The sizeof operator [ISO 6.5.3.4], which returns the size in bytes of its
operand [ISO 6.5.3.4/2], must return 1 when applied to a char, unsigned char, or
signed char object. This implies that signed char objects consist of 1 byte,
like unsigned char objects. *)

type Schar = | schar (Bits | ofLength? CHAR_BIT)

(* [ISO 6.2.6.2/2] says that a signed char object must include a sign bit and
that the other bits are divided among value and padding bits. We assume that
there are no padding bits and that signed chars are represented as two's
complement (vs. one's complement or sign & magnitude) -- these are two examples
of parameters of the C language that are implicitly defined by our
formalization. As with unsigned chars, we choose a big endian interpretation for
signed chars. *)

op mathIntOfSchar (schar bs : Schar) : Int = toInt bs

op SCHAR_MIN : Int = - (2 ** (CHAR_BIT - 1))
op SCHAR_MAX : Nat = 2 ** (CHAR_BIT - 1) - 1

op rangeOfSchar : FiniteSet Int = fn i:Int -> SCHAR_MIN <= i && i <= SCHAR_MAX

theorem schar_range is fa(x:Schar) mathIntOfSchar x in? rangeOfSchar

op scharOfMathInt (i:Int | i in? rangeOfSchar) : Schar =
  the(x:Schar) mathIntOfSchar x = i

(* The constraint that SCHAR_MAX is at least +127 [ISO 5.2.4.2.1/1] is
satisfied. *)

theorem min_SCHAR_MAX is SCHAR_MAX >= 127


%subsection (* The plain char type *)

(* Plain char objects have the same range and representation as either signed
char objects or unsigned char objects [ISO 6.2.5/15]. Either way, plain chars
consist of CHAR_BIT bits. However, their range of value differs. *)

% In spec CTargetParameters:
%
% op plainCharsAreSigned : Bool

op plainCharsAreUnsigned : Bool = ~ plainCharsAreSigned

type Char = | char (Bits | ofLength? CHAR_BIT)

op mathIntOfChar (char bs : Char) : Int =
  if plainCharsAreSigned then toInt bs else toNat bs

op CHAR_MIN : Int = if plainCharsAreSigned then SCHAR_MIN else 0
op CHAR_MAX : Nat = if plainCharsAreSigned then SCHAR_MAX else UCHAR_MAX

op rangeOfChar : FiniteSet Int = fn i:Int -> CHAR_MIN <= i && i <= CHAR_MAX

theorem char_range is fa(x:Char) mathIntOfChar x in? rangeOfChar

op charOfMathInt (i:Int | i in? rangeOfChar) : Char =
  the(x:Char) mathIntOfChar x = i


%subsection (* The other integer types *)

(* The representation of an unsigned integer type other than unsigned char, must
consist of N value bits plus 0 or more padding bits, yielding a range of values
between 0 and 2^N-1 [ISO 6.2.6.2/1]. This constrains the U..._MAX value of each
unsigned integer type to be 2^N-1. We assume that no padding bits are used, so
that the representation consists of exactly N (value) bits. Since every object
(including integers) has a size in bytes [ISO 6.5.3.4/2, 6.2.6.1/4], N must be a
multiple of CHAR_BIT.

The sizeof_... constants express the size, in bytes, of each unsigned integer
type other than unsigned char (which we have covered earlier). So, for each
unsigned integer type, the number of bits N is CHAR_BIT times the
sizeof_... constants. For convenience, we also define ..._bit constants that
express the size in bits of the types.

The minimum magnitude constraints on the U..._MAX values given in [ISO
5.2.4.2.1/1] correspond to the minimum magnitude constraints on the
sizeof_... constants expressed by the theorems below.

Unlike chars, the big or little endian interpretation of the bytes that
constitute a value of a larger integer types makes a difference in some C
programs. However, for now we plan to stick to a type-safe subset of C, where
endianness does not matter. *)

% In spec CTargetParameters:
%
% op sizeof_short : Nat
% op sizeof_int   : Nat
% op sizeof_long  : Nat
% op sizeof_llong : Nat

op short_bits : Nat = sizeof_short * CHAR_BIT
op   int_bits : Nat = sizeof_int   * CHAR_BIT
op  long_bits : Nat = sizeof_long  * CHAR_BIT
op llong_bits : Nat = sizeof_llong * CHAR_BIT

theorem min_sizeof_short is sizeof_short >= 2
theorem min_sizeof_int   is sizeof_int   >= 2
theorem min_sizeof_long  is sizeof_long  >= 4
theorem min_sizeof_llong is sizeof_llong >= 8

theorem min_short_bits is short_bits >= 16
theorem min_int_bits   is   int_bits >= 16
theorem min_long_bits  is  long_bits >= 32
theorem min_llong_bits is llong_bits >= 64

op  USHRT_MAX : Nat = 2 ** short_bits - 1
op   UINT_MAX : Nat = 2 **   int_bits - 1
op  ULONG_MAX : Nat = 2 **  long_bits - 1
op ULLONG_MAX : Nat = 2 ** llong_bits - 1

theorem min_USHRT_MAX  is  USHRT_MAX  >= 2 ** 16 - 1
theorem min_UINT_MAX   is  UINT_MAX   >= 2 ** 16 - 1
theorem min_ULONG_MAX  is  ULONG_MAX  >= 2 ** 32 - 1
theorem min_ULLONG_MAX is  ULLONG_MAX >= 2 ** 64 - 1

type Ushort = | ushort (Bits | ofLength? short_bits)
type   Uint = | uint   (Bits | ofLength?   int_bits)
type  Ulong = | ulong  (Bits | ofLength?  long_bits)
type Ullong = | ullong (Bits | ofLength? llong_bits)

op mathIntOfUshort (ushort bs : Ushort) : Nat = toNat bs
op mathIntOfUint   (uint   bs : Uint)   : Nat = toNat bs
op mathIntOfUlong  (ulong  bs : Ulong)  : Nat = toNat bs
op mathIntOfUllong (ullong bs : Ullong) : Nat = toNat bs

op rangeOfUshort : FiniteSet Int = fn i:Int -> 0 <= i && i <= USHRT_MAX
op rangeOfUint   : FiniteSet Int = fn i:Int -> 0 <= i && i <= UINT_MAX
op rangeOfUlong  : FiniteSet Int = fn i:Int -> 0 <= i && i <= ULONG_MAX
op rangeOfUllong : FiniteSet Int = fn i:Int -> 0 <= i && i <= ULLONG_MAX

theorem ushort_range is fa(x:Ushort) mathIntOfUshort x in? rangeOfUshort
theorem   uint_range is fa(x:Uint)   mathIntOfUint   x in? rangeOfUint
theorem  ulong_range is fa(x:Ulong)  mathIntOfUlong  x in? rangeOfUlong
theorem ullong_range is fa(x:Ullong) mathIntOfUllong x in? rangeOfUllong

op ushortOfMathInt (i:Int | i in? rangeOfUshort) : Ushort =
  the(x:Ushort) mathIntOfUshort x = i

op uintOfMathInt (i:Int | i in? rangeOfUint) : Uint   =
  the(x:Uint) mathIntOfUint   x = i

op ulongOfMathInt (i:Int | i in? rangeOfUlong) : Ulong  =
  the(x:Ulong) mathIntOfUlong  x = i

op ullongOfMathInt (i:Int | i in? rangeOfUllong) : Ullong =
  the(x:Ullong) mathIntOfUllong x = i

(* The signed integer types use the same amount of storage as their unsigned
counterparts [ISO 6.2.5/6]. Thus, the sizeof_... and ..._bits constants above
also apply to the signed integer types, not only the unsigned ones -- note that
the names of those constants make no reference to (un)signedness.

Similarly to the signed char type, we assume that the other signed integer types
use a two's complement representation with no padding bits. Thus, the
sizeof_... constants determine the values below for the ..._MIN and ..._MAX
limits of the signed integer types [ISO 5.2.4.2.1/1]. *)

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

type Sshort = | sshort (Bits | ofLength? short_bits)
type   Sint = | sint   (Bits | ofLength?   int_bits)
type  Slong = | slong  (Bits | ofLength?  long_bits)
type Sllong = | sllong (Bits | ofLength? llong_bits)

op mathIntOfSshort (sshort bs : Sshort) : Int = toInt bs
op mathIntOfSint   (sint   bs : Sint)   : Int = toInt bs
op mathIntOfSlong  (slong  bs : Slong)  : Int = toInt bs
op mathIntOfSllong (sllong bs : Sllong) : Int = toInt bs

op rangeOfSshort : FiniteSet Int = fn i:Int ->  SHRT_MIN <= i && i <=  SHRT_MAX
op rangeOfSint   : FiniteSet Int = fn i:Int ->   INT_MIN <= i && i <=   INT_MAX
op rangeOfSlong  : FiniteSet Int = fn i:Int ->  LONG_MIN <= i && i <=  LONG_MAX
op rangeOfSllong : FiniteSet Int = fn i:Int -> LLONG_MIN <= i && i <= LLONG_MAX

theorem sshort_range is fa(x:Sshort) mathIntOfSshort x in? rangeOfSshort
theorem   sint_range is fa(x:Sint)   mathIntOfSint   x in? rangeOfSint
theorem  slong_range is fa(x:Slong)  mathIntOfSlong  x in? rangeOfSlong
theorem sllong_range is fa(x:Sllong) mathIntOfSllong x in? rangeOfSllong

op sshortOfMathInt (i:Int | i in? rangeOfSshort) : Sshort =
  the(x:Sshort) mathIntOfSshort x = i

op sintOfMathInt (i:Int | i in? rangeOfSint) : Sint   =
  the(x:Sint) mathIntOfSint   x = i

op slongOfMathInt (i:Int | i in? rangeOfSlong) : Slong  =
  the(x:Slong) mathIntOfSlong  x = i

op sllongOfMathInt (i:Int | i in? rangeOfSllong) : Sllong =
  the(x:Sllong) mathIntOfSllong x = i

(* There are inclusion constraints among the ranges of the integer types [ISO
6.2.5/8], determined by the integer conversion ranks [ISO 6.3.1.1/1]. Given our
assumptions and constants introduced above, these inclusion constraints are
expressed via the following theorems on the sizeof_... constants. *)

theorem sizeof_short_int  is sizeof_short <= sizeof_int
theorem sizeof_int_long   is sizeof_int   <= sizeof_long
theorem sizeof_long_llong is sizeof_long  <= sizeof_llong

(* Our formalization currently does not include any extended unsigned integer
types [ISO 6.2.5/6] or extended signed integer types [ISO 6.2.5/4]. *)


%subsection (* Arrays *)

(* An array is a sequence of objects of the same type [ISO 6.2.5/20], which we
model as a list, with a constructor to keep arrays "separate" from other lists.

The following type is polymorphic and can be instantiated with any Metaslang
type, but the code generator will only accept array types instantiated with
Metaslang types that correspond to C types. *)

type Array a = | array List a

(* Each array has a length, i.e. number of elements. *)

op [a] length (array elems : Array a) : Nat =
  length elems

op [a] ofLength? (n:Nat) (arr:Array a) : Bool =
  length arr = n

(* The predicate ofLength? just defined can be used to construct array types of
given lengths (an array type includes the number of elements [ISO 6.2.5/20]),
e.g.
 (Array Sint | ofLength? 5)                         for   int[5]
 (Array (Array Char | ofLength? 2) | ofLength? 4)   for   char[2][4]
*)


%subsection (* Structures *)

(* A structure is a sequence of named objects, not necessarily of the same type
[ISO 6.2.5./20]. This corresponds to a Metaslang record almost perfectly, except
that in Metaslang record fields are ordered alphabetically, while in a C
structure members are ordered as declared by the program. It may be possible to
work around this mismatch by having the code generator map Metaslang fields like
"_a_first", "_b_second", "_c_third", "_d_fourth", etc. to C fields like "first",
"second", "third", "fourth", etc.

In order to represent a C structure type, a Metaslang record type must have all
all fields whose Metaslang types correspond to C types, e.g.
 {x:Sint, y:Sint}   for   struct {int x, int y}
*)


%subsection (* Type definitions *)

(* A type definition [ISO 6.7.7] assigns a synonym to an existing type. This
corresponds to Metaslang type definitions, e.g.
 type T = Uint   for   typedef unsigned int T
*)


%subsection (* Other types *)

(* We may extend this formalization with other Metaslang types that correspond
to C types, e.g. floating types [ISO 6.2.5/10]. *)


%section (* Constants *)

(* We define Metaslang ops that correspond to C constants. *)


%subsection (* Integer constants *)

(* An integer constant [ISO 6.4.4.1] denotes a natural number, in decimal,
hexadecimal, or octal notation. Since Metaslang does not support octal constants
and it internally translates decimal and hexadecimal constants to the same
representation, we introduce an enumeration that is used in subsequent ops to
indicate the desired base of constants. *)

type IntConstBase = | dec | hex | oct

(* The following ops create integer values out of natural numbers in the
appropriate ranges. The base argument does not affect the result, but is needed
so that the C code generator can generate, from the following ops, constants in
the desired base. In addition, the C code generator must generate appropriate U,
L, and LL suffixes. *)

op sintConstant (n:Nat | n in? rangeOfSint) (base:IntConstBase) : Sint =
  sintOfMathInt n

op slongConstant (n:Nat | n in? rangeOfSlong) (base:IntConstBase) : Slong =
  slongOfMathInt n

op sllongConstant (n:Nat | n in? rangeOfSllong) (base:IntConstBase) : Sllong =
  sllongOfMathInt n

op uintConstant (n:Nat | n in? rangeOfUint) (base:IntConstBase) : Uint =
  uintOfMathInt n

op ulongConstant (n:Nat | n in? rangeOfUlong) (base:IntConstBase) : Ulong =
  ulongOfMathInt n

op ullongConstant (n:Nat | n in? rangeOfSllong) (base:IntConstBase) : Ullong =
  ullongOfMathInt n


%subsection (* Other constants *)

(* We may extend this formalization with other Metaslang types that correspond
to C constants, e.g. floating constants [ISO 6.4.4.2]. *)


%section (* Operators *)

(* We introduce Metaslang operators that correpond to C operators. If a
Metaslang spec is refined to use such Metaslang operators, the code generator
can map them to the corresponding C operators. *)


%subsection (* Integer conversions *)

(* An integer value can be converted into (a value of) an(other) integer type
[ISO 6.3.1.3].

The conversion is described in terms of the mathematical value of the integer.
If the new type can represent it, the (mathematical) value is unchanged [ISO
6.3.1.3/1].

Otherwise, the outcome depends on whether the new type is unsigned or not. Note
that the new type could be char, which is classified as neither a signed nor an
unsigned integer type [ISO 6.2.5/4, 6.2.5/6]. But according to [ISO 6.2.5/15]
the char type has the same behavior as either signed or unsigned char, and this
choice is captured by ops plainCharsAreSigned and plainCharsAreUnsigned,
introduced earlier.

If the new type is unsigned, we apply the (flooring) modulo operation, with
argument one plus the maximum representable integer in the type. This is
equivalent to the repeated subtraction or addition mentioned in [ISO 6.3.1.3/2].

If the new type is signed, the outcome is non-standard [ISO 6.3.1.3/3]. We use
subtype constraints to ensure that the results of the conversions is always
standard and well-defined; in other words, we disallow conversions when the
outcome is non-standard.

There are 11 integer types:
 uchar ushort uint ulong ullong
 schar sshort sint slong sllong
 char
Thus, there are 11 * 11 - 11 = 110 conversion ops. *)

% ucharOf...:

op ucharOfUshort (x:Ushort) : Uchar =
  ucharOfMathInt (mathIntOfUshort x modF (1 + UCHAR_MAX))

op ucharOfUint (x:Uint) : Uchar =
  ucharOfMathInt (mathIntOfUint x modF (1 + UCHAR_MAX))

op ucharOfUlong (x:Ulong) : Uchar =
  ucharOfMathInt (mathIntOfUlong x modF (1 + UCHAR_MAX))

op ucharOfUllong (x:Ullong) : Uchar =
  ucharOfMathInt (mathIntOfUllong x modF (1 + UCHAR_MAX))

op ucharOfSchar (x:Schar) : Uchar =
  ucharOfMathInt (mathIntOfSchar x modF (1 + UCHAR_MAX))

op ucharOfSshort (x:Sshort) : Uchar =
  ucharOfMathInt (mathIntOfSshort x modF (1 + UCHAR_MAX))

op ucharOfSint (x:Sint) : Uchar =
  ucharOfMathInt (mathIntOfSint x modF (1 + UCHAR_MAX))

op ucharOfSlong (x:Slong) : Uchar =
  ucharOfMathInt (mathIntOfSlong x modF (1 + UCHAR_MAX))

op ucharOfSllong (x:Sllong) : Uchar =
  ucharOfMathInt (mathIntOfSllong x modF (1 + UCHAR_MAX))

op ucharOfChar (x:Char) : Uchar =
  ucharOfMathInt (mathIntOfChar x modF (1 + UCHAR_MAX))

% ushortOf...:

op ushortOfUchar (x:Uchar) : Ushort =
  ushortOfMathInt (mathIntOfUchar x)

op ushortOfUint (x:Uint) : Ushort =
  ushortOfMathInt (mathIntOfUint x modF (1 + USHRT_MAX))

op ushortOfUlong (x:Ulong) : Ushort =
  ushortOfMathInt (mathIntOfUlong x modF (1 + USHRT_MAX))

op ushortOfUllong (x:Ullong) : Ushort =
  ushortOfMathInt (mathIntOfUllong x modF (1 + USHRT_MAX))

op ushortOfSchar (x:Schar) : Ushort =
  ushortOfMathInt (mathIntOfSchar x modF (1 + USHRT_MAX))

op ushortOfSshort (x:Sshort) : Ushort =
  ushortOfMathInt (mathIntOfSshort x modF (1 + USHRT_MAX))

op ushortOfSint (x:Sint) : Ushort =
  ushortOfMathInt (mathIntOfSint x modF (1 + USHRT_MAX))

op ushortOfSlong (x:Slong) : Ushort =
  ushortOfMathInt (mathIntOfSlong x modF (1 + USHRT_MAX))

op ushortOfSllong (x:Sllong) : Ushort =
  ushortOfMathInt (mathIntOfSllong x modF (1 + USHRT_MAX))

op ushortOfChar (x:Char) : Ushort =
  ushortOfMathInt (mathIntOfChar x modF (1 + USHRT_MAX))

% uintOf ...:

op uintOfUchar (x:Uchar) : Uint =
  uintOfMathInt (mathIntOfUchar x)

op uintOfUshort (x:Ushort) : Uint =
  uintOfMathInt (mathIntOfUshort x)

op uintOfUlong (x:Ulong) : Uint =
  uintOfMathInt (mathIntOfUlong x modF (1 + UINT_MAX))

op uintOfUllong (x:Ullong) : Uint =
  uintOfMathInt (mathIntOfUllong x modF (1 + UINT_MAX))

op uintOfSchar (x:Schar) : Uint =
  uintOfMathInt (mathIntOfSchar x modF (1 + UINT_MAX))

op uintOfSshort (x:Sshort) : Uint =
  uintOfMathInt (mathIntOfSshort x modF (1 + UINT_MAX))

op uintOfSint (x:Sint) : Uint =
  uintOfMathInt (mathIntOfSint x modF (1 + UINT_MAX))

op uintOfSlong (x:Slong) : Uint =
  uintOfMathInt (mathIntOfSlong x modF (1 + UINT_MAX))

op uintOfSllong (x:Sllong) : Uint =
  uintOfMathInt (mathIntOfSllong x modF (1 + UINT_MAX))

op uintOfChar (x:Char) : Uint =
  uintOfMathInt (mathIntOfChar x modF (1 + UINT_MAX))

% ulongOf...:

op ulongOfUchar (x:Uchar) : Ulong =
  ulongOfMathInt (mathIntOfUchar x)

op ulongOfUshort (x:Ushort) : Ulong =
  ulongOfMathInt (mathIntOfUshort x)

op ulongOfUint (x:Uint) : Ulong =
  ulongOfMathInt (mathIntOfUint x)

op ulongOfUllong (x:Ullong) : Ulong =
  ulongOfMathInt (mathIntOfUllong x modF (1 + ULONG_MAX))

op ulongOfSchar (x:Schar) : Ulong =
  ulongOfMathInt (mathIntOfSchar x modF (1 + ULONG_MAX))

op ulongOfSshort (x:Sshort) : Ulong =
  ulongOfMathInt (mathIntOfSshort x modF (1 + ULONG_MAX))

op ulongOfSint (x:Sint) : Ulong =
  ulongOfMathInt (mathIntOfSint x modF (1 + ULONG_MAX))

op ulongOfSlong (x:Slong) : Ulong =
  ulongOfMathInt (mathIntOfSlong x modF (1 + ULONG_MAX))

op ulongOfSllong (x:Sllong) : Ulong =
  ulongOfMathInt (mathIntOfSllong x modF (1 + ULONG_MAX))

op ulongOfChar (x:Char) : Ulong =
  ulongOfMathInt (mathIntOfChar x modF (1 + ULONG_MAX))

% ullongOf...:

op ullongOfUchar (x:Uchar) : Ullong =
  ullongOfMathInt (mathIntOfUchar x)

op ullongOfUshort (x:Ushort) : Ullong =
  ullongOfMathInt (mathIntOfUshort x)

op ullongOfUint (x:Uint) : Ullong =
  ullongOfMathInt (mathIntOfUint x)

op ullongOfUlong (x:Ulong) : Ullong =
  ullongOfMathInt (mathIntOfUlong x)

op ullongOfSchar (x:Schar) : Ullong =
  ullongOfMathInt (mathIntOfSchar x modF (1 + ULLONG_MAX))

op ullongOfSshort (x:Sshort) : Ullong =
  ullongOfMathInt (mathIntOfSshort x modF (1 + ULLONG_MAX))

op ullongOfSint (x:Sint) : Ullong =
  ullongOfMathInt (mathIntOfSint x modF (1 + ULLONG_MAX))

op ullongOfSlong (x:Slong) : Ullong =
  ullongOfMathInt (mathIntOfSlong x modF (1 + ULLONG_MAX))

op ullongOfSllong (x:Sllong) : Ullong =
  ullongOfMathInt (mathIntOfSllong x modF (1 + ULLONG_MAX))

op ullongOfChar (x:Char) : Ullong =
  ullongOfMathInt (mathIntOfChar x modF (1 + ULLONG_MAX))

% scharOf...:

op scharOfUchar (x:Uchar | mathIntOfUchar x in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfUchar x)

op scharOfUshort (x:Ushort | mathIntOfUshort x in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfUshort x)

op scharOfUint (x:Uint | mathIntOfUint x in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfUint x)

op scharOfUlong (x:Ulong | mathIntOfUlong x in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfUlong x)

op scharOfUllong (x:Ullong | mathIntOfUllong x in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfUllong x)

op scharOfSshort (x:Sshort | mathIntOfSshort x in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfSshort x)

op scharOfSint (x:Sint | mathIntOfSint x in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfSint x)

op scharOfSlong (x:Slong | mathIntOfSlong x in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfSlong x)

op scharOfSllong (x:Sllong | mathIntOfSllong x in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfSllong x)

op scharOfChar (x:Char | mathIntOfChar x in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfChar x)

% sshortOf...:

op sshortOfUchar (x:Uchar) : Sshort =
  sshortOfMathInt (mathIntOfUchar x)

op sshortOfUshort (x:Ushort | mathIntOfUshort x in? rangeOfSshort) : Sshort =
  sshortOfMathInt (mathIntOfUshort x)

op sshortOfUint (x:Uint | mathIntOfUint x in? rangeOfSshort) : Sshort =
  sshortOfMathInt (mathIntOfUint x)

op sshortOfUlong (x:Ulong | mathIntOfUlong x in? rangeOfSshort) : Sshort =
  sshortOfMathInt (mathIntOfUlong x)

op sshortOfUllong (x:Ullong | mathIntOfUllong x in? rangeOfSshort) : Sshort =
  sshortOfMathInt (mathIntOfUllong x)

op sshortOfSchar (x:Schar) : Sshort =
  sshortOfMathInt (mathIntOfSchar x)

op sshortOfSint (x:Sint | mathIntOfSint x in? rangeOfSshort) : Sshort =
  sshortOfMathInt (mathIntOfSint x)

op sshortOfSlong (x:Slong | mathIntOfSlong x in? rangeOfSshort) : Sshort =
  sshortOfMathInt (mathIntOfSlong x)

op sshortOfSllong (x:Sllong | mathIntOfSllong x in? rangeOfSshort) : Sshort =
  sshortOfMathInt (mathIntOfSllong x)

op sshortOfChar (x:Char) : Sshort =
  sshortOfMathInt (mathIntOfChar x)

% sintOf...:

op sintOfUchar (x:Uchar) : Sint =
  sintOfMathInt (mathIntOfUchar x)

op sintOfUshort (x:Ushort | mathIntOfUshort x in? rangeOfSint) : Sint =
  sintOfMathInt (mathIntOfUshort x)

op sintOfUint (x:Uint | mathIntOfUint x in? rangeOfSint) : Sint =
  sintOfMathInt (mathIntOfUint x)

op sintOfUlong (x:Ulong | mathIntOfUlong x in? rangeOfSint) : Sint =
  sintOfMathInt (mathIntOfUlong x)

op sintOfUllong (x:Ullong | mathIntOfUllong x in? rangeOfSint) : Sint =
  sintOfMathInt (mathIntOfUllong x)

op sintOfSchar (x:Schar) : Sint =
  sintOfMathInt (mathIntOfSchar x)

op sintOfSshort (x:Sshort) : Sint =
  sintOfMathInt (mathIntOfSshort x)

op sintOfSlong (x:Slong | mathIntOfSlong x in? rangeOfSint) : Sint =
  sintOfMathInt (mathIntOfSlong x)

op sintOfSllong (x:Sllong | mathIntOfSllong x in? rangeOfSint) : Sint =
  sintOfMathInt (mathIntOfSllong x)

op sintOfChar (x:Char) : Sint =
  sintOfMathInt (mathIntOfChar x)

% slongOf...:

op slongOfUchar (x:Uchar) : Slong =
  slongOfMathInt (mathIntOfUchar x)

op slongOfUshort (x:Ushort | mathIntOfUshort x in? rangeOfSlong) : Slong =
  slongOfMathInt (mathIntOfUshort x)

op slongOfUint (x:Uint | mathIntOfUint x in? rangeOfSlong) : Slong =
  slongOfMathInt (mathIntOfUint x)

op slongOfUlong (x:Ulong | mathIntOfUlong x in? rangeOfSlong) : Slong =
  slongOfMathInt (mathIntOfUlong x)

op slongOfUllong (x:Ullong | mathIntOfUllong x in? rangeOfSlong) : Slong =
  slongOfMathInt (mathIntOfUllong x)

op slongOfSchar (x:Schar) : Slong =
  slongOfMathInt (mathIntOfSchar x)

op slongOfSshort (x:Sshort) : Slong =
  slongOfMathInt (mathIntOfSshort x)

op slongOfSint (x:Sint) : Slong =
  slongOfMathInt (mathIntOfSint x)

op slongOfSllong (x:Sllong | mathIntOfSllong x in? rangeOfSlong) : Slong =
  slongOfMathInt (mathIntOfSllong x)

op slongOfChar (x:Char) : Slong =
  slongOfMathInt (mathIntOfChar x)

% sllongOf...:

op sllongOfUchar (x:Uchar) : Sllong =
  sllongOfMathInt (mathIntOfUchar x)

op sllongOfUshort (x:Ushort | mathIntOfUshort x in? rangeOfSllong) : Sllong =
  sllongOfMathInt (mathIntOfUshort x)

op sllongOfUint (x:Uint | mathIntOfUint x in? rangeOfSllong) : Sllong =
  sllongOfMathInt (mathIntOfUint x)

op sllongOfUlong (x:Ulong | mathIntOfUlong x in? rangeOfSllong) : Sllong =
  sllongOfMathInt (mathIntOfUlong x)

op sllongOfUllong (x:Ullong | mathIntOfUllong x in? rangeOfSllong) : Sllong =
  sllongOfMathInt (mathIntOfUllong x)

op sllongOfSchar (x:Schar) : Sllong =
  sllongOfMathInt (mathIntOfSchar x)

op sllongOfSshort (x:Sshort) : Sllong =
  sllongOfMathInt (mathIntOfSshort x)

op sllongOfSint (x:Sint) : Sllong =
  sllongOfMathInt (mathIntOfSint x)

op sllongOfSlong (x:Slong) : Sllong =
  sllongOfMathInt (mathIntOfSlong x)

op sllongOfChar (x:Char) : Sllong =
  sllongOfMathInt (mathIntOfChar x)

% charOf...:

op charOfUchar (x:Uchar | mathIntOfUchar x in? rangeOfChar) : Char =
  charOfMathInt (mathIntOfUchar x)

op charOfUshort (x:Ushort |
   plainCharsAreSigned => mathIntOfUshort x in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfUshort x)
  else charOfMathInt (mathIntOfUshort x modF (1 + UCHAR_MAX))

op charOfUint (x:Uint |
   plainCharsAreSigned => mathIntOfUint x in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfUint x)
  else charOfMathInt (mathIntOfUint x modF (1 + UCHAR_MAX))

op charOfUlong (x:Ulong |
   plainCharsAreSigned => mathIntOfUlong x in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfUlong x)
  else charOfMathInt (mathIntOfUlong x modF (1 + UCHAR_MAX))

op charOfUllong (x:Ullong |
   plainCharsAreSigned => mathIntOfUllong x in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfUllong x)
  else charOfMathInt (mathIntOfUllong x modF (1 + UCHAR_MAX))

op charOfSchar (x:Schar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfSchar x)
  else charOfMathInt (mathIntOfSchar x modF (1 + UCHAR_MAX))

op charOfSshort (x:Sshort |
   plainCharsAreSigned => mathIntOfSshort x in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfSshort x)
  else charOfMathInt (mathIntOfSshort x modF (1 + UCHAR_MAX))

op charOfSint (x:Sint |
   plainCharsAreSigned => mathIntOfSint x in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfSint x)
  else charOfMathInt (mathIntOfSint x modF (1 + UCHAR_MAX))

op charOfSlong (x:Slong |
   plainCharsAreSigned => mathIntOfSlong x in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfSlong x)
  else charOfMathInt (mathIntOfSlong x modF (1 + UCHAR_MAX))

op charOfSllong (x:Sllong |
   plainCharsAreSigned => mathIntOfSllong x in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfSllong x)
  else charOfMathInt (mathIntOfSllong x modF (1 + UCHAR_MAX))

(* Converting between integer types with the same integer conversion rank [ISO
6.3.1.1/1] leaves the bits unchanged. *)

theorem ucharOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ucharOfSchar (schar bs) = uchar bs

theorem ucharOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ucharOfChar (char bs) = uchar bs

theorem scharOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT && toNat bs in? rangeOfSchar =>
    ucharOfSchar (schar bs) = uchar bs

theorem scharOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT &&
              mathIntOfChar (char bs) in? rangeOfSchar =>
    scharOfChar (char bs) = schar bs

theorem charOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT && toNat bs in? rangeOfChar =>
    charOfUchar (uchar bs) = char bs

theorem charOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT && toInt bs in? rangeOfChar =>
    charOfSchar (schar bs) = char bs

theorem ushortOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    ushortOfSshort (sshort bs) = ushort bs

theorem sshortOfUshort_bits is
  fa(bs:Bits) length bs = short_bits && toNat bs in? rangeOfSshort =>
    sshortOfUshort (ushort bs) = sshort bs

theorem uintOfSint_bits is
  fa(bs:Bits) length bs = int_bits =>
    uintOfSint (sint bs) = uint bs

theorem sintOfUint_bits is
  fa(bs:Bits) length bs = int_bits && toNat bs in? rangeOfSint =>
    sintOfUint (uint bs) = sint bs

theorem ulongOfSlong_bits is
  fa(bs:Bits) length bs = long_bits =>
    ulongOfSlong (slong bs) = ulong bs

theorem slongOfUlong_bits is
  fa(bs:Bits) length bs = long_bits && toNat bs in? rangeOfSlong =>
    slongOfUlong (ulong bs) = slong bs

theorem ullongOfSllong_bits is
  fa(bs:Bits) length bs = llong_bits =>
    ullongOfSllong (sllong bs) = ullong bs

theorem sllongOfUllong_bits is
  fa(bs:Bits) length bs = llong_bits && toNat bs in? rangeOfSllong =>
    sllongOfUllong (ullong bs) = sllong bs

(* Converting from a signed or unsigned integer type to an unsigned integer type
of higher rank amounts to zero-extending the bits. *)

theorem ushortOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ushortOfUchar (uchar bs) = ushort (zeroExtend (bs, short_bits))

theorem ushortOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ushortOfSchar (schar bs) = ushort (zeroExtend (bs, short_bits))

theorem ushortOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ushortOfChar (char bs) = ushort (zeroExtend (bs, short_bits))

theorem uintOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    uintOfUchar (uchar bs) = uint (zeroExtend (bs, int_bits))

theorem uintOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    uintOfSchar (schar bs) = uint (zeroExtend (bs, int_bits))

theorem uintOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    uintOfChar (char bs) = uint (zeroExtend (bs, int_bits))

theorem uintOfUshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    uintOfUshort (ushort bs) = uint (zeroExtend (bs, int_bits))

theorem uintOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    uintOfSshort (sshort bs) = uint (zeroExtend (bs, int_bits))

theorem ulongOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ulongOfUchar (uchar bs) = ulong (zeroExtend (bs, long_bits))

theorem ulongOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ulongOfSchar (schar bs) = ulong (zeroExtend (bs, long_bits))

theorem ulongOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ulongOfChar (char bs) = ulong (zeroExtend (bs, long_bits))

theorem ulongOfUshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    ulongOfUshort (ushort bs) = ulong (zeroExtend (bs, long_bits))

theorem ulongOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    ulongOfSshort (sshort bs) = ulong (zeroExtend (bs, long_bits))

theorem ulongOfUint_bits is
  fa(bs:Bits) length bs = int_bits =>
    ulongOfUint (uint bs) = ulong (zeroExtend (bs, long_bits))

theorem ulongOfSint_bits is
  fa(bs:Bits) length bs = int_bits =>
    ulongOfSint (sint bs) = ulong (zeroExtend (bs, long_bits))

theorem ullongOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ullongOfUchar (uchar bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ullongOfSchar (schar bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ullongOfChar (char bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfUshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    ullongOfUshort (ushort bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    ullongOfSshort (sshort bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfUint_bits is
  fa(bs:Bits) length bs = int_bits =>
    ullongOfUint (uint bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfSint_bits is
  fa(bs:Bits) length bs = int_bits =>
    ullongOfSint (sint bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfUlong_bits is
  fa(bs:Bits) length bs = long_bits =>
    ullongOfUlong (ulong bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfSlong_bits is
  fa(bs:Bits) length bs = long_bits =>
    ullongOfSlong (slong bs) = ullong (zeroExtend (bs, llong_bits))

(* Converting from an unsigned integer type to a signed integer type of higher
rank amounts to zero-extending the bits. *)

theorem sshortOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    sshortOfUchar (uchar bs) = sshort (zeroExtend (bs, short_bits))

theorem sshortOfChar_bits_unsigned is
  plainCharsAreUnsigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     sshortOfChar (char bs) = sshort (zeroExtend (bs, short_bits)))

theorem sintOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    sintOfUchar (uchar bs) = sint (zeroExtend (bs, int_bits))

theorem sintOfChar_bits_unsigned is
  plainCharsAreUnsigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     sintOfChar (char bs) = sint (zeroExtend (bs, int_bits)))

theorem sintOfUshort_bits is
  fa(bs:Bits) length bs = short_bits && toNat bs in? rangeOfSint =>
    sintOfUshort (ushort bs) = sint (zeroExtend (bs, int_bits))

theorem slongOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    slongOfUchar (uchar bs) = slong (zeroExtend (bs, long_bits))

theorem slongOfChar_bits_unsigned is
  plainCharsAreUnsigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     slongOfChar (char bs) = slong (zeroExtend (bs, long_bits)))

theorem slongOfUshort_bits is
  fa(bs:Bits) length bs = short_bits && toNat bs in? rangeOfSlong =>
    slongOfUshort (ushort bs) = slong (zeroExtend (bs, long_bits))

theorem slongOfUint_bits is
  fa(bs:Bits) length bs = int_bits && toNat bs in? rangeOfSlong =>
    slongOfUint (uint bs) = slong (zeroExtend (bs, long_bits))

theorem sllongOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    sllongOfUchar (uchar bs) = sllong (zeroExtend (bs, llong_bits))

theorem sllongOfChar_bits_unsigned is
  plainCharsAreUnsigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     sllongOfChar (char bs) = sllong (zeroExtend (bs, llong_bits)))

theorem sllongOfUshort_bits is
  fa(bs:Bits) length bs = short_bits && toNat bs in? rangeOfSllong =>
    sllongOfUshort (ushort bs) = sllong (zeroExtend (bs, llong_bits))

theorem sllongOfUint_bits is
  fa(bs:Bits) length bs = int_bits && toNat bs in? rangeOfSllong =>
    sllongOfUint (uint bs) = sllong (zeroExtend (bs, llong_bits))

theorem sllongOfUlong_bits is
  fa(bs:Bits) length bs = long_bits && toNat bs in? rangeOfSllong =>
    sllongOfUlong (ulong bs) = sllong (zeroExtend (bs, llong_bits))

(* Converting from a signed integer type to a signed integer type of higher rank
amounts to sign-extending the bits. *)

theorem sshortOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    sshortOfSchar (schar bs) = sshort (signExtend (bs, short_bits))

theorem sshortOfChar_bits_signed is
  plainCharsAreSigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     sshortOfChar (char bs) = sshort (signExtend (bs, short_bits)))

theorem sintOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    sintOfSchar (schar bs) = sint (signExtend (bs, int_bits))

theorem sintOfChar_bits_signed is
  plainCharsAreSigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     sintOfChar (char bs) = sint (signExtend (bs, int_bits)))

theorem sintOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    sintOfSshort (sshort bs) = sint (signExtend (bs, int_bits))

theorem slongOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    slongOfSchar (schar bs) = slong (signExtend (bs, long_bits))

theorem slongOfChar_bits_signed is
  plainCharsAreSigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     slongOfChar (char bs) = slong (signExtend (bs, long_bits)))

theorem slongOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    slongOfSshort (sshort bs) = slong (signExtend (bs, long_bits))

theorem slongOfSint_bits is
  fa(bs:Bits) length bs = int_bits =>
    slongOfSint (sint bs) = slong (signExtend (bs, long_bits))

theorem sllongOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    sllongOfSchar (schar bs) = sllong (signExtend (bs, llong_bits))

theorem sllongOfChar_bits_signed is
  plainCharsAreSigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     sllongOfChar (char bs) = sllong (signExtend (bs, llong_bits)))

theorem sllongOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    sllongOfSshort (sshort bs) = sllong (signExtend (bs, llong_bits))

theorem sllongOfSint_bits is
  fa(bs:Bits) length bs = int_bits =>
    sllongOfSint (sint bs) = sllong (signExtend (bs, llong_bits))

theorem sllongOfSlong_bits is
  fa(bs:Bits) length bs = long_bits =>
    sllongOfSlong (slong bs) = sllong (signExtend (bs, llong_bits))

(* Converting from a signed or unsigned integer type to a signed or unsigned
integer type of lower rank amounts to truncating the most significant bits. *)

theorem ucharOfUshort_bit is
  fa(bs:Bits) length bs = short_bits =>
    ucharOfUshort (ushort bs) = uchar (suffix (bs, CHAR_BIT))

theorem ucharOfUint_bit is
  fa(bs:Bits) length bs = int_bits =>
    ucharOfUint (uint bs) = uchar (suffix (bs, CHAR_BIT))

theorem ucharOfUlong_bit is
  fa(bs:Bits) length bs = long_bits =>
    ucharOfUlong (ulong bs) = uchar (suffix (bs, CHAR_BIT))

theorem ucharOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    ucharOfUllong (ullong bs) = uchar (suffix (bs, CHAR_BIT))

theorem ucharOfSshort_bit is
  fa(bs:Bits) length bs = short_bits =>
    ucharOfSshort (sshort bs) = uchar (suffix (bs, CHAR_BIT))

theorem ucharOfSint_bit is
  fa(bs:Bits) length bs = int_bits =>
    ucharOfSint (sint bs) = uchar (suffix (bs, CHAR_BIT))

theorem ucharOfSlong_bit is
  fa(bs:Bits) length bs = long_bits =>
    ucharOfSlong (slong bs) = uchar (suffix (bs, CHAR_BIT))

theorem ucharOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    ucharOfSllong (sllong bs) = uchar (suffix (bs, CHAR_BIT))

theorem ushortOfUint_bit is
  fa(bs:Bits) length bs = int_bits =>
    ushortOfUint (uint bs) = ushort (suffix (bs, CHAR_BIT))

theorem ushortOfUlong_bit is
  fa(bs:Bits) length bs = long_bits =>
    ushortOfUlong (ulong bs) = ushort (suffix (bs, CHAR_BIT))

theorem ushortOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    ushortOfUllong (ullong bs) = ushort (suffix (bs, CHAR_BIT))

theorem ushortOfSint_bit is
  fa(bs:Bits) length bs = int_bits =>
    ushortOfSint (sint bs) = ushort (suffix (bs, CHAR_BIT))

theorem ushortOfSlong_bit is
  fa(bs:Bits) length bs = long_bits =>
    ushortOfSlong (slong bs) = ushort (suffix (bs, CHAR_BIT))

theorem ushortOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    ushortOfSllong (sllong bs) = ushort (suffix (bs, CHAR_BIT))

theorem uintOfUlong_bit is
  fa(bs:Bits) length bs = long_bits =>
    uintOfUlong (ulong bs) = uint (suffix (bs, CHAR_BIT))

theorem uintOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    uintOfUllong (ullong bs) = uint (suffix (bs, CHAR_BIT))

theorem uintOfSlong_bit is
  fa(bs:Bits) length bs = long_bits =>
    uintOfSlong (slong bs) = uint (suffix (bs, CHAR_BIT))

theorem uintOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    uintOfSllong (sllong bs) = uint (suffix (bs, CHAR_BIT))

theorem ulongOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    ulongOfUllong (ullong bs) = ulong (suffix (bs, CHAR_BIT))

theorem ulongOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    ulongOfSllong (sllong bs) = ulong (suffix (bs, CHAR_BIT))

theorem scharOfUshort_bit is
  fa(bs:Bits) length bs = short_bits && toNat bs in? rangeOfSchar =>
    scharOfUshort (ushort bs) = schar (suffix (bs, CHAR_BIT))

theorem scharOfUint_bit is
  fa(bs:Bits) length bs = int_bits && toNat bs in? rangeOfSchar =>
    scharOfUint (uint bs) = schar (suffix (bs, CHAR_BIT))

theorem scharOfUlong_bit is
  fa(bs:Bits) length bs = long_bits && toNat bs in? rangeOfSchar =>
    scharOfUlong (ulong bs) = schar (suffix (bs, CHAR_BIT))

theorem scharOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits && toNat bs in? rangeOfSchar =>
    scharOfUllong (ullong bs) = schar (suffix (bs, CHAR_BIT))

theorem scharOfSshort_bit is
  fa(bs:Bits) length bs = short_bits && toInt bs in? rangeOfSchar =>
    scharOfSshort (sshort bs) = schar (suffix (bs, CHAR_BIT))

theorem scharOfSint_bit is
  fa(bs:Bits) length bs = int_bits && toInt bs in? rangeOfSchar =>
    scharOfSint (sint bs) = schar (suffix (bs, CHAR_BIT))

theorem scharOfSlong_bit is
  fa(bs:Bits) length bs = long_bits && toInt bs in? rangeOfSchar =>
    scharOfSlong (slong bs) = schar (suffix (bs, CHAR_BIT))

theorem scharOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits && toInt bs in? rangeOfSchar =>
    scharOfSllong (sllong bs) = schar (suffix (bs, CHAR_BIT))

theorem sshortOfUint_bit is
  fa(bs:Bits) length bs = int_bits && toNat bs in? rangeOfSshort =>
    sshortOfUint (uint bs) = sshort (suffix (bs, CHAR_BIT))

theorem sshortOfUlong_bit is
  fa(bs:Bits) length bs = long_bits && toNat bs in? rangeOfSshort =>
    sshortOfUlong (ulong bs) = sshort (suffix (bs, CHAR_BIT))

theorem sshortOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits && toNat bs in? rangeOfSshort =>
    sshortOfUllong (ullong bs) = sshort (suffix (bs, CHAR_BIT))

theorem sshortOfSint_bit is
  fa(bs:Bits) length bs = int_bits && toInt bs in? rangeOfSshort =>
    sshortOfSint (sint bs) = sshort (suffix (bs, CHAR_BIT))

theorem sshortOfSlong_bit is
  fa(bs:Bits) length bs = long_bits && toInt bs in? rangeOfSshort =>
    sshortOfSlong (slong bs) = sshort (suffix (bs, CHAR_BIT))

theorem sshortOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits && toInt bs in? rangeOfSshort =>
    sshortOfSllong (sllong bs) = sshort (suffix (bs, CHAR_BIT))

theorem sintOfUlong_bit is
  fa(bs:Bits) length bs = long_bits && toNat bs in? rangeOfSint =>
    sintOfUlong (ulong bs) = sint (suffix (bs, CHAR_BIT))

theorem sintOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits && toNat bs in? rangeOfSint =>
    sintOfUllong (ullong bs) = sint (suffix (bs, CHAR_BIT))

theorem sintOfSlong_bit is
  fa(bs:Bits) length bs = long_bits && toInt bs in? rangeOfSint =>
    sintOfSlong (slong bs) = sint (suffix (bs, CHAR_BIT))

theorem sintOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits && toInt bs in? rangeOfSint =>
    sintOfSllong (sllong bs) = sint (suffix (bs, CHAR_BIT))

theorem slongOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits && toNat bs in? rangeOfSlong =>
    slongOfUllong (ullong bs) = slong (suffix (bs, CHAR_BIT))

theorem slongOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits && toInt bs in? rangeOfSlong =>
    slongOfSllong (sllong bs) = slong (suffix (bs, CHAR_BIT))

theorem charOfUshort_bit is
  fa(bs:Bits) length bs = short_bits && toNat bs in? rangeOfChar =>
    charOfUshort (ushort bs) = char (suffix (bs, CHAR_BIT))

theorem charOfUint_bit is
  fa(bs:Bits) length bs = int_bits && toNat bs in? rangeOfChar =>
    charOfUint (uint bs) = char (suffix (bs, CHAR_BIT))

theorem charOfUlong_bit is
  fa(bs:Bits) length bs = long_bits && toNat bs in? rangeOfChar =>
    charOfUlong (ulong bs) = char (suffix (bs, CHAR_BIT))

theorem charOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits && toNat bs in? rangeOfChar =>
    charOfUllong (ullong bs) = char (suffix (bs, CHAR_BIT))

theorem charOfSshort_bit is
  fa(bs:Bits) length bs = short_bits && toInt bs in? rangeOfChar =>
    charOfSshort (sshort bs) = char (suffix (bs, CHAR_BIT))

theorem charOfSint_bit is
  fa(bs:Bits) length bs = int_bits && toInt bs in? rangeOfChar =>
    charOfSint (sint bs) = char (suffix (bs, CHAR_BIT))

theorem charOfSlong_bit is
  fa(bs:Bits) length bs = long_bits && toInt bs in? rangeOfChar =>
    charOfSlong (slong bs) = char (suffix (bs, CHAR_BIT))

theorem charOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits && toInt bs in? rangeOfChar =>
    charOfSllong (sllong bs) = char (suffix (bs, CHAR_BIT))


%subsection (* Integer operators *)

(* The unary operator + [ISO 6.5.3.3/2] promotes [ISO 6.3.1.1/2] [ISO C2.10] its
integer operand and leaves it unchanged. Because promotion turns every integer
of integer conversion rank [ISO 6.3.1.1/1] lower than sint/uint into sint or
uint, we only need to define versions of unary + for sint/uint and types of
higher rank. The C code generator should not generate casts for conversion ops
that carry out the needed promotions. The "_1" part of the name of the following
ops serves to distinguish them from those for binary +, defined later. *)

op +_1_sint   (x:Sint  ) : Sint   = x
op +_1_slong  (x:Slong ) : Slong  = x
op +_1_sllong (x:Sllong) : Sllong = x
op +_1_uint   (x:Uint  ) : Uint   = x
op +_1_ulong  (x:Ulong ) : Ulong  = x
op +_1_ullong (x:Ullong) : Ullong = x

(* The unary - operator [ISO 6.5.3.3/3] returns the negative of its promoted
operand. Analogously to unary +, we only define ops for sint/uint and higher
ranks.

If the operand is unsigned, we follow the laws of arithmetic modulo one plus the
maximum of the type of the operand [ISO 6.2.5/9]. If the operand is signed, the
ops are defined only if the negative of the operand can be represented in the
type, because otherwise the behavior is undefined [ISO 6.5/5]. *)

op -_1_sint   (x:Sint   | - mathIntOfSint   x in? rangeOfSint  ) : Sint   =
    sintOfMathInt (- mathIntOfSint   x)
op -_1_slong  (x:Slong  | - mathIntOfSlong  x in? rangeOfSlong ) : Slong  =
   slongOfMathInt (- mathIntOfSlong  x)
op -_1_sllong (x:Sllong | - mathIntOfSllong x in? rangeOfSllong) : Sllong =
  sllongOfMathInt (- mathIntOfSllong x)

op -_1_uint   (x:Uint  ) : Uint   =
    uintOfMathInt ((- mathIntOfUint   x) modF (1 +   UINT_MAX))
op -_1_ulong  (x:Ulong ) : Ulong  =
   ulongOfMathInt ((- mathIntOfUlong  x) modF (1 +  ULONG_MAX))
op -_1_ullong (x:Ullong) : Ullong =
  ullongOfMathInt ((- mathIntOfUllong x) modF (1 + ULLONG_MAX))

(* The ~ operator [ISO 6.5.3.3/4] promotes its operand and returns its bitwise
complement. Analogously to unary + and -, we only define ops for sint/uint and
higher ranks. *)

op ~_sint   (sint   bs : Sint  ) : Sint   = sint   (not bs)
op ~_slong  (slong  bs : Slong ) : Slong  = slong  (not bs)
op ~_sllong (sllong bs : Sllong) : Sllong = sllong (not bs)
op ~_uint   (uint   bs : Uint  ) : Uint   = uint   (not bs)
op ~_ulong  (ulong  bs : Ulong ) : Ulong  = ulong  (not bs)
op ~_ullong (ullong bs : Ullong) : Ullong = ullong (not bs)

(* The ! operator [ISO 6.5.3.3/5] returns the signed int 1 or 0 depending on
whether the operator compares equal or unequal to 0. This operator performs no
promotion, so we define an op for every integer type. *)

op sint0 : Sint = sintOfMathInt 0
op sint1 : Sint = sintOfMathInt 1

op !_char   (char   bs : Char  ) : Sint = if zero? bs then sint1 else sint0
op !_schar  (uchar  bs : Uchar ) : Sint = if zero? bs then sint1 else sint0
op !_uchar  (uchar  bs : Uchar ) : Sint = if zero? bs then sint1 else sint0
op !_sshort (sshort bs : Sshort) : Sint = if zero? bs then sint1 else sint0
op !_ushort (ushort bs : Ushort) : Sint = if zero? bs then sint1 else sint0
op !_sint   (sint   bs : Sint  ) : Sint = if zero? bs then sint1 else sint0
op !_uint   (uint   bs : Uint  ) : Sint = if zero? bs then sint1 else sint0
op !_slong  (slong  bs : Slong ) : Sint = if zero? bs then sint1 else sint0
op !_ulong  (ulong  bs : Ulong ) : Sint = if zero? bs then sint1 else sint0
op !_sllong (sllong bs : Sllong) : Sint = if zero? bs then sint1 else sint0
op !_ullong (ullong bs : Ullong) : Sint = if zero? bs then sint1 else sint0

(* The binary *, /, %, +, and - operators perform the usual arithmetic
conversions on the operands [ISO 6.5.5/3, 6.5.6/4] and return their product [ISO
6.5.5/4], quotient (truncated toward 0) [ISO 6.5.5/5, 6.5.5/6], remainder [ISO
6.5.5/5, 6.5.5/6], sum [ISO 6.5.6/5], and difference [ISO 6.5.6/6]. Since the
usual arithmetic conversions [ISO 6.3.1.8] promote the operands and convert them
to a common type, we only need to define versions of these 5 operations for
sint/uint and types of higher rank. The C code generator should not generate
casts for conversion ops that carry out the needed usual arithmetic conversions.

If the operands are unsigned, we follow the laws of arithmetic modulo one plus
the maximum of the type of the operands [ISO 6.2.5/9]. If the operands are
signed, the ops are defined only if the product of the operands can be
represented in the type, because otherwise the behavior is undefined [ISO
6.5/5].

There are 30 ops (5 operators times 6 integer types). We factor commonalities of
(subsets of) the 30 ops into a few parameterized ops that are suitably
instantiated to define the 30 ops. A key parameter is the (exact) arithmetic
operation carried out by each of the 5 operators. *)

type ArithOp = Int * Int -> Int

(* The Metaslang ops +, -, and * have type ArithOp and can be used to
instantiate the ArithOp parameter. The Metaslang ops divT and modT do not have
type ArithOp due to the subtype restriction that the divisor is 0. Thus, we
define two versions that return 0 (an arbitrary value) when the divisor is 0.
As defined later, the divisor is never 0 when these ops are actually used. *)

op divT0 (i:Int, j:Int) : Int = if j ~= 0 then i divT j else 0
op modT0 (i:Int, j:Int) : Int = if j ~= 0 then i modT j else 0

(* Given an arithmetic operation and two signed integers of the same type, we
can determine whether the result is representable in the signed integer of the
same type. If it is, we can return the result. *)

op fitsSint? (aop:ArithOp, x:Sint, y:Sint) : Bool =
  let (x',y') = (mathIntOfSint x, mathIntOfSint y) in
  aop (x', y') in? rangeOfSint

op fitsSlong? (aop:ArithOp, x:Slong, y:Slong) : Bool =
  let (x',y') = (mathIntOfSlong x, mathIntOfSlong y) in
  aop (x', y') in? rangeOfSlong

op fitsSllong? (aop:ArithOp, x:Sllong, y:Sllong) : Bool =
  let (x',y') = (mathIntOfSllong x, mathIntOfSllong y) in
  aop (x', y') in? rangeOfSllong

op applySint
   (aop:ArithOp, x:Sint, y:Sint | fitsSint? (aop, x, y)) : Sint =
  sintOfMathInt (aop (mathIntOfSint x, mathIntOfSint y))

op applySlong
   (aop:ArithOp, x:Slong, y:Slong | fitsSlong? (aop, x, y)) : Slong =
  slongOfMathInt (aop (mathIntOfSlong x, mathIntOfSlong y))

op applySllong
   (aop:ArithOp, x:Sllong, y:Sllong | fitsSllong? (aop, x, y)) : Sllong =
  sllongOfMathInt (aop (mathIntOfSllong x, mathIntOfSllong y))

(* Given an arithmetic operation, we can return the result of applying it to two
unsigned integers of the same type. *)

op applyUint (aop:ArithOp, x:Uint, y:Uint) : Uint =
  uintOfMathInt
   (aop (mathIntOfUint x, mathIntOfUint y) modF (1 + UINT_MAX))

op applyUlong (aop:ArithOp, x:Ulong, y:Ulong) : Ulong =
  ulongOfMathInt
   (aop (mathIntOfUlong x, mathIntOfUlong y) modF (1 + ULONG_MAX))

op applyUllong (aop:ArithOp, x:Ullong, y:Ullong) : Ullong =
  ullongOfMathInt
   (aop (mathIntOfUllong x, mathIntOfUllong y) modF (1 + ULLONG_MAX))

(* With the above generic ops in hand, we can define the 30 ops for the 5
operators for each of the 6 integer types. Note that the ops for / and % include
the condition that the second operand is not 0. Thus, the 0 result that ops
divT0 and modT0 return in that case is never used, as mentioned earlier.

Note that we cannot use "%" in an op name because "%" starts an end-of-line
comment in Metaslang. So we use "//" instead. *)

% operator *

op *_sint
   (x:Sint, y:Sint | fitsSint? (( * ), x, y)) infixl 111 : Sint =
  applySint (( * ), x, y)

op *_slong
   (x:Slong, y:Slong | fitsSlong? (( * ), x, y)) infixl 111 : Slong =
  applySlong (( * ), x, y)

op *_sllong
   (x:Sllong, y:Sllong | fitsSllong? (( * ), x, y)) infixl 111 : Sllong =
  applySllong (( * ), x, y)

op *_uint (x:Uint, y:Uint) infixl 111 : Uint =
  applyUint (( * ), x, y)

op *_ulong (x:Ulong, y:Ulong) infixl 111 : Ulong =
  applyUlong (( * ), x, y)

op *_ullong (x:Ullong, y:Ullong) infixl 111 : Ullong =
  applyUllong (( * ), x, y)

% operator /

op /_sint
   (x:Sint, y:Sint | fitsSint? (divT0, x, y) && y ~= sintOfMathInt 0)
   infixl 111 : Sint =
  applySint (divT0, x, y)

op /_slong
   (x:Slong, y:Slong | fitsSlong? (divT0, x, y) && y ~= slongOfMathInt 0)
   infixl 111 : Slong =
  applySlong (divT0, x, y)

op /_sllong
   (x:Sllong, y:Sllong | fitsSllong? (divT0, x, y) && y ~= sllongOfMathInt 0)
   infixl 111 : Sllong =
  applySllong (divT0, x, y)

op /_uint
   (x:Uint, y:Uint | y ~= uintOfMathInt 0) infixl 111 : Uint =
  applyUint (divT0, x, y)

op /_ulong
   (x:Ulong, y:Ulong | y ~= ulongOfMathInt 0) infixl 111 : Ulong =
  applyUlong (divT0, x, y)

op /_ullong
   (x:Ullong, y:Ullong | y ~= ullongOfMathInt 0) infixl 111 : Ullong =
  applyUllong (divT0, x, y)

% operator %

op //_sint
   (x:Sint, y:Sint | fitsSint? (modT0, x, y) && y ~= sintOfMathInt 0)
   infixl 111 : Sint =
  applySint (modT0, x, y)

op //_slong
   (x:Slong, y:Slong | fitsSlong? (modT0, x, y) && y ~= slongOfMathInt 0)
   infixl 111 : Slong =
  applySlong (modT0, x, y)

op //_sllong
   (x:Sllong, y:Sllong | fitsSllong? (modT0, x, y) && y ~= sllongOfMathInt 0)
   infixl 111 : Sllong =
  applySllong (modT0, x, y)

op //_uint
   (x:Uint, y:Uint | y ~= uintOfMathInt 0) infixl 111 : Uint =
  applyUint (modT0, x, y)

op //_ulong
   (x:Ulong, y:Ulong | y ~= ulongOfMathInt 0) infixl 111 : Ulong =
  applyUlong (modT0, x, y)

op //_ullong
   (x:Ullong, y:Ullong | y ~= ullongOfMathInt 0) infixl 111 : Ullong =
  applyUllong (modT0, x, y)

% operator +

op +_sint
   (x:Sint, y:Sint | fitsSint? ((+), x, y)) infixl 110 : Sint =
  applySint ((+), x, y)

op +_slong
   (x:Slong, y:Slong | fitsSlong? ((+), x, y)) infixl 110 : Slong =
  applySlong ((+), x, y)

op +_sllong
   (x:Sllong, y:Sllong | fitsSllong? ((+), x, y)) infixl 110 : Sllong =
  applySllong ((+), x, y)

op +_uint (x:Uint, y:Uint) infixl 110 : Uint =
  applyUint ((+), x, y)

op +_ulong (x:Ulong, y:Ulong) infixl 110 : Ulong =
  applyUlong ((+), x, y)

op +_ullong (x:Ullong, y:Ullong) infixl 110 : Ullong =
  applyUllong ((+), x, y)

% operator -

op -_sint
   (x:Sint, y:Sint | fitsSint? ((-), x, y)) infixl 110 : Sint =
  applySint ((-), x, y)

op -_slong
   (x:Slong, y:Slong | fitsSlong? ((-), x, y)) infixl 110 : Slong =
  applySlong ((-), x, y)

op -_sllong
   (x:Sllong, y:Sllong | fitsSllong? ((-), x, y)) infixl 110 : Sllong =
  applySllong ((-), x, y)

op -_uint (x:Uint, y:Uint) infixl 110 : Uint =
  applyUint ((-), x, y)

op -_ulong (x:Ulong, y:Ulong) infixl 110 : Ulong =
  applyUlong ((-), x, y)

op -_ullong (x:Ullong, y:Ullong) infixl 110 : Ullong =
  applyUllong ((-), x, y)

(* The binary << operator requires integer operands [ISO 6.5.7/2], promotes
them, and left-shifts the first operand E1 by the number of positions E2
indicated by the second operand, filling the vacated bits with 0 [ISO
6.5.7/4]. If E2 is negative or greater than or equal to the size of E1, the
behavior is undefined [ISO 6.5.7/3].

If E1 is unsigned, the result of the left-shift is E1 * 2^E2 modulo MAX+1 (where
MAX is the maximum integer representable in E1's type) [ISO 6.5.7/4].

If E1 is signed, there are two cases: (i) if E1 is non-negative and E1 * 2^E2 is
representable in E1's type, that is the resulting value; (ii) otherwise (i.e. E1
is negative or E1 * 2^E2 is not representable), the behavior is undefined [ISO
6.5.7/4].

Since the two operands are promoted, we only need to define ops for sint/uint
and integer types of higher rank. The C code generator should not generate casts
for conversion ops that carry out the needed promotions. Since the two operands
are promoted independently (as opposed to the usual arithmetic conversion on
other binary operators, which bring both operands to a common type), we need to
define ops that correspond to all possible combinations of operand types. The
ops are only defined when the result of << is well defined. *)

% 1st operand sint:

op <<_sint_sint
   (x:Sint, y:Sint | let (x',y') = (mathIntOfSint x, mathIntOfSint y) in
                     0 <= y' && y' < int_bits &&
                     x' >= 0 && x' * 2**y' in? rangeOfSint)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x * 2**(mathIntOfSint y))

op <<_sint_slong
   (x:Sint, y:Slong | let (x',y') = (mathIntOfSint x, mathIntOfSlong y) in
                      0 <= y' && y' < int_bits &&
                      x' >= 0 && x' * 2**y' in? rangeOfSint)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x * 2**(mathIntOfSlong y))

op <<_sint_sllong
   (x:Sint, y:Sllong | let (x',y') = (mathIntOfSint x, mathIntOfSllong y) in
                       0 <= y' && y' < int_bits &&
                       x' >= 0 && x' * 2**y' in? rangeOfSint)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x * 2**(mathIntOfSllong y))

op <<_sint_uint
   (x:Sint, y:Uint | let (x',y') = (mathIntOfSint x, mathIntOfUint y) in
                     y' < int_bits &&
                     x' >= 0 && x' * 2**y' in? rangeOfSint)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x * 2**(mathIntOfUint y))

op <<_sint_ulong
   (x:Sint, y:Ulong | let (x',y') = (mathIntOfSint x, mathIntOfUlong y) in
                      y' < int_bits &&
                      x' >= 0 && x' * 2**y' in? rangeOfSint)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x * 2**(mathIntOfUlong y))

op <<_sint_ullong
   (x:Sint, y:Ullong | let (x',y') = (mathIntOfSint x, mathIntOfUllong y) in
                       y' < int_bits &&
                       x' >= 0 && x' * 2**y' in? rangeOfSint)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x * 2**(mathIntOfUllong y))

% 1st operand slong:

op <<_slong_sint
   (x:Slong, y:Sint | let (x',y') = (mathIntOfSlong x, mathIntOfSint y) in
                      0 <= y' && y' < long_bits &&
                      x' >= 0 && x' * 2**y' in? rangeOfSlong)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x * 2**(mathIntOfSint y))

op <<_slong_slong
   (x:Slong, y:Slong | let (x',y') = (mathIntOfSlong x, mathIntOfSlong y) in
                       0 <= y' && y' < long_bits &&
                       x' >= 0 && x' * 2**y' in? rangeOfSlong)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x * 2**(mathIntOfSlong y))

op <<_slong_sllong
   (x:Slong, y:Sllong | let (x',y') = (mathIntOfSlong x, mathIntOfSllong y) in
                        0 <= y' && y' < long_bits &&
                        x' >= 0 && x' * 2**y' in? rangeOfSlong)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x * 2**(mathIntOfSllong y))

op <<_slong_uint
   (x:Slong, y:Uint | let (x',y') = (mathIntOfSlong x, mathIntOfUint y) in
                      y' < long_bits &&
                      x' >= 0 && x' * 2**y' in? rangeOfSlong)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x * 2**(mathIntOfUint y))

op <<_slong_ulong
   (x:Slong, y:Ulong | let (x',y') = (mathIntOfSlong x, mathIntOfUlong y) in
                       y' < long_bits &&
                       x' >= 0 && x' * 2**y' in? rangeOfSlong)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x * 2**(mathIntOfUlong y))

op <<_slong_ullong
   (x:Slong, y:Ullong | let (x',y') = (mathIntOfSlong x, mathIntOfUllong y) in
                        y' < long_bits &&
                        x' >= 0 && x' * 2**y' in? rangeOfSlong)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x * 2**(mathIntOfUllong y))

% 1st operand sllong:

op <<_sllong_sint
   (x:Sllong, y:Sint | let (x',y') = (mathIntOfSllong x, mathIntOfSint y) in
                       0 <= y' && y' < llong_bits &&
                       x' >= 0 && x' * 2**y' in? rangeOfSllong)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x * 2**(mathIntOfSint y))

op <<_sllong_slong
   (x:Sllong, y:Slong | let (x',y') = (mathIntOfSllong x, mathIntOfSlong y) in
                        0 <= y' && y' < llong_bits &&
                        x' >= 0 && x' * 2**y' in? rangeOfSllong)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x * 2**(mathIntOfSlong y))

op <<_sllong_sllong
   (x:Sllong, y:Sllong | let (x',y') = (mathIntOfSllong x, mathIntOfSllong y) in
                         0 <= y' && y' < llong_bits &&
                         x' >= 0 && x' * 2**y' in? rangeOfSllong)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x * 2**(mathIntOfSllong y))

op <<_sllong_uint
   (x:Sllong, y:Uint | let (x',y') = (mathIntOfSllong x, mathIntOfUint y) in
                       y' < llong_bits &&
                       x' >= 0 && x' * 2**y' in? rangeOfSllong)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x * 2**(mathIntOfUint y))

op <<_sllong_ulong
   (x:Sllong, y:Ulong | let (x',y') = (mathIntOfSllong x, mathIntOfUlong y) in
                        y' < llong_bits &&
                        x' >= 0 && x' * 2**y' in? rangeOfSllong)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x * 2**(mathIntOfUlong y))

op <<_sllong_ullong
   (x:Sllong, y:Ullong | let (x',y') = (mathIntOfSllong x, mathIntOfUllong y) in
                         y' < llong_bits &&
                         x' >= 0 && x' * 2**y' in? rangeOfSllong)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x * 2**(mathIntOfUllong y))

% 1st operand uint:

op <<_uint_sint
   (x:Uint, y:Sint | 0 <= mathIntOfSint y && mathIntOfSint y < int_bits)
   infixl 109 : Uint =
  uintOfMathInt ((mathIntOfUint x * 2**(mathIntOfSint y)) modF (1 + UINT_MAX))

op <<_uint_slong
   (x:Uint, y:Slong | 0 <= mathIntOfSlong y && mathIntOfSlong y < int_bits)
   infixl 109 : Uint =
  uintOfMathInt ((mathIntOfUint x * 2**(mathIntOfSlong y)) modF (1 + UINT_MAX))

op <<_uint_sllong
   (x:Uint, y:Sllong | 0 <= mathIntOfSllong y && mathIntOfSllong y < int_bits)
   infixl 109 : Uint =
  uintOfMathInt ((mathIntOfUint x * 2**(mathIntOfSllong y)) modF (1 + UINT_MAX))

op <<_uint_uint
   (x:Uint, y:Uint | mathIntOfUint y < int_bits) infixl 109 : Uint =
  uintOfMathInt ((mathIntOfUint x * 2**(mathIntOfUint y)) modF (1 + UINT_MAX))

op <<_uint_ulong
   (x:Uint, y:Ulong | mathIntOfUlong y < int_bits) infixl 109 : Uint =
  uintOfMathInt ((mathIntOfUint x * 2**(mathIntOfUlong y)) modF (1 + UINT_MAX))

op <<_uint_ullong
   (x:Uint, y:Ullong | mathIntOfUllong y < int_bits) infixl 109 : Uint =
  uintOfMathInt ((mathIntOfUint x * 2**(mathIntOfUllong y)) modF (1 + UINT_MAX))

% 1st operand ulong:

op <<_ulong_sint
   (x:Ulong, y:Sint | 0 <= mathIntOfSint y && mathIntOfSint y < long_bits)
   infixl 109 : Ulong =
  ulongOfMathInt
    ((mathIntOfUlong x * 2**(mathIntOfSint y)) modF (1 + ULONG_MAX))

op <<_ulong_slong
   (x:Ulong, y:Slong | 0 <= mathIntOfSlong y && mathIntOfSlong y < long_bits)
   infixl 109 : Ulong =
  ulongOfMathInt
    ((mathIntOfUlong x * 2**(mathIntOfSlong y)) modF (1 + ULONG_MAX))

op <<_ulong_sllong
   (x:Ulong, y:Sllong | 0 <= mathIntOfSllong y && mathIntOfSllong y < long_bits)
   infixl 109 : Ulong =
  ulongOfMathInt
    ((mathIntOfUlong x * 2**(mathIntOfSllong y)) modF (1 + ULONG_MAX))

op <<_ulong_uint
   (x:Ulong, y:Uint | mathIntOfUint y < long_bits) infixl 109 : Ulong =
  ulongOfMathInt
    ((mathIntOfUlong x * 2**(mathIntOfUint y)) modF (1 + ULONG_MAX))

op <<_ulong_ulong
   (x:Ulong, y:Ulong | mathIntOfUlong y < long_bits) infixl 109 : Ulong =
  ulongOfMathInt
    ((mathIntOfUlong x * 2**(mathIntOfUlong y)) modF (1 + ULONG_MAX))

op <<_ulong_ullong
   (x:Ulong, y:Ullong | mathIntOfUllong y < long_bits) infixl 109 : Ulong =
  ulongOfMathInt
    ((mathIntOfUlong x * 2**(mathIntOfUllong y)) modF (1 + ULONG_MAX))

% 1st operand ullong:

op <<_ullong_sint
   (x:Ullong, y:Sint |
    0 <= mathIntOfSint y && mathIntOfSint y < llong_bits)
   infixl 109 : Ullong =
  ullongOfMathInt
    ((mathIntOfUllong x * 2**(mathIntOfSint y)) modF (1 + ULLONG_MAX))

op <<_ullong_slong
   (x:Ullong, y:Slong |
    0 <= mathIntOfSlong y && mathIntOfSlong y < llong_bits)
   infixl 109 : Ullong =
  ullongOfMathInt
    ((mathIntOfUllong x * 2**(mathIntOfSlong y)) modF (1 + ULLONG_MAX))

op <<_ullong_sllong
   (x:Ullong, y:Sllong |
    0 <= mathIntOfSllong y && mathIntOfSllong y < llong_bits)
   infixl 109 : Ullong =
  ullongOfMathInt
    ((mathIntOfUllong x * 2**(mathIntOfSllong y)) modF (1 + ULLONG_MAX))

op <<_ullong_uint
   (x:Ullong, y:Uint | mathIntOfUint y < llong_bits) infixl 109 : Ullong =
  ullongOfMathInt
    ((mathIntOfUllong x * 2**(mathIntOfUint y)) modF (1 + ULLONG_MAX))

op <<_ullong_ulong
   (x:Ullong, y:Ulong | mathIntOfUlong y < llong_bits) infixl 109 : Ullong =
  ullongOfMathInt
    ((mathIntOfUllong x * 2**(mathIntOfUlong y)) modF (1 + ULLONG_MAX))

op <<_ullong_ullong
   (x:Ullong, y:Ullong | mathIntOfUllong y < llong_bits) infixl 109 : Ullong =
  ullongOfMathInt
    ((mathIntOfUllong x * 2**(mathIntOfUllong y)) modF (1 + ULLONG_MAX))

(* The binary >> operator requires integer operands [ISO 6.5.7/2], promotes
them, and right-shifts the first operand E1 by the number of positions E2
indicated by the second operand [ISO 6.5.7/5]. If E2 is negative or greater than
or equal to the size of E1, the behavior is undefined [ISO 6.5.7/3].

If E1 is unsigned, or if it signed and non-negative, the result is the integral
part of the quotient E1 / 2^E2 [ISO 6.5.7/5]. Otherwise, the result is
implementation-dependent [ISO 6.5.7/5].

Since the two operands are promoted, we only need to define ops for sint/uint
and integer types of higher rank. The C code generator should not generate casts
for conversion ops that carry out the needed promotions. Since the two operands
are promoted independently (as opposed to the usual arithmetic conversion on
other binary operators, which bring both operands to a common type), we need to
define ops that correspond to all possible combinations of operand types. The
ops are only defined when the result of >> is well defined. *)

% 1st operand sint:

op >>_sint_sint
   (x:Sint, y:Sint | 0 <= mathIntOfSint y && mathIntOfSint y < int_bits &&
                     mathIntOfSint x >= 0)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x divT 2**(mathIntOfSint y))

op >>_sint_slong
   (x:Sint, y:Slong | 0 <= mathIntOfSlong y && mathIntOfSlong y < int_bits &&
                      mathIntOfSint x >= 0)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x divT 2**(mathIntOfSlong y))

op >>_sint_sllong
   (x:Sint, y:Sllong | 0 <= mathIntOfSllong y && mathIntOfSllong y < int_bits &&
                       mathIntOfSint x >= 0)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x divT 2**(mathIntOfSllong y))

op >>_sint_uint
   (x:Sint, y:Uint | mathIntOfUint y < int_bits && mathIntOfSint x >= 0)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x divT 2**(mathIntOfUint y))

op >>_sint_ulong
   (x:Sint, y:Ulong | mathIntOfUlong y < int_bits && mathIntOfSint x >= 0)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x divT 2**(mathIntOfUlong y))

op >>_sint_ullong
   (x:Sint, y:Ullong | mathIntOfUllong y < int_bits && mathIntOfSint x >= 0)
   infixl 109 : Sint =
  sintOfMathInt (mathIntOfSint x divT 2**(mathIntOfUllong y))

% 1st operand slong:

op >>_slong_sint
   (x:Slong, y:Sint | 0 <= mathIntOfSint y && mathIntOfSint y < long_bits
                   && mathIntOfSlong x >= 0)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x divT 2**(mathIntOfSint y))

op >>_slong_slong
   (x:Slong, y:Slong | 0 <= mathIntOfSlong y && mathIntOfSlong y < long_bits
                    && mathIntOfSlong x >= 0)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x divT 2**(mathIntOfSlong y))

op >>_slong_sllong
   (x:Slong, y:Sllong | 0 <= mathIntOfSllong y && mathIntOfSllong y < long_bits
                     && mathIntOfSlong x >= 0)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x divT 2**(mathIntOfSllong y))

op >>_slong_uint
   (x:Slong, y:Uint | mathIntOfUint y < long_bits && mathIntOfSlong x >= 0)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x divT 2**(mathIntOfUint y))

op >>_slong_ulong
   (x:Slong, y:Ulong | mathIntOfUlong y < long_bits && mathIntOfSlong x >= 0)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x divT 2**(mathIntOfUlong y))

op >>_slong_ullong
   (x:Slong, y:Ullong | mathIntOfUllong y < long_bits && mathIntOfSlong x >= 0)
   infixl 109 : Slong =
  slongOfMathInt (mathIntOfSlong x divT 2**(mathIntOfUllong y))

% 1st operand sllong:

op >>_sllong_sint
   (x:Sllong, y:Sint |
    0 <= mathIntOfSint y && mathIntOfSint y < llong_bits &&
    mathIntOfSllong x >= 0)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x divT 2**(mathIntOfSint y))

op >>_sllong_slong
   (x:Sllong, y:Slong |
    0 <= mathIntOfSlong y && mathIntOfSlong y < llong_bits &&
    mathIntOfSllong x >= 0)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x divT 2**(mathIntOfSlong y))

op >>_sllong_sllong
   (x:Sllong, y:Sllong |
    0 <= mathIntOfSllong y && mathIntOfSllong y < llong_bits &&
    mathIntOfSllong x >= 0)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x divT 2**(mathIntOfSllong y))

op >>_sllong_uint
   (x:Sllong, y:Uint |
    mathIntOfUint y < llong_bits && mathIntOfSllong x >= 0)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x divT 2**(mathIntOfUint y))

op >>_sllong_ulong
   (x:Sllong, y:Ulong |
    mathIntOfUlong y < llong_bits && mathIntOfSllong x >= 0)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x divT 2**(mathIntOfUlong y))

op >>_sllong_ullong
   (x:Sllong, y:Ullong |
    mathIntOfUllong y < llong_bits && mathIntOfSllong x >= 0)
   infixl 109 : Sllong =
  sllongOfMathInt (mathIntOfSllong x divT 2**(mathIntOfUllong y))

% 1st operand uint:

op >>_uint_sint
   (x:Uint, y:Sint | 0 <= mathIntOfSint y && mathIntOfSint y < int_bits)
   infixl 109 : Uint =
  uintOfMathInt (mathIntOfUint x divT 2**(mathIntOfSint y))

op >>_uint_slong
   (x:Uint, y:Slong | 0 <= mathIntOfSlong y && mathIntOfSlong y < int_bits)
   infixl 109 : Uint =
  uintOfMathInt (mathIntOfUint x divT 2**(mathIntOfSlong y))

op >>_uint_sllong
   (x:Uint, y:Sllong | 0 <= mathIntOfSllong y && mathIntOfSllong y < int_bits)
   infixl 109 : Uint =
  uintOfMathInt (mathIntOfUint x divT 2**(mathIntOfSllong y))

op >>_uint_uint
   (x:Uint, y:Uint | mathIntOfUint y < int_bits) infixl 109 : Uint =
  uintOfMathInt (mathIntOfUint x divT 2**(mathIntOfUint y))

op >>_uint_ulong
   (x:Uint, y:Ulong | mathIntOfUlong y < int_bits) infixl 109 : Uint =
  uintOfMathInt (mathIntOfUint x divT 2**(mathIntOfUlong y))

op >>_uint_ullong
   (x:Uint, y:Ullong | mathIntOfUllong y < int_bits) infixl 109 : Uint =
  uintOfMathInt (mathIntOfUint x divT 2**(mathIntOfUllong y))

% 1st operand ulong:

op >>_ulong_sint
   (x:Ulong, y:Sint | 0 <= mathIntOfSint y && mathIntOfSint y < long_bits)
   infixl 109 : Ulong =
  ulongOfMathInt (mathIntOfUlong x divT 2**(mathIntOfSint y))

op >>_ulong_slong
   (x:Ulong, y:Slong | 0 <= mathIntOfSlong y && mathIntOfSlong y < long_bits)
   infixl 109 : Ulong =
  ulongOfMathInt (mathIntOfUlong x divT 2**(mathIntOfSlong y))

op >>_ulong_sllong
   (x:Ulong, y:Sllong | 0 <= mathIntOfSllong y && mathIntOfSllong y < long_bits)
   infixl 109 : Ulong =
  ulongOfMathInt (mathIntOfUlong x divT 2**(mathIntOfSllong y))

op >>_ulong_uint
   (x:Ulong, y:Uint | mathIntOfUint y < long_bits) infixl 109 : Ulong =
  ulongOfMathInt (mathIntOfUlong x divT 2**(mathIntOfUint y))

op >>_ulong_ulong
   (x:Ulong, y:Ulong | mathIntOfUlong y < long_bits) infixl 109 : Ulong =
  ulongOfMathInt (mathIntOfUlong x divT 2**(mathIntOfUlong y))

op >>_ulong_ullong
   (x:Ulong, y:Ullong | mathIntOfUllong y < long_bits) infixl 109 : Ulong =
  ulongOfMathInt (mathIntOfUlong x divT 2**(mathIntOfUllong y))

% 1st operand ullong:

op >>_ullong_sint
   (x:Ullong, y:Sint |
    0 <= mathIntOfSint y && mathIntOfSint y < llong_bits)
   infixl 109 : Ullong =
  ullongOfMathInt (mathIntOfUllong x divT 2**(mathIntOfSint y))

op >>_ullong_slong
   (x:Ullong, y:Slong |
    0 <= mathIntOfSlong y && mathIntOfSlong y < llong_bits)
   infixl 109 : Ullong =
  ullongOfMathInt (mathIntOfUllong x divT 2**(mathIntOfSlong y))

op >>_ullong_sllong
   (x:Ullong, y:Sllong |
    0 <= mathIntOfSllong y && mathIntOfSllong y < llong_bits)
   infixl 109 : Ullong =
  ullongOfMathInt (mathIntOfUllong x divT 2**(mathIntOfSllong y))

op >>_ullong_uint
   (x:Ullong, y:Uint | mathIntOfUint y < llong_bits) infixl 109 : Ullong =
  ullongOfMathInt (mathIntOfUllong x divT 2**(mathIntOfUint y))

op >>_ullong_ulong
   (x:Ullong, y:Ulong | mathIntOfUlong y < llong_bits) infixl 109 : Ullong =
  ullongOfMathInt (mathIntOfUllong x divT 2**(mathIntOfUlong y))

op >>_ullong_ullong
   (x:Ullong, y:Ullong | mathIntOfUllong y < llong_bits) infixl 109 : Ullong =
  ullongOfMathInt (mathIntOfUllong x divT 2**(mathIntOfUllong y))

(* The binary <, >, <=, >=, ==, and != operators perform the usual arithmetic
conversions [ISO 6.5.8/3], and return the signed int 1 or 0 depending on whether
the comparison is true or false [ISO 6.5.8/6].

Since the operands are subjected to the usual arithmetic conversions, we only
need to define ops for for sint/uint and integer types of higher rank. The C
code generator should not generate casts for conversion ops that carry out the
needed usual arithmetic conversions.

There are 36 ops (6 operators times 6 integer types). We factor commonalities of
(subsets of) the 36 ops into a few parameterized ops that are suitably
instantiated to define the 36 ops. A key parameter is the comparison operation
on integers carried out by each of the 6 operators. *)

type CompOp = Int * Int -> Bool

(* Given a comparison operation and two signed or unsigned integers of the same
type, we can return the result of comparing them. *)

op compSint (cop:CompOp, x:Sint, y:Sint) : Sint =
  let (x',y') = (mathIntOfSint x, mathIntOfSint y) in
  if cop (x', y') then sint1 else sint0

op compSlong (cop:CompOp, x:Slong, y:Slong) : Sint =
  let (x',y') = (mathIntOfSlong x, mathIntOfSlong y) in
  if cop (x', y') then sint1 else sint0

op compSllong (cop:CompOp, x:Sllong, y:Sllong) : Sint =
  let (x',y') = (mathIntOfSllong x, mathIntOfSllong y) in
  if cop (x', y') then sint1 else sint0

op compUint (cop:CompOp, x:Uint, y:Uint) : Sint =
  let (x',y') = (mathIntOfUint x, mathIntOfUint y) in
  if cop (x', y') then sint1 else sint0

op compUlong (cop:CompOp, x:Ulong, y:Ulong) : Sint =
  let (x',y') = (mathIntOfUlong x, mathIntOfUlong y) in
  if cop (x', y') then sint1 else sint0

op compUllong (cop:CompOp, x:Ullong, y:Ullong) : Sint =
  let (x',y') = (mathIntOfUllong x, mathIntOfUllong y) in
  if cop (x', y') then sint1 else sint0

(* With the above generic ops in hand, we can define the 36 ops for the 6
operators for each of the 6 integer types. *)

op <_sint   (x:Sint,   y:Sint  ) infixl 108 : Sint = compSint   ((<), x, y)
op <_slong  (x:Slong,  y:Slong ) infixl 108 : Sint = compSlong  ((<), x, y)
op <_sllong (x:Sllong, y:Sllong) infixl 108 : Sint = compSllong ((<), x, y)
op <_uint   (x:Uint,   y:Uint  ) infixl 108 : Sint = compUint   ((<), x, y)
op <_ulong  (x:Ulong,  y:Ulong ) infixl 108 : Sint = compUlong  ((<), x, y)
op <_ullong (x:Ullong, y:Ullong) infixl 108 : Sint = compUllong ((<), x, y)

op >_sint   (x:Sint,   y:Sint  ) infixl 108 : Sint = compSint   ((>), x, y)
op >_slong  (x:Slong,  y:Slong ) infixl 108 : Sint = compSlong  ((>), x, y)
op >_sllong (x:Sllong, y:Sllong) infixl 108 : Sint = compSllong ((>), x, y)
op >_uint   (x:Uint,   y:Uint  ) infixl 108 : Sint = compUint   ((>), x, y)
op >_ulong  (x:Ulong,  y:Ulong ) infixl 108 : Sint = compUlong  ((>), x, y)
op >_ullong (x:Ullong, y:Ullong) infixl 108 : Sint = compUllong ((>), x, y)

op <=_sint   (x:Sint,   y:Sint  ) infixl 108 : Sint = compSint   ((<=), x, y)
op <=_slong  (x:Slong,  y:Slong ) infixl 108 : Sint = compSlong  ((<=), x, y)
op <=_sllong (x:Sllong, y:Sllong) infixl 108 : Sint = compSllong ((<=), x, y)
op <=_uint   (x:Uint,   y:Uint  ) infixl 108 : Sint = compUint   ((<=), x, y)
op <=_ulong  (x:Ulong,  y:Ulong ) infixl 108 : Sint = compUlong  ((<=), x, y)
op <=_ullong (x:Ullong, y:Ullong) infixl 108 : Sint = compUllong ((<=), x, y)

op >=_sint   (x:Sint,   y:Sint  ) infixl 108 : Sint = compSint   ((>=), x, y)
op >=_slong  (x:Slong,  y:Slong ) infixl 108 : Sint = compSlong  ((>=), x, y)
op >=_sllong (x:Sllong, y:Sllong) infixl 108 : Sint = compSllong ((>=), x, y)
op >=_uint   (x:Uint,   y:Uint  ) infixl 108 : Sint = compUint   ((>=), x, y)
op >=_ulong  (x:Ulong,  y:Ulong ) infixl 108 : Sint = compUlong  ((>=), x, y)
op >=_ullong (x:Ullong, y:Ullong) infixl 108 : Sint = compUllong ((>=), x, y)

op ==_sint   (x:Sint,   y:Sint  ) infixl 107 : Sint = compSint   ((=), x, y)
op ==_slong  (x:Slong,  y:Slong ) infixl 107 : Sint = compSlong  ((=), x, y)
op ==_sllong (x:Sllong, y:Sllong) infixl 107 : Sint = compSllong ((=), x, y)
op ==_uint   (x:Uint,   y:Uint  ) infixl 107 : Sint = compUint   ((=), x, y)
op ==_ulong  (x:Ulong,  y:Ulong ) infixl 107 : Sint = compUlong  ((=), x, y)
op ==_ullong (x:Ullong, y:Ullong) infixl 107 : Sint = compUllong ((=), x, y)

op !=_sint   (x:Sint,   y:Sint  ) infixl 107 : Sint = compSint   ((~=), x, y)
op !=_slong  (x:Slong,  y:Slong ) infixl 107 : Sint = compSlong  ((~=), x, y)
op !=_sllong (x:Sllong, y:Sllong) infixl 107 : Sint = compSllong ((~=), x, y)
op !=_uint   (x:Uint,   y:Uint  ) infixl 107 : Sint = compUint   ((~=), x, y)
op !=_ulong  (x:Ulong,  y:Ulong ) infixl 107 : Sint = compUlong  ((~=), x, y)
op !=_ullong (x:Ullong, y:Ullong) infixl 107 : Sint = compUllong ((~=), x, y)

(* The binary &, ^, and | operators require integer operands [ISO 6.5.10/2,
6.5.11/2, 6.5.12/2], perform the usual arithmetic conversions [ISO 6.5.10/3,
6.5.11/3, 6.5.12/3], and return the bitwise AND [ISO 6.5.10/4], exclusive OR
[ISO 6.5.11/4], and inclusive OR [ISO 6.5.12/4] of their operands.

Since the operands are subjected to the usual arithmetic conversions, we only
need to define ops for for sint/uint and integer types of higher rank. The C
code generator should not generate casts for conversion ops that carry out the
needed usual arithmetic conversions. *)

op &_sint (sint bs1 : Sint, sint bs2 : Sint) : Sint =
  sint (bs1 and bs2)

op &_slong (slong bs1 : Slong, slong bs2 : Slong) : Slong =
  slong (bs1 and bs2)

op &_sllong (sllong bs1 : Sllong, sllong bs2 : Sllong) : Sllong =
  sllong (bs1 and bs2)

op &_uint (uint bs1 : Uint, uint bs2 : Uint) : Uint =
  uint (bs1 and bs2)

op &_ulong (ulong bs1 : Ulong, ulong bs2 : Ulong) : Ulong =
  ulong (bs1 and bs2)

op &_ullong (ullong bs1 : Ullong, ullong bs2 : Ullong) : Ullong =
  ullong (bs1 and bs2)

op ^_sint (sint bs1 : Sint, sint bs2 : Sint) : Sint =
  sint (bs1 xor bs2)

op ^_slong (slong bs1 : Slong, slong bs2 : Slong) : Slong =
  slong (bs1 xor bs2)

op ^_sllong (sllong bs1 : Sllong, sllong bs2 : Sllong) : Sllong =
  sllong (bs1 xor bs2)

op ^_uint (uint bs1 : Uint, uint bs2 : Uint) : Uint =
  uint (bs1 xor bs2)

op ^_ulong (ulong bs1 : Ulong, ulong bs2 : Ulong) : Ulong =
  ulong (bs1 xor bs2)

op ^_ullong (ullong bs1 : Ullong, ullong bs2 : Ullong) : Ullong =
  ullong (bs1 xor bs2)

op |_sint (sint bs1 : Sint, sint bs2 : Sint) : Sint =
  sint (bs1 ior bs2)

op |_slong (slong bs1 : Slong, slong bs2 : Slong) : Slong =
  slong (bs1 ior bs2)

op |_sllong (sllong bs1 : Sllong, sllong bs2 : Sllong) : Sllong =
  sllong (bs1 ior bs2)

op |_uint (uint bs1 : Uint, uint bs2 : Uint) : Uint =
  uint (bs1 ior bs2)

op |_ulong (ulong bs1 : Ulong, ulong bs2 : Ulong) : Ulong =
  ulong (bs1 ior bs2)

op |_ullong (ullong bs1 : Ullong, ullong bs2 : Ullong) : Ullong =
  ullong (bs1 ior bs2)

(* The binary && and || operators [ISO 6.5.13, 6.5.14] are non-strict: the first
operand is evaluated first, and the second operand is evaluated only if the
first one is not sufficient to determine the result. Thus, these two operators
correspond to Metaslang's built-in && and || constructs. *)


%subsection (* Array operators *)

(* The array subscript operator in C [ISO 6.5.2.1] takes any integer value as
the subscript argument. We define an op for each integer type. These ops are
defined only if the index is in range of the array. *)

op [a] @_char (array elems : Array a, i:Char |
               0 <= mathIntOfChar i && mathIntOfChar i < length elems)
              infixl 30 : a =
  elems @ mathIntOfChar i

op [a] @_schar (array elems : Array a, i:Schar |
                0 <= mathIntOfSchar i && mathIntOfSchar i < length elems)
               infixl 30 : a =
  elems @ mathIntOfSchar i

op [a] @_uchar (array elems : Array a, i:Uchar |
                0 <= mathIntOfUchar i && mathIntOfUchar i < length elems)
               infixl 30 : a =
  elems @ mathIntOfUchar i

op [a] @_sshort (array elems : Array a, i:Sshort |
                 0 <= mathIntOfSshort i && mathIntOfSshort i < length elems)
                infixl 30 : a =
  elems @ mathIntOfSshort i

op [a] @_ushort (array elems : Array a, i:Ushort |
                 0 <= mathIntOfUshort i && mathIntOfUshort i < length elems)
                infixl 30 : a =
  elems @ mathIntOfUshort i

op [a] @_sint (array elems : Array a, i:Sint |
               0 <= mathIntOfSint i && mathIntOfSint i < length elems)
              infixl 30 : a =
  elems @ mathIntOfSint i

op [a] @_uint (array elems : Array a, i:Uint |
               0 <= mathIntOfUint i && mathIntOfUint i < length elems)
              infixl 30 : a =
  elems @ mathIntOfUint i

op [a] @_slong (array elems : Array a, i:Slong |
                0 <= mathIntOfSlong i && mathIntOfSlong i < length elems)
               infixl 30 : a =
  elems @ mathIntOfSlong i

op [a] @_ulong (array elems : Array a, i:Ulong |
                0 <= mathIntOfUlong i && mathIntOfUlong i < length elems)
               infixl 30 : a =
  elems @ mathIntOfUlong i

op [a] @_sllong (array elems : Array a, i:Sllong |
                 0 <= mathIntOfSllong i && mathIntOfSllong i < length elems)
                infixl 30 : a =
  elems @ mathIntOfSllong i

op [a] @_ullong (array elems : Array a, i:Ullong |
                 0 <= mathIntOfUllong i && mathIntOfUllong i < length elems)
                infixl 30 : a =
  elems @ mathIntOfUllong i


%subsection (* Structure operators *)

(* Given the correspondence between Metaslang records and C structures described
earlier, field selections in Metaslang correspond exactly to structure member
expressions (i.e. "." operator) in C. *)


%section (* Function definitions *)

(* A Metaslang function of type T1 * ... * Tn -> T, where n >= 0 and the Ti's
and T are all Metaslang types that correspond to C types, correspond to a C
function [ISO 6.7.5.3, 6.9.1] with the corresponding argument and result
types. The Metaslang function must have explicit argument names and its body
must only use Metaslang operators (defined above) that correspond to C
operators. The body of the corresponding C function consists of a "return"
followed by the C expression that corresponds to the Metaslang function's body
expression.

For example, the Metaslang function

 op f (x:Sshort) : Slong = slongOfSint (-_1_sint (sintOfSshort x))

corresponds to the C function

 long f(short x) { return (-x); }

Note that the C code generator should not generate casts that correspond to the
conversion ops because the short is automatically promoted to an int by virtue
of the unary - operation, and the resulting int is automatically converted to
the return type of the function (a long) as if by assignment [ISO 6.8.6.4/3].
Generating the cast would be correct, but makes the code less readable. *)


endspec
