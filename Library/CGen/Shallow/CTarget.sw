(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

C qualifying spec

import CTargetParameters
import Library

%%todo why not simp add below?
proof isa -verbatim
declare List__ofLength_p_def [simp]
declare List__nonEmpty_p_def [simp]

declare List.length_map [simp add]

end-proof


%section (* Introduction *)

(* We formalize types and ops that may be useful to target C from Metaslang.
This spec captures C concepts (e.g. C types) that (1) can be targeted by
refinements and (2) can be mapped to corresponding C code by a suitable code
generator. This spec can be viewed as a shallow embedding of (a subset of) C
into Metaslang.

Our formalization is based on the ANSI C11 standard, ISO/IEC 9899, "Programming
languages - C", Third edition (2011-12-15). Note that the Second edition of
Brian Kernighan and Dennis Ritchie's "The C Programming Language", published in
1988, refers to an earlier version of the standard.

In the comments in this spec, we reference the ISO standard as '[ISO]', possibly
including (dotted) (sub)section numbers (e.g. '[ISO 6.5.9]') and paragraph
numbers separated by '/' (e.g. '[ISO 6.5.9/2]'). We use ',' to indicate multiple
sub-references (e.g. '[ISO 6.5.4/3, 5.2.1]') and we use '-' to indicate ranges
of contiguous sub-references (e.g.  '[ISO 6.5.4-6.5.6]' is the same as '[ISO
6.5.4, 6.5.5, 6.5.6]').

The comments in this spec are structured into sections and subsections,
following a literate programming style. Even though there are currently no tools
to process these structured comments (e.g. to produce PDF documents), the
structuring is valuable per se. The following formats are used for the
structured comments:

- each (sub)section starts with '%section', '%subsection', '%subsubsection',
  etc. (recall that '%' starts a line comment) in column 0, followed by a title
  between the Metaslang symbols for block comments (which we do not repeat here
  otherwise we would be closing this comment!);

- each paragraph of comments is part of a block comment in Metaslang, with each
  line starting at column 0 and the opening and closing symbols of the block
  comments in line with the text (i.e. not in separate lines);

- paragraphs and bullets are separeted by single blank lines;

- no comment line exceeds 80 columns;

- each new (sub)section is preceded by exactly two blank lines, unless it
  follows a higher (sub)section title (e.g. a section title immediately followed
  by a subsection title, with no text in the section and before the subsection),
  in which case it is preceded by exactly one blank line.

Formal Metaslang text (i.e. not comments) always starts at column 0 and never
exceeds 80 columns. Metaslang declarations are usually separated by single blank
lines (like paragraphs), or occasionally by no blank lines if they are closely
related and only one line long each. This and the previous comment formats
should be followed by anybody editing this file, to ensure uniformity, ease of
text search, no line wrapping if the spec is printed, and support for several
side-by-side editors without line wrapping. *)


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


%subsection (* The Unsigned Char Type *)

(* The number of bits that comprise a byte [ISO 3.6] is expressed by CHAR_BIT
[ISO 5.2.4.2.1/1], which must be at least 8. (Note that the notion of byte in C
may not coincide, although it often does, with the notion of byte in the
Specware library, which defines a byte to always consist of 8 bits. However,
given our definition of CHAR_BIT as 8, the two notions coincide.) *)

% In spec CTargetParameters:
%
% op CHAR_BIT : Nat

theorem min_CHAR_BIT is CHAR_BIT >= 8
proof isa [simp]
  by (auto)
end-proof

(* [ISO 5.2.4.2.1/2] constrains UCHAR_MAX [ISO 5.2.4.2.1/1] to be
2^CHAR_BIT-1. *)

op UCHAR_MAX : Nat = 2 ** CHAR_BIT - 1
proof isa [simp] end-proof

theorem min_UCHAR_MAX is UCHAR_MAX >= 255

(* [ISO 6.2.6.1/3] constrains unsigned chars to be represented using a pure
binary notation, i.e. to range from 0 to 2^CHAR_BIT-1. Thus, unsigned chars are
always bytes in C, and every non-bit-field value (of any type) consists of one
or more bytes [ISO 6.2.6.1/4]. This leads to the following type definition. We
"interpose" the uchar constructor between the list of CHAR_BIT bits and the
corresponding value of type Uchar in order to keep all the C types separate
(i.e. with no values in common) -- we use such constructors for the other C
types below. This may ease refinements, but experience will tell. *)

type Uchar = | uchar (Bits | ofLength? CHAR_BIT)

(* The bits that constitute an unsigned char can be interpreted in big endian or
little endian, to denote a "mathematical integer". Since a byte is always
addressed as a unit, the exact choice is unimportant. We choose big endian (as
implied by the use of toNat). *)

%%TODO restrict return type as we do for the other ops
op mathIntOfUchar (uchar bs : Uchar) : Nat = toNat bs

theorem mathIntOfUchar_injective is
  fa(x:Uchar, y:Uchar) (mathIntOfUchar x = mathIntOfUchar y) = (x = y)

theorem mathIntOfUchar_injective_fw is
  fa(x:Uchar, y:Uchar) (mathIntOfUchar x = mathIntOfUchar y) => (x = y)

op rangeOfUchar : FiniteSet Int = fn i:Int -> 0 <= i && i <= UCHAR_MAX

%% TODO must currently add an int around the element to get the Isabelle theorem to type-check
theorem uchar_range is fa(x:Uchar) ((mathIntOfUchar x):Int) in? rangeOfUchar

op ucharOfMathInt (i:Int | i in? rangeOfUchar) : Uchar =
  the(x:Uchar) mathIntOfUchar x = i

theorem mathIntOfUchar_ucharOfMathInt is
  fa(i:Int) i in? rangeOfUchar => mathIntOfUchar (ucharOfMathInt i) = i

%% helper lemma that moves the int on one side to be a nat on the other side
proof isa -verbatim
theorem C__mathIntOfUchar_ucharOfMathInt_2 [simp]: 
  "\<lbrakk>i \<in> C__rangeOfUchar\<rbrakk> \<Longrightarrow> 
   (C__mathIntOfUchar (C__ucharOfMathInt i)) = nat i"
  apply (cut_tac i=i in C__mathIntOfUchar_ucharOfMathInt)
  apply(auto simp del:C__mathIntOfUchar_ucharOfMathInt)
  done

theorem C__Uchar__subtype_pred_ucharOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfUchar\<rbrakk> \<Longrightarrow>
  C__Uchar__subtype_pred (C__ucharOfMathInt i)"
  apply(simp add: C__ucharOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Uchar) . (C__Uchar__subtype_pred x \<and> int (C__mathIntOfUchar x) = i)" in theI')
  apply(auto simp add:C__mathIntOfUchar_injective)
  apply(cut_tac i=i in C__ucharOfMathInt_Obligation_the)
  apply(auto)
  done
end-proof




theorem ucharOfMathInt_mathIntOfUchar is
  fa(x:Uchar) ucharOfMathInt (mathIntOfUchar x) = x


%subsection (* The Signed Char Type *)

(* The sizeof operator [ISO 6.5.3.4], which returns the size in bytes of its
operand [ISO 6.5.3.4/2], must return 1 when applied to a char, unsigned char, or
signed char [ISO 6.5.3.4/4]. This implies that signed chars consist of 1 byte,
like unsigned chars. *)

type Schar = | schar (Bits | ofLength? CHAR_BIT)

(* [ISO 6.2.6.2/2] says that a signed char must consist of a sign bit and value
bits. We assume that signed chars are represented as two's complement (vs. one's
complement, or sign & magnitude) -- these are two examples of parameters of the
C language that are implicitly defined by our formalization. As with unsigned
chars, we choose a big endian interpretation for signed chars.

The choice of a two's complement representation determines the value of
SCHAR_MIN and SCHAR_MAX [ISO 5.2.4.2.1/1] as a function of CHAR_BIT. *)

op mathIntOfSchar (schar bs : Schar) : Int = toInt bs

theorem mathIntOfSchar_injective is
  fa(x:Schar, y:Schar) (mathIntOfSchar x = mathIntOfSchar y) = (x = y)

theorem mathIntOfSchar_injective_fw is
  fa(x:Schar, y:Schar) (mathIntOfSchar x = mathIntOfSchar y) => (x = y)

op SCHAR_MIN : Int = - (2 ** (CHAR_BIT - 1))
proof isa [simp] end-proof

op SCHAR_MAX : Nat = 2 ** (CHAR_BIT - 1) - 1
proof isa [simp] end-proof

theorem max_SCHAR_MIN is SCHAR_MIN <= -127

theorem min_SCHAR_MAX is SCHAR_MAX >= 127

op rangeOfSchar : FiniteSet Int = fn i:Int -> SCHAR_MIN <= i && i <= SCHAR_MAX

theorem schar_range is fa(x:Schar) mathIntOfSchar x in? rangeOfSchar

op scharOfMathInt (i:Int | i in? rangeOfSchar) : Schar =
  the(x:Schar) mathIntOfSchar x = i

theorem mathIntOfSchar_scharOfMathInt is
  fa(i:Int) i in? rangeOfSchar => mathIntOfSchar (scharOfMathInt i) = i

proof isa -verbatim
theorem C__Schar__subtype_pred_scharOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfSchar\<rbrakk> \<Longrightarrow>
  C__Schar__subtype_pred (C__scharOfMathInt i)"
  apply(simp add: C__scharOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Schar) . (C__Schar__subtype_pred x \<and> (C__mathIntOfSchar x) = i)" in theI')
  apply(auto simp add:C__mathIntOfSchar_injective)
  apply(cut_tac i=i in C__scharOfMathInt_Obligation_the)
  apply(auto)
  done
end-proof

theorem scharOfMathInt_mathIntOfSchar is
  fa(x:Schar) scharOfMathInt (mathIntOfSchar x) = x


%subsection (* The Plain Char Type *)

(* Plain chars have the same range and representation as either signed chars or
unsigned chars [ISO 6.2.5/15]. Either way, plain chars consist of CHAR_BIT
bits. However, their range of value differs. CHAR_MIN and CHAR_MAX [ISO
5.2.4.2.1/1] are determined by CHAR_BIT and by the choice of whether plain chars
are signed or unsigned. *)

% In spec CTargetParameters:
%
% op plainCharsAreSigned : Bool

op plainCharsAreUnsigned : Bool = ~ plainCharsAreSigned

op CHAR_MIN : Int = if plainCharsAreSigned then SCHAR_MIN else 0
proof isa [simp] end-proof

op CHAR_MAX : Nat = if plainCharsAreSigned then SCHAR_MAX else UCHAR_MAX
proof isa [simp] end-proof

type Char = | char (Bits | ofLength? CHAR_BIT)

op mathIntOfChar (char bs : Char) : Int =
  if plainCharsAreSigned then toInt bs else toNat bs

theorem mathIntOfChar_injective is
  fa(x:Char, y:Char) (mathIntOfChar x = mathIntOfChar y) = (x = y)

theorem mathIntOfChar_injective_fw is
  fa(x:Char, y:Char) (mathIntOfChar x = mathIntOfChar y) => (x = y)

op rangeOfChar : FiniteSet Int = fn i:Int -> CHAR_MIN <= i && i <= CHAR_MAX

%%proof should apply regardless of whether chars are signed
theorem char_range is fa(x:Char) mathIntOfChar x in? rangeOfChar

op charOfMathInt (i:Int | i in? rangeOfChar) : Char =
  the(x:Char) mathIntOfChar x = i

theorem mathIntOfChar_charOfMathInt is
  fa(i:Int) i in? rangeOfChar => mathIntOfChar (charOfMathInt i) = i
proof isa [simp]
  apply (auto simp add:C__charOfMathInt_def)
  apply(cut_tac i=i in C__charOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Char) . (C__Char__subtype_pred x \<and> (C__mathIntOfChar x) = i)" in theI')
  apply(auto)
end-proof

proof isa -verbatim
theorem C__Char__subtype_pred_charOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfChar\<rbrakk> \<Longrightarrow>
  C__Char__subtype_pred (C__charOfMathInt i)"
  apply(simp add: C__charOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Char) . (C__Char__subtype_pred x \<and> (C__mathIntOfChar x) = i)" in theI')
  apply(auto simp add:C__mathIntOfChar_injective)
  apply(cut_tac i=i in C__charOfMathInt_Obligation_the)
  apply(auto)
  done
end-proof

theorem charOfMathInt_mathIntOfChar is
  fa(x:Char) charOfMathInt (mathIntOfChar x) = x


%subsection (* The Other Integer Types *)

(* The representation of an unsigned integer type other than unsigned char, must
consist of N value bits plus 0 or more padding bits, yielding a range of values
between 0 and 2^N-1 [ISO 6.2.6.2/1]. This constrains the U..._MAX value of each
unsigned integer type [ISO 5.2.4.2.1/1] to be 2^N-1. We assume that no padding
bits are used, so that the representation consists of exactly N (value)
bits. Since every value (including integers) has a size in bytes [ISO 6.5.3.4/2,
6.2.6.1/4], N must be a multiple of CHAR_BIT.

The sizeof_... constants express the size, in bytes, of each unsigned integer
type. So, for each unsigned integer type, the number of bits N is CHAR_BIT times
the sizeof_... constants. For convenience, we also define ..._bit constants that
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

proof isa -verbatim
declare C__short_bits_def [simp]
declare C__int_bits_def [simp]
declare C__long_bits_def [simp]
declare C__llong_bits_def [simp]
declare C__sizeof_short_def [simp]
declare C__sizeof_int_def [simp]
declare C__sizeof_long_def [simp]
declare C__sizeof_llong_def [simp]
end-proof

theorem min_sizeof_short is sizeof_short >= 2
theorem min_sizeof_int   is sizeof_int   >= 2
theorem min_sizeof_long  is sizeof_long  >= 4
theorem min_sizeof_llong is sizeof_llong >= 8

theorem min_short_bits is short_bits >= 16
theorem min_int_bits   is   int_bits >= 16
theorem min_long_bits  is  long_bits >= 32
theorem min_llong_bits is llong_bits >= 64

%%TODO change back to mention SHRT
op USHORT_MAX : Nat = 2 ** short_bits - 1
op   UINT_MAX : Nat = 2 **   int_bits - 1
op  ULONG_MAX : Nat = 2 **  long_bits - 1
op ULLONG_MAX : Nat = 2 ** llong_bits - 1

proof isa -verbatim
declare C__USHORT_MAX_def [simp]
declare C__UINT_MAX_def [simp]
declare C__ULONG_MAX_def [simp]
declare C__ULLONG_MAX_def [simp]
end-proof

theorem min_USHORT_MAX is  USHORT_MAX >= 2 ** 16 - 1
theorem min_UINT_MAX   is  UINT_MAX   >= 2 ** 16 - 1
theorem min_ULONG_MAX  is  ULONG_MAX  >= 2 ** 32 - 1
theorem min_ULLONG_MAX is  ULLONG_MAX >= 2 ** 64 - 1

op rangeOfUshort : FiniteSet Int = fn i:Int -> 0 <= i && i <= USHORT_MAX
op rangeOfUint   : FiniteSet Int = fn i:Int -> 0 <= i && i <= UINT_MAX
op rangeOfUlong  : FiniteSet Int = fn i:Int -> 0 <= i && i <= ULONG_MAX
op rangeOfUllong : FiniteSet Int = fn i:Int -> 0 <= i && i <= ULLONG_MAX

%% Ints that fit in their respective data types
%% TODO should we use Nat as the base type?
%% TODO use these more (currently trying it out with just IntUint)
type IntUshort = {i:Int | i in? rangeOfUshort}
type IntUint   = {i:Int | i in? rangeOfUint  }
type IntUlong  = {i:Int | i in? rangeOfUlong }
type IntUllong = {i:Int | i in? rangeOfUllong}

type Ushort = | ushort (Bits | ofLength? short_bits)
type   Uint = | uint   (Bits | ofLength?   int_bits)
type  Ulong = | ulong  (Bits | ofLength?  long_bits)
type Ullong = | ullong (Bits | ofLength? llong_bits)

op mathIntOfUshort (ushort bs : Ushort) : IntUshort = toNat bs
op mathIntOfUint   (uint   bs : Uint)   : IntUint   = toNat bs
op mathIntOfUlong  (ulong  bs : Ulong)  : IntUlong  = toNat bs
op mathIntOfUllong (ullong bs : Ullong) : IntUllong = toNat bs

theorem mathIntOfUshort_non_neg is fa(x:Ushort) 0 <= mathIntOfUshort x
theorem mathIntOfUint_non_neg   is fa(x:Uint  ) 0 <= mathIntOfUint   x
theorem mathIntOfUlong_non_neg  is fa(x:Ulong ) 0 <= mathIntOfUlong  x
theorem mathIntOfUllong_non_neg is fa(x:Ullong) 0 <= mathIntOfUllong x

theorem mathIntOfUshort_injective is
  fa(x:Ushort, y:Ushort) (mathIntOfUshort x = mathIntOfUshort y) = (x = y)

theorem mathIntOfUint_injective is
  fa(x:Uint, y:Uint) (mathIntOfUint x = mathIntOfUint y) = (x = y)

theorem mathIntOfUlong_injective is
  fa(x:Ulong, y:Ulong) (mathIntOfUlong x = mathIntOfUlong y) = (x = y)

theorem mathIntOfUllong_injective is
  fa(x:Ullong, y:Ullong) (mathIntOfUllong x = mathIntOfUllong y) = (x = y)

theorem mathIntOfUshort_injective_fw is
  fa(x:Ushort, y:Ushort) (mathIntOfUshort x = mathIntOfUshort y) => (x = y)

theorem mathIntOfUint_injective_fw is
  fa(x:Uint, y:Uint) (mathIntOfUint x = mathIntOfUint y) => (x = y)

theorem mathIntOfUlong_injective_fw is
  fa(x:Ulong, y:Ulong) (mathIntOfUlong x = mathIntOfUlong y) => (x = y)

theorem mathIntOfUllong_injective_fw is
  fa(x:Ullong, y:Ullong) (mathIntOfUllong x = mathIntOfUllong y) => (x = y)

theorem ushort_range is fa(x:Ushort) ((mathIntOfUshort x):Int) in? rangeOfUshort
theorem uint_range is fa(x:Uint)   ((mathIntOfUint   x):Int) in? rangeOfUint
theorem ulong_range is fa(x:Ulong)  ((mathIntOfUlong  x):Int) in? rangeOfUlong
theorem ullong_range is fa(x:Ullong) ((mathIntOfUllong x):Int) in? rangeOfUllong

op ushortOfMathInt (i:IntUshort) : Ushort = the(x:Ushort) mathIntOfUshort x = i
op   uintOfMathInt (i:IntUint  ) : Uint   = the(x:Uint  ) mathIntOfUint   x = i
op  ulongOfMathInt (i:IntUlong ) : Ulong  = the(x:Ulong ) mathIntOfUlong  x = i
op ullongOfMathInt (i:IntUllong) : Ullong = the(x:Ullong) mathIntOfUllong x = i

theorem mathIntOfUshort_ushortOfMathInt is
  fa(i:Int) i in? rangeOfUshort => mathIntOfUshort (ushortOfMathInt i) = i

theorem mathIntOfUint_uintOfMathInt is
  fa(i:Int) i in? rangeOfUint => mathIntOfUint (uintOfMathInt i) = i

theorem mathIntOfUlong_ulongOfMathInt is
  fa(i:Int) i in? rangeOfUlong => mathIntOfUlong (ulongOfMathInt i) = i

theorem mathIntOfUllong_ullongOfMathInt is
  fa(i:Int) i in? rangeOfUllong => mathIntOfUllong (ullongOfMathInt i) = i

%TODO why verbatim?
proof isa -verbatim
theorem C__mathIntOfUshort_ushortOfMathInt_2: 
  "\<lbrakk>i \<in> C__rangeOfUshort\<rbrakk> \<Longrightarrow> 
   (C__mathIntOfUshort (C__ushortOfMathInt i)) = i"
  apply (cut_tac i=i in C__mathIntOfUshort_ushortOfMathInt)
  apply(auto simp del:C__mathIntOfUshort_ushortOfMathInt)
  done

(*TODO add to [simp]   TODO delete this now that the type has changed? *)
theorem C__mathIntOfUint_uintOfMathInt_2: 
  "\<lbrakk>i \<in> C__rangeOfUint\<rbrakk> \<Longrightarrow> 
   (C__mathIntOfUint (C__uintOfMathInt i)) = i"
  apply (cut_tac i=i in C__mathIntOfUint_uintOfMathInt)
  apply(auto simp del:C__mathIntOfUint_uintOfMathInt)
  done

theorem C__mathIntOfUlong_ulongOfMathInt_2: 
  "\<lbrakk>i \<in> C__rangeOfUlong\<rbrakk> \<Longrightarrow> 
   (C__mathIntOfUlong (C__ulongOfMathInt i)) = i"
  apply (cut_tac i=i in C__mathIntOfUlong_ulongOfMathInt)
  apply(auto simp del:C__mathIntOfUlong_ulongOfMathInt)
  done

theorem C__mathIntOfUllong_ullongOfMathInt_2: 
  "\<lbrakk>i \<in> C__rangeOfUllong\<rbrakk> \<Longrightarrow> 
   (C__mathIntOfUllong (C__ullongOfMathInt i)) = i"
  apply (cut_tac i=i in C__mathIntOfUllong_ullongOfMathInt)
  apply(auto simp del:C__mathIntOfUllong_ullongOfMathInt)
  done

theorem C__Ushort__subtype_pred_ushortOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfUshort\<rbrakk> \<Longrightarrow>
  C__Ushort__subtype_pred (C__ushortOfMathInt i)"
  apply(simp add: C__ushortOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Ushort) . (C__Ushort__subtype_pred x \<and> (C__mathIntOfUshort x) = i)" in theI')
  apply(auto simp add:C__mathIntOfUshort_injective)
  apply(cut_tac i=i in C__ushortOfMathInt_Obligation_the)
  apply(auto)
  done

theorem C__Uint__subtype_pred_uintOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfUint\<rbrakk> \<Longrightarrow>
  C__Uint__subtype_pred (C__uintOfMathInt i)"
  apply(simp add: C__uintOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Uint) . (C__Uint__subtype_pred x \<and> (C__mathIntOfUint x) = i)" in theI')
  apply(auto simp add:C__mathIntOfUint_injective)
  apply(cut_tac i=i in C__uintOfMathInt_Obligation_the)
  apply(auto)
  done

theorem C__Ulong__subtype_pred_ulongOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfUlong\<rbrakk> \<Longrightarrow>
  C__Ulong__subtype_pred (C__ulongOfMathInt i)"
  apply(simp add: C__ulongOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Ulong) . (C__Ulong__subtype_pred x \<and> (C__mathIntOfUlong x) = i)" in theI')
  apply(auto simp add:C__mathIntOfUlong_injective)
  apply(cut_tac i=i in C__ulongOfMathInt_Obligation_the)
  apply(auto)
  done

theorem C__Ullong__subtype_pred_ullongOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfUllong\<rbrakk> \<Longrightarrow>
  C__Ullong__subtype_pred (C__ullongOfMathInt i)"
  apply(simp add: C__ullongOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Ullong) . (C__Ullong__subtype_pred x \<and> (C__mathIntOfUllong x) = i)" in theI')
  apply(auto simp add:C__mathIntOfUllong_injective)
  apply(cut_tac i=i in C__ullongOfMathInt_Obligation_the)
  apply(auto)
  done
end-proof

theorem ushortOfMathInt_mathIntOfUshort is
  fa(x:Ushort) ushortOfMathInt (mathIntOfUshort x) = x

theorem uintOfMathInt_mathIntOfUint is
  fa(x:Uint) uintOfMathInt (mathIntOfUint x) = x

theorem ulongOfMathInt_mathIntOfUlong is
  fa(x:Ulong) ulongOfMathInt (mathIntOfUlong x) = x

theorem ullongOfMathInt_mathIntOfUllong is
  fa(x:Ullong) ullongOfMathInt (mathIntOfUllong x) = x

(* The signed integer types use the same amount of storage as their unsigned
counterparts [ISO 6.2.5/6]. Thus, the sizeof_... and ..._bits constants above
also apply to the signed integer types, not only the unsigned ones -- note that
the names of those constants make no reference to (un)signedness.

Similarly to the signed char type, we assume that the other signed integer types
use a two's complement representation with no padding bits [ISO 6.2.6.2/2].
Thus, the sizeof_... constants determine the values below for the ..._MIN and
..._MAX limits of the signed integer types [ISO 5.2.4.2.1/1]. *)

op SSHORT_MIN : Int = - (2 ** (short_bits - 1))
op   SINT_MIN : Int = - (2 ** (  int_bits - 1))
op  SLONG_MIN : Int = - (2 ** ( long_bits - 1))
op SLLONG_MIN : Int = - (2 ** (llong_bits - 1))

op SSHORT_MAX : Nat =   2 ** (short_bits - 1) - 1
op   SINT_MAX : Nat =   2 ** (  int_bits - 1) - 1
op  SLONG_MAX : Nat =   2 ** ( long_bits - 1) - 1
op SLLONG_MAX : Nat =   2 ** (llong_bits - 1) - 1

proof isa -verbatim
declare C__SSHORT_MIN_def [simp]
declare C__SINT_MIN_def [simp]
declare C__SLONG_MIN_def [simp]
declare C__SLLONG_MIN_def [simp]

declare C__SSHORT_MAX_def [simp]
declare C__SINT_MAX_def [simp]
declare C__SLONG_MAX_def [simp]
declare C__SLLONG_MAX_def [simp]
end-proof

theorem min_SSHORT_MIN is  SSHORT_MIN <= - (2 ** 15)
theorem min_SINT_MIN   is    SINT_MIN <= - (2 ** 15)
theorem min_SLONG_MIN  is   SLONG_MIN <= - (2 ** 31)
theorem min_SLLONG_MIN is  SLLONG_MIN <= - (2 ** 63)

theorem min_SSHORT_MAX is  SSHORT_MAX >=    2 ** 15 - 1
theorem min_SINT_MAX   is    SINT_MAX >=    2 ** 15 - 1
theorem min_SLONG_MAX  is   SLONG_MAX >=    2 ** 31 - 1
theorem min_SLLONG_MAX is  SLLONG_MAX >=    2 ** 63 - 1

type Sshort = | sshort (Bits | ofLength? short_bits)
type   Sint = | sint   (Bits | ofLength?   int_bits)
type  Slong = | slong  (Bits | ofLength?  long_bits)
type Sllong = | sllong (Bits | ofLength? llong_bits)

op mathIntOfSshort (sshort bs : Sshort) : Int = toInt bs
op mathIntOfSint   (sint   bs : Sint)   : Int = toInt bs
op mathIntOfSlong  (slong  bs : Slong)  : Int = toInt bs
op mathIntOfSllong (sllong bs : Sllong) : Int = toInt bs

theorem mathIntOfSshort_injective is
  fa(x:Sshort, y:Sshort) (mathIntOfSshort x = mathIntOfSshort y) = (x = y)
theorem mathIntOfSint_injective is
  fa(x:Sint, y:Sint) (mathIntOfSint x = mathIntOfSint y) = (x = y)
theorem mathIntOfSlong_injective is
  fa(x:Slong, y:Slong) (mathIntOfSlong x = mathIntOfSlong y) = (x = y)
theorem mathIntOfSllong_injective is
  fa(x:Sllong, y:Sllong) (mathIntOfSllong x = mathIntOfSllong y) = (x = y)

theorem mathIntOfSshort_injective_fw is
  fa(x:Sshort, y:Sshort) (mathIntOfSshort x = mathIntOfSshort y) => (x = y)
theorem mathIntOfSint_injective_fw is
  fa(x:Sint, y:Sint) (mathIntOfSint x = mathIntOfSint y) => (x = y)
theorem mathIntOfSlong_injective_fw is
  fa(x:Slong, y:Slong) (mathIntOfSlong x = mathIntOfSlong y) => (x = y)
theorem mathIntOfSllong_injective_fw is
  fa(x:Sllong, y:Sllong) (mathIntOfSllong x = mathIntOfSllong y) => (x = y)

op rangeOfSshort : FiniteSet Int =
 fn i:Int -> SSHORT_MIN <= i && i <= SSHORT_MAX

op rangeOfSint   : FiniteSet Int =
 fn i:Int -> SINT_MIN <= i && i <= SINT_MAX

op rangeOfSlong  : FiniteSet Int =
 fn i:Int -> SLONG_MIN <= i && i <= SLONG_MAX

op rangeOfSllong : FiniteSet Int =
 fn i:Int -> SLLONG_MIN <= i && i <= SLLONG_MAX

%%clean this: up
proof isa -verbatim

(* use a refine def? *)

theorem rangeOfSchar_alt_def:
  "C__rangeOfSchar = TwosComplement__rangeForLength C__CHAR_BIT"
  apply(simp add: C__rangeOfSchar_def TwosComplement__rangeForLength_def TwosComplement__minForLength_def TwosComplement__maxForLength_def)
  done

theorem rangeOfSshort_alt_def:
  "C__rangeOfSshort = TwosComplement__rangeForLength C__short_bits"
  apply(simp add: C__rangeOfSshort_def TwosComplement__rangeForLength_def TwosComplement__minForLength_def TwosComplement__maxForLength_def)
  done

theorem rangeOfSint_alt_def:
  "C__rangeOfSint = TwosComplement__rangeForLength C__int_bits"
  apply(simp add: C__rangeOfSint_def TwosComplement__rangeForLength_def TwosComplement__minForLength_def TwosComplement__maxForLength_def)
  done

theorem rangeOfSlong_alt_def:
  "C__rangeOfSlong = TwosComplement__rangeForLength C__long_bits"
  apply(simp add: C__rangeOfSlong_def TwosComplement__rangeForLength_def TwosComplement__minForLength_def TwosComplement__maxForLength_def)
  done

theorem rangeOfSllong_alt_def:
  "C__rangeOfSllong = TwosComplement__rangeForLength C__llong_bits"
  apply(simp add: C__rangeOfSllong_def TwosComplement__rangeForLength_def TwosComplement__minForLength_def TwosComplement__maxForLength_def)
  done

end-proof

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

proof isa -verbatim
declare TwosComplement__rangeForLength_def [simp]
declare TwosComplement__minForLength_def [simp]
declare TwosComplement__maxForLength_def [simp]
end-proof

theorem mathIntOfSshort_sshortOfMathInt is
  fa(i:Int) i in? rangeOfSshort => mathIntOfSshort (sshortOfMathInt i) = i

theorem mathIntOfSint_sintOfMathInt is
  fa(i:Int) i in? rangeOfSint => mathIntOfSint (sintOfMathInt i) = i

theorem mathIntOfSlong_slongOfMathInt is
  fa(i:Int) i in? rangeOfSlong => mathIntOfSlong (slongOfMathInt i) = i

theorem mathIntOfSllong_sllongOfMathInt is
  fa(i:Int) i in? rangeOfSllong => mathIntOfSllong (sllongOfMathInt i) = i

proof isa -verbatim
theorem C__Sshort__subtype_pred_sshortOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfSshort\<rbrakk> \<Longrightarrow>
  C__Sshort__subtype_pred (C__sshortOfMathInt i)"
  apply(simp add: C__sshortOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Sshort) . (C__Sshort__subtype_pred x \<and> (C__mathIntOfSshort x) = i)" in theI')
  apply(auto simp add:C__mathIntOfSshort_injective)
  apply(cut_tac i=i in C__sshortOfMathInt_Obligation_the)
  apply(auto)
  done
end-proof

proof isa -verbatim
theorem C__Sint__subtype_pred_sintOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfSint\<rbrakk> \<Longrightarrow>
  C__Sint__subtype_pred (C__sintOfMathInt i)"
  apply(simp add: C__sintOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Sint) . (C__Sint__subtype_pred x \<and> (C__mathIntOfSint x) = i)" in theI')
  apply(auto simp add:C__mathIntOfSint_injective)
  apply(cut_tac i=i in C__sintOfMathInt_Obligation_the)
  apply(auto)
  done
end-proof

proof isa -verbatim
theorem C__Slong__subtype_pred_slongOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfSlong\<rbrakk> \<Longrightarrow>
  C__Slong__subtype_pred (C__slongOfMathInt i)"
  apply(simp add: C__slongOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Slong) . (C__Slong__subtype_pred x \<and> (C__mathIntOfSlong x) = i)" in theI')
  apply(auto simp add:C__mathIntOfSlong_injective)
  apply(cut_tac i=i in C__slongOfMathInt_Obligation_the)
  apply(auto)
  done
end-proof

proof isa -verbatim
theorem C__Sllong__subtype_pred_sllongOfMathInt [simp]:
  "\<lbrakk>(i::int) \<in> C__rangeOfSllong\<rbrakk> \<Longrightarrow>
  C__Sllong__subtype_pred (C__sllongOfMathInt i)"
  apply(simp add: C__sllongOfMathInt_def)
  apply(cut_tac P="\<lambda> (x::C__Sllong) . (C__Sllong__subtype_pred x \<and> (C__mathIntOfSllong x) = i)" in theI')
  apply(auto simp add:C__mathIntOfSllong_injective)
  apply(cut_tac i=i in C__sllongOfMathInt_Obligation_the)
  apply(auto)
  done
end-proof

theorem sshortOfMathInt_mathIntOfSshort is
  fa(x:Sshort) sshortOfMathInt (mathIntOfSshort x) = x

theorem sintOfMathInt_mathIntOfSint is
  fa(x:Sint) sintOfMathInt (mathIntOfSint x) = x

theorem slongOfMathInt_mathIntOfSlong is
  fa(x:Slong) slongOfMathInt (mathIntOfSlong x) = x

theorem sllongOfMathInt_mathIntOfSllong is
  fa(x:Sllong) sllongOfMathInt (mathIntOfSllong x) = x

refine def scharOfMathInt  (i:Int | i in? rangeOfSchar) : Schar  =
 schar (tcNumber(i, CHAR_BIT))

refine def sshortOfMathInt (i:Int | i in? rangeOfSshort) : Sshort =
 sshort (tcNumber(i, short_bits))

refine def sintOfMathInt   (i:Int | i in? rangeOfSint) : Sint   =
 sint (tcNumber(i, int_bits))

refine def slongOfMathInt  (i:Int | i in? rangeOfSlong) : Slong  =
 slong (tcNumber(i, long_bits))

refine def sllongOfMathInt (i:Int | i in? rangeOfSllong) : Sllong =
 sllong (tcNumber(i, llong_bits))

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
 (Array (Array Char | ofLength? 4) | ofLength? 2)   for   char[2][4]

*)


%subsection (* Structures *)


(* TODO: "deepen" the structs, as maps from names to values *)


(* A structure is a sequence of named objects, not necessarily of the same type
[ISO 6.2.5./20]. This corresponds to a Metaslang record almost perfectly, except
that in Metaslang record fields are ordered alphabetically, while in a C
structure members are ordered as declared by the program. It may be possible to
work around this mismatch by having the code generator map Metaslang fields like
'_a_first', '_b_second', '_c_third', '_d_fourth', etc. to C fields like 'first',
'second', 'third', 'fourth', etc.

In order to represent a C structure type, a Metaslang record type must have only
fields whose Metaslang types correspond to C types, e.g.

 {x:Sint, y:Sint}   for   struct {int x, int y}

Given a named Metaslang record type

 type R = {f1:T1, ..., fn:Tn}

where all the Ti's are Metaslang types that correspond to C types, the C code
generator should generate a structure declaration [ISO 6.7, 6.7.2.1]

 struct R {U1 f1; ... Un fn;};

where each Ui is the C type that corresponds to the Metaslang type Ti. *)


%subsection (* Type Definitions *)

(* A type definition [ISO 6.7.8] assigns a synonym to an existing type. This
corresponds to Metaslang type definitions, e.g.

 type T = Uint   for   typedef unsigned int T

*)


%subsection (* Other Types *)

(* We may extend this formalization with other Metaslang types that correspond
to C types, e.g. floating types [ISO 6.2.5/10]. *)


%section (* Values *)

(* We define a type that includes all the C values of the types that we have
defined above....... *)

type Value =
  | Uchar Uchar
  % ... add all others

(*

introduce object designators (from deep embedding)

*)







%section (* Constants *)

(* We define Metaslang ops that correspond to C constants. *)


%subsection (* Integer Constants *)

(* An integer constant [ISO 6.4.4.1] denotes a natural number, in decimal,
hexadecimal, or octal notation. Since Metaslang internally translates decimal,
binary, octal and hexadecimal constants to the same representation, we introduce
an enumeration that is used in subsequent ops to indicate the desired base of 
constants. *)

type IntConstBase = | dec | hex | oct

(* The following ops create integer values out of natural numbers in the
appropriate ranges. The base argument does not affect the result, but is needed
so that the C code generator can generate, from the following ops, constants in
the desired base. In addition, the C code generator must generate appropriate U,
L, and LL suffixes. *)

op sintConstant (n:Nat | (n:Int) in? rangeOfSint) (base:IntConstBase) : Sint =
  sintOfMathInt n

op slongConstant (n:Nat | (n:Int) in? rangeOfSlong) (base:IntConstBase) : Slong =
  slongOfMathInt n

op sllongConstant (n:Nat | (n:Int) in? rangeOfSllong) (base:IntConstBase) : Sllong =
  sllongOfMathInt n

op uintConstant (n:IntUint) (base:IntConstBase) : Uint =
  uintOfMathInt n

op ulongConstant (n:IntUlong) (base:IntConstBase) : Ulong =
  ulongOfMathInt n

op ullongConstant (n:IntUllong) (base:IntConstBase) : Ullong =
  ullongOfMathInt n


%subsection (* Other Constants *)

(* We may extend this formalization with other Metaslang types that correspond
to C constants, e.g. floating constants [ISO 6.4.4.2]. *)


%section (* Operators *)

(* We introduce Metaslang operators that correpond to C operators. If a
Metaslang spec is refined to use such Metaslang operators, the code generator
can map them to the corresponding C operators. *)


%subsection (* Integer Conversions *)

(* An integer value can be converted into (a value of) an(other) integer type
[ISO 6.3.1.3].

The conversion is described in terms of the mathematical value of the integer.
If the new type can represent it, the (mathematical) value is unchanged [ISO
6.3.1.3/1].

Otherwise, the outcome depends on whether the new type is unsigned or not. Note
that the new type could be char, which is classified as neither a signed or an
unsigned integer type [ISO 6.2.5/4, 6.2.5/6]. But according to [ISO 6.2.5/15]
the char type has the same behavior as either signed or unsigned char, and this
choice is captured by ops plainCharsAreSigned and plainCharsAreUnsigned,
introduced earlier.

If the new type is unsigned but cannot represent the mathematical value of the
integer, we apply the (flooring) modulo operation, with argument one plus the
maximum representable integer in the type. This is equivalent to the repeated
subtraction or addition mentioned in [ISO 6.3.1.3/2].

If the new type is signed but cannot represent the mathematical value of the
integer, the outcome is non-standard [ISO 6.3.1.3/3]. We use subtype
constraints to ensure that the results of the conversions are always standard
and well-defined; in other words, we disallow conversions when the outcome is
non-standard.

There are 11 integer types:

 uchar ushort uint ulong ullong
 schar sshort sint slong sllong
 char

Thus, there are 11 * 11 - 11 = 110 conversion ops. *)

proof isa -verbatim
declare C__rangeOfUchar_def [simp]
declare C__rangeOfUshort_def [simp]
declare C__rangeOfUint_def [simp]
declare C__rangeOfUlong_def [simp]
declare C__rangeOfUllong_def [simp]
declare C__rangeOfSchar_def [simp]
declare C__rangeOfChar_def [simp]
end-proof

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
  ushortOfMathInt (mathIntOfUint x modF (1 + USHORT_MAX))

op ushortOfUlong (x:Ulong) : Ushort =
  ushortOfMathInt (mathIntOfUlong x modF (1 + USHORT_MAX))

op ushortOfUllong (x:Ullong) : Ushort =
  ushortOfMathInt (mathIntOfUllong x modF (1 + USHORT_MAX))

op ushortOfSchar (x:Schar) : Ushort =
  ushortOfMathInt (mathIntOfSchar x modF (1 + USHORT_MAX))

op ushortOfSshort (x:Sshort) : Ushort =
  ushortOfMathInt (mathIntOfSshort x modF (1 + USHORT_MAX))

op ushortOfSint (x:Sint) : Ushort =
  ushortOfMathInt (mathIntOfSint x modF (1 + USHORT_MAX))

op ushortOfSlong (x:Slong) : Ushort =
  ushortOfMathInt (mathIntOfSlong x modF (1 + USHORT_MAX))

op ushortOfSllong (x:Sllong) : Ushort =
  ushortOfMathInt (mathIntOfSllong x modF (1 + USHORT_MAX))

op ushortOfChar (x:Char) : Ushort =
  ushortOfMathInt (mathIntOfChar x modF (1 + USHORT_MAX))

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

op scharOfUchar (x:Uchar | ((mathIntOfUchar x):Int) in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfUchar x)

op scharOfUshort (x:Ushort | ((mathIntOfUshort x):Int) in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfUshort x)

op scharOfUint (x:Uint | ((mathIntOfUint x):Int) in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfUint x)

op scharOfUlong (x:Ulong | ((mathIntOfUlong x):Int) in? rangeOfSchar) : Schar =
  scharOfMathInt (mathIntOfUlong x)

op scharOfUllong (x:Ullong | ((mathIntOfUllong x):Int) in? rangeOfSchar) : Schar =
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

proof isa -verbatim
declare C__rangeOfSshort_def [simp]
declare C__rangeOfSint_def [simp]
declare C__rangeOfSlong_def [simp]
declare C__rangeOfSllong_def [simp]
end-proof

op sshortOfUchar (x:Uchar) : Sshort =
  sshortOfMathInt (mathIntOfUchar x)

op sshortOfUshort (x:Ushort | ((mathIntOfUshort x):Int) in? rangeOfSshort) : Sshort =
  sshortOfMathInt (mathIntOfUshort x)

op sshortOfUint (x:Uint | ((mathIntOfUint x):Int) in? rangeOfSshort) : Sshort =
  sshortOfMathInt (mathIntOfUint x)

op sshortOfUlong (x:Ulong | ((mathIntOfUlong x):Int) in? rangeOfSshort) : Sshort =
  sshortOfMathInt (mathIntOfUlong x)

op sshortOfUllong (x:Ullong | ((mathIntOfUllong x):Int) in? rangeOfSshort) : Sshort =
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

op sintOfUshort (x:Ushort | ((mathIntOfUshort x):Int) in? rangeOfSint) : Sint =
  sintOfMathInt (mathIntOfUshort x)

op sintOfUint (x:Uint | ((mathIntOfUint x):Int) in? rangeOfSint) : Sint =
  sintOfMathInt (mathIntOfUint x)

op sintOfUlong (x:Ulong | ((mathIntOfUlong x):Int) in? rangeOfSint) : Sint =
  sintOfMathInt (mathIntOfUlong x)

op sintOfUllong (x:Ullong | ((mathIntOfUllong x):Int) in? rangeOfSint) : Sint =
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

op slongOfUshort (x:Ushort | ((mathIntOfUshort x):Int) in? rangeOfSlong) : Slong =
  slongOfMathInt (mathIntOfUshort x)

op slongOfUint (x:Uint | ((mathIntOfUint x):Int) in? rangeOfSlong) : Slong =
  slongOfMathInt (mathIntOfUint x)

op slongOfUlong (x:Ulong | ((mathIntOfUlong x):Int) in? rangeOfSlong) : Slong =
  slongOfMathInt (mathIntOfUlong x)

op slongOfUllong (x:Ullong | ((mathIntOfUllong x):Int) in? rangeOfSlong) : Slong =
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

op sllongOfUshort (x:Ushort | ((mathIntOfUshort x):Int) in? rangeOfSllong) : Sllong =
  sllongOfMathInt (mathIntOfUshort x)

op sllongOfUint (x:Uint | ((mathIntOfUint x):Int) in? rangeOfSllong) : Sllong =
  sllongOfMathInt (mathIntOfUint x)

op sllongOfUlong (x:Ulong | ((mathIntOfUlong x):Int) in? rangeOfSllong) : Sllong =
  sllongOfMathInt (mathIntOfUlong x)

op sllongOfUllong (x:Ullong | ((mathIntOfUllong x):Int) in? rangeOfSllong) : Sllong =
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

op charOfUchar (x:Uchar | ((mathIntOfUchar x):Int) in? rangeOfChar) : Char =
  charOfMathInt (mathIntOfUchar x)

op charOfUshort (x:Ushort |
   plainCharsAreSigned => ((mathIntOfUshort x):Int) in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfUshort x)
  else charOfMathInt (mathIntOfUshort x modF (1 + UCHAR_MAX))

op charOfUint (x:Uint |
   plainCharsAreSigned => ((mathIntOfUint x):Int) in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfUint x)
  else charOfMathInt (mathIntOfUint x modF (1 + UCHAR_MAX))

op charOfUlong (x:Ulong |
   plainCharsAreSigned => ((mathIntOfUlong x):Int) in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfUlong x)
  else charOfMathInt (mathIntOfUlong x modF (1 + UCHAR_MAX))

op charOfUllong (x:Ullong |
   plainCharsAreSigned => ((mathIntOfUllong x):Int) in? rangeOfChar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfUllong x)
  else charOfMathInt (mathIntOfUllong x modF (1 + UCHAR_MAX))

%%TODO issue with obligation
op charOfSchar (x:Schar) : Char =
  if plainCharsAreSigned then charOfMathInt (mathIntOfSchar x)
  else charOfMathInt (mathIntOfSchar x modF (1 + UCHAR_MAX))

%%just use by auto?
proof isa charOfSchar_Obligation_subtype 
  apply(case_tac "x", simp)
  done
end-proof

proof isa charOfSchar_Obligation_subtype1
  apply(case_tac "x")
  apply(simp add: mod_upper_bound_chained mod_lower_bound_chained)
end-proof

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

proof isa -verbatim
declare fun_Compl_def [simp]
end-proof

theorem ucharOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ucharOfSchar (schar bs) = uchar bs

theorem ucharOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ucharOfChar (char bs) = uchar bs

theorem scharOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT && ((toNat bs):Int) in? rangeOfSchar =>
    scharOfUchar (uchar bs) = schar bs

theorem scharOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT &&
              mathIntOfChar (char bs) in? rangeOfSchar =>
    scharOfChar (char bs) = schar bs

theorem charOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT && ((toNat bs):Int) in? rangeOfChar =>
    charOfUchar (uchar bs) = char bs

theorem charOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT && ((toInt bs):Int) in? rangeOfChar =>
    charOfSchar (schar bs) = char bs

theorem ushortOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    ushortOfSshort (sshort bs) = ushort bs

theorem sshortOfUshort_bits is
  fa(bs:Bits) length bs = short_bits && ((toNat bs):Int) in? rangeOfSshort =>
    sshortOfUshort (ushort bs) = sshort bs

theorem uintOfSint_bits is
  fa(bs:Bits) length bs = int_bits =>
    uintOfSint (sint bs) = uint bs

theorem sintOfUint_bits is
  fa(bs:Bits) length bs = int_bits && ((toNat bs):Int) in? rangeOfSint =>
    sintOfUint (uint bs) = sint bs

theorem ulongOfSlong_bits is
  fa(bs:Bits) length bs = long_bits =>
    ulongOfSlong (slong bs) = ulong bs

theorem slongOfUlong_bits is
  fa(bs:Bits) length bs = long_bits && ((toNat bs):Int) in? rangeOfSlong =>
    slongOfUlong (ulong bs) = slong bs

theorem ullongOfSllong_bits is
  fa(bs:Bits) length bs = llong_bits =>
    ullongOfSllong (sllong bs) = ullong bs

theorem sllongOfUllong_bits is
  fa(bs:Bits) length bs = llong_bits && ((toNat bs):Int) in? rangeOfSllong =>
    sllongOfUllong (ullong bs) = sllong bs

(* Converting from an unsigned integer type to an unsigned integer type of
higher rank amounts to zero-extending the bits. *)

refine def ucharOfMathInt  (i:Int | i in? rangeOfUchar) : Uchar = uchar (bits(i, CHAR_BIT))
refine def ushortOfMathInt (i:Int | i in? rangeOfUshort) : Ushort = ushort (bits(i, short_bits))
refine def uintOfMathInt   (i:Int | i in? rangeOfUint  ) : Uint   = uint   (bits(i,   int_bits))
refine def ulongOfMathInt  (i:Int | i in? rangeOfUlong ) : Ulong  = ulong  (bits(i,  long_bits))
refine def ullongOfMathInt (i:Int | i in? rangeOfUllong) : Ullong = ullong (bits(i, llong_bits))

%% %TODO move up and use more
%% %TODO kill use the refine def instead
%% proof isa -verbatim
%% theorem C__ushortOfMathInt_alt_def: 
%%   "\<lbrakk>i \<in> C__rangeOfUshort\<rbrakk> \<Longrightarrow> 
%%    (C__ushortOfMathInt i) = C__ushort (toBits(nat i,16::nat))"
%%   apply(cut_tac x="(C__ushortOfMathInt i)" and y="C__ushort (toBits(nat i,16::nat))" in C__mathIntOfUshort_injective)
%%   apply(simp add: Bits__bits_length)
%%   apply(simp)
%%   apply(simp del:C__mathIntOfUshort_injective add:C__mathIntOfUshort_ushortOfMathInt_2)
%%   done
%% end-proof

theorem ushortOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ushortOfUchar (uchar bs) = ushort (zeroExtend (bs, short_bits))

theorem uintOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    uintOfUchar (uchar bs) = uint (zeroExtend (bs, int_bits))

theorem uintOfUshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    uintOfUshort (ushort bs) = uint (zeroExtend (bs, int_bits))

theorem ulongOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ulongOfUchar (uchar bs) = ulong (zeroExtend (bs, long_bits))

theorem ulongOfUshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    ulongOfUshort (ushort bs) = ulong (zeroExtend (bs, long_bits))

theorem ulongOfUint_bits is
  fa(bs:Bits) length bs = int_bits =>
    ulongOfUint (uint bs) = ulong (zeroExtend (bs, long_bits))

theorem ullongOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ullongOfUchar (uchar bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfUshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    ullongOfUshort (ushort bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfUint_bits is
  fa(bs:Bits) length bs = int_bits =>
    ullongOfUint (uint bs) = ullong (zeroExtend (bs, llong_bits))

theorem ullongOfUlong_bits is
  fa(bs:Bits) length bs = long_bits =>
    ullongOfUlong (ulong bs) = ullong (zeroExtend (bs, llong_bits))

(* Converting from a signed integer type to an unsigned integer type of higher
rank amounts to sign-extending the bits. *)

%% conversions of Schar

theorem ushortOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ushortOfSchar (schar bs) = ushort (signExtend (bs, short_bits))

theorem uintOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    uintOfSchar (schar bs) = uint (signExtend (bs, int_bits))

theorem ulongOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ulongOfSchar (schar bs) = ulong (signExtend (bs, long_bits))

theorem ullongOfSchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ullongOfSchar (schar bs) = ullong (signExtend (bs, llong_bits))

%% conversions of Sshort

theorem uintOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    uintOfSshort (sshort bs) = uint (signExtend (bs, int_bits))

theorem ulongOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    ulongOfSshort (sshort bs) = ulong (signExtend (bs, long_bits))

theorem ullongOfSshort_bits is
  fa(bs:Bits) length bs = short_bits =>
    ullongOfSshort (sshort bs) = ullong (signExtend (bs, llong_bits))

%% conversions of Sint

theorem ulongOfSint_bits is
  fa(bs:Bits) length bs = int_bits =>
    ulongOfSint (sint bs) = ulong (signExtend (bs, long_bits))

theorem ullongOfSint_bits is
  fa(bs:Bits) length bs = int_bits =>
    ullongOfSint (sint bs) = ullong (signExtend (bs, llong_bits))

%% conversions of Slong

theorem ullongOfSlong_bits is
  fa(bs:Bits) length bs = long_bits =>
    ullongOfSlong (slong bs) = ullong (signExtend (bs, llong_bits))

(* Converting from a Char to an unsigned integer type of higher rank amounts to
either sign-extending or zero-extending the bits, depending on whether
plainCharsAreSigned. *)

theorem ushortOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ushortOfChar (char bs) = 
    ushort (if plainCharsAreSigned then 
               (signExtend (bs, short_bits)) else 
               (zeroExtend (bs, short_bits))) 

theorem uintOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    uintOfChar (char bs) = 
    uint (if plainCharsAreSigned then 
               (signExtend (bs, int_bits)) else 
               (zeroExtend (bs, int_bits)))

theorem ulongOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ulongOfChar (char bs) = 
    ulong (if plainCharsAreSigned then 
               (signExtend (bs, long_bits)) else 
               (zeroExtend (bs, long_bits)))

theorem ullongOfChar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    ullongOfChar (char bs) =
    ullong (if plainCharsAreSigned then 
               (signExtend (bs, llong_bits)) else 
               (zeroExtend (bs, llong_bits)))

(* Converting from an unsigned integer type to a signed integer type of higher
rank amounts to zero-extending the bits. *)

theorem sshortOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    sshortOfUchar (uchar bs) = sshort (zeroExtend (bs, short_bits))

theorem sintOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    sintOfUchar (uchar bs) = sint (zeroExtend (bs, int_bits))

theorem slongOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    slongOfUchar (uchar bs) = slong (zeroExtend (bs, long_bits))

theorem sllongOfUchar_bits is
  fa(bs:Bits) length bs = CHAR_BIT =>
    sllongOfUchar (uchar bs) = sllong (zeroExtend (bs, llong_bits))

theorem sintOfUshort_bits is
  fa(bs:Bits) length bs = short_bits && ((toNat bs):Int) in? rangeOfSint =>
    sintOfUshort (ushort bs) = sint (zeroExtend (bs, int_bits))

theorem slongOfUshort_bits is
  fa(bs:Bits) length bs = short_bits && ((toNat bs):Int) in? rangeOfSlong =>
    slongOfUshort (ushort bs) = slong (zeroExtend (bs, long_bits))

theorem sllongOfUshort_bits is
  fa(bs:Bits) length bs = short_bits && ((toNat bs):Int) in? rangeOfSllong =>
    sllongOfUshort (ushort bs) = sllong (zeroExtend (bs, llong_bits))

theorem slongOfUint_bits is
  fa(bs:Bits) length bs = int_bits && ((toNat bs):Int) in? rangeOfSlong =>
    slongOfUint (uint bs) = slong (zeroExtend (bs, long_bits))

theorem sllongOfUint_bits is
  fa(bs:Bits) length bs = int_bits && ((toNat bs):Int) in? rangeOfSllong =>
    sllongOfUint (uint bs) = sllong (zeroExtend (bs, llong_bits))

theorem sllongOfUlong_bits is
  fa(bs:Bits) length bs = long_bits && ((toNat bs):Int) in? rangeOfSllong =>
    sllongOfUlong (ulong bs) = sllong (zeroExtend (bs, llong_bits))

%% TODO add comment

theorem sshortOfChar_bits_unsigned is
  plainCharsAreUnsigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     sshortOfChar (char bs) = sshort (zeroExtend (bs, short_bits)))

theorem sintOfChar_bits_unsigned is
  plainCharsAreUnsigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     sintOfChar (char bs) = sint (zeroExtend (bs, int_bits)))

theorem slongOfChar_bits_unsigned is
  plainCharsAreUnsigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     slongOfChar (char bs) = slong (zeroExtend (bs, long_bits)))

theorem sllongOfChar_bits_unsigned is
  plainCharsAreUnsigned =>
  (fa(bs:Bits) length bs = CHAR_BIT =>
     sllongOfChar (char bs) = sllong (zeroExtend (bs, llong_bits)))

(* Converting from a signed integer type to a signed integer type of higher rank
amounts to sign-extending the bits. *)

proof isa -verbatim
lemmas Conversions =
  C__sshortOfSchar_def
  C__sshortOfChar_def
  C__sintOfSchar_def
  C__sintOfChar_def
  C__slongOfSchar_def
  C__slongOfChar_def
  C__sllongOfSchar_def
  C__sllongOfChar_def
  C__sintOfSshort_def
  C__slongOfSshort_def
  C__sllongOfSshort_def
  C__slongOfSint_def
  C__sllongOfSint_def
  C__sllongOfSlong_def
  C__sshortOfMathInt__1__obligation_refine_def
  C__sshortOfMathInt__1_def
  C__sintOfMathInt__1__obligation_refine_def
  C__sintOfMathInt__1_def
  C__slongOfMathInt__1__obligation_refine_def
  C__slongOfMathInt__1_def
  C__sllongOfMathInt__1__obligation_refine_def
  C__sllongOfMathInt__1_def
  TwosComplement__nonNegative_p_def
  TwosComplement__negative_p_def
  TwosComplement__sign_def
  mod_does_nothing_rewrite
end-proof

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


proof isa -verbatim
(****************** we need these later **********)

lemma charOfMathInt_suffix:
  "\<lbrakk>length bs \<ge> 8; toNat bs \<le> 255\<rbrakk>
    \<Longrightarrow> C__charOfMathInt (int (toNat bs) mod 256) = C__char (List__suffix (bs, 8))"
  apply (rule_tac t="256" and s="int 256" in subst, arith, 
         simp only: zmod_int [symmetric], simp)
  apply (subst C__mathIntOfChar_injective [symmetric],
         rule C__Char__subtype_pred_charOfMathInt,
         simp_all add: C__plainCharsAreSigned_def toNat_suffix)
done
(***********************************************************)
end-proof

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
    ushortOfUint (uint bs) = ushort (suffix (bs, short_bits))

theorem ushortOfUlong_bit is
  fa(bs:Bits) length bs = long_bits =>
    ushortOfUlong (ulong bs) = ushort (suffix (bs, short_bits))

theorem ushortOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    ushortOfUllong (ullong bs) = ushort (suffix (bs, short_bits))

proof isa -verbatim
(* TODO add more *)
lemmas Conversions2 =
  C__ushortOfSint_def
  C__ushortOfSlong_def
  C__ushortOfSllong_def
  C__uintOfUlong_def
  C__uintOfUllong_def
  C__ulongOfUllong_def
  C__uintOfSlong_def
  C__uintOfSllong_def
  C__ulongOfSllong_def
  C__scharOfUshort_def
  C__scharOfUint_def
  C__scharOfUlong_def
  C__scharOfUllong_def
  C__ucharOfMathInt__1__obligation_refine_def
  C__ucharOfMathInt__1_def
  C__ushortOfMathInt__1__obligation_refine_def
  C__ushortOfMathInt__1_def
  C__uintOfMathInt__1__obligation_refine_def
  C__uintOfMathInt__1_def
  C__ulongOfMathInt__1__obligation_refine_def
  C__ulongOfMathInt__1_def
  C__ullongOfMathInt__1__obligation_refine_def
  C__ullongOfMathInt__1_def
  C__scharOfMathInt__1__obligation_refine_def
  C__scharOfMathInt__1_def
  C__sshortOfMathInt__1__obligation_refine_def
  C__sshortOfMathInt__1_def
  C__sintOfMathInt__1__obligation_refine_def
  C__sintOfMathInt__1_def
  C__slongOfMathInt__1__obligation_refine_def
  C__slongOfMathInt__1_def
  C__sllongOfMathInt__1__obligation_refine_def
  C__sllongOfMathInt__1_def
end-proof

theorem ushortOfSint_bit is
  fa(bs:Bits) length bs = int_bits =>
    ushortOfSint (sint bs) = ushort (suffix (bs, short_bits))

theorem ushortOfSlong_bit is
  fa(bs:Bits) length bs = long_bits =>
    ushortOfSlong (slong bs) = ushort (suffix (bs, short_bits))

theorem ushortOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    ushortOfSllong (sllong bs) = ushort (suffix (bs, short_bits))

theorem uintOfUlong_bit is
  fa(bs:Bits) length bs = long_bits =>
    uintOfUlong (ulong bs) = uint (suffix (bs, int_bits))

theorem uintOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    uintOfUllong (ullong bs) = uint (suffix (bs, int_bits))

theorem uintOfSlong_bit is
  fa(bs:Bits) length bs = long_bits =>
    uintOfSlong (slong bs) = uint (suffix (bs, int_bits))

theorem uintOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    uintOfSllong (sllong bs) = uint (suffix (bs, int_bits))

theorem ulongOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    ulongOfUllong (ullong bs) = ulong (suffix (bs, long_bits))

theorem ulongOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits =>
    ulongOfSllong (sllong bs) = ulong (suffix (bs, long_bits))

theorem scharOfUshort_bit is
  fa(bs:Bits) length bs = short_bits && ((toNat bs):Int) in? rangeOfSchar =>
    scharOfUshort (ushort bs) = schar (suffix (bs, CHAR_BIT))

theorem scharOfUint_bit is
  fa(bs:Bits) length bs = int_bits && ((toNat bs):Int) in? rangeOfSchar =>
    scharOfUint (uint bs) = schar (suffix (bs, CHAR_BIT))

theorem scharOfUlong_bit is
  fa(bs:Bits) length bs = long_bits && ((toNat bs):Int) in? rangeOfSchar =>
    scharOfUlong (ulong bs) = schar (suffix (bs, CHAR_BIT))

theorem scharOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits && ((toNat bs):Int) in? rangeOfSchar =>
    scharOfUllong (ullong bs) = schar (suffix (bs, CHAR_BIT))

proof isa -verbatim
(* TODO combine with Conversions2 *)
lemmas Conversions3 =
  C__scharOfSshort_def
  C__scharOfSint_def
  C__scharOfSlong_def
  C__scharOfSllong_def
  C__sshortOfUint_def
  C__sshortOfUlong_def
  C__sshortOfUllong_def
  C__sintOfUlong_def
  C__sintOfUllong_def
  C__slongOfUllong_def
end-proof

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
  fa(bs:Bits) length bs = int_bits && ((toNat bs):Int) in? rangeOfSshort =>
    sshortOfUint (uint bs) = sshort (suffix (bs, short_bits))

theorem sshortOfUlong_bit is
  fa(bs:Bits) length bs = long_bits && ((toNat bs):Int) in? rangeOfSshort =>
    sshortOfUlong (ulong bs) = sshort (suffix (bs, short_bits))

theorem sshortOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits && ((toNat bs):Int) in? rangeOfSshort =>
    sshortOfUllong (ullong bs) = sshort (suffix (bs, short_bits))

theorem sshortOfSint_bit is
  fa(bs:Bits) length bs = int_bits && toInt bs in? rangeOfSshort =>
    sshortOfSint (sint bs) = sshort (suffix (bs, short_bits))

theorem sshortOfSlong_bit is
  fa(bs:Bits) length bs = long_bits && toInt bs in? rangeOfSshort =>
    sshortOfSlong (slong bs) = sshort (suffix (bs, short_bits))

theorem sshortOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits && toInt bs in? rangeOfSshort =>
    sshortOfSllong (sllong bs) = sshort (suffix (bs, short_bits))

theorem sintOfUlong_bit is
  fa(bs:Bits) length bs = long_bits && ((toNat bs):Int) in? rangeOfSint =>
    sintOfUlong (ulong bs) = sint (suffix (bs, int_bits))

theorem sintOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits && ((toNat bs):Int) in? rangeOfSint =>
    sintOfUllong (ullong bs) = sint (suffix (bs, int_bits))

theorem sintOfSlong_bit is
  fa(bs:Bits) length bs = long_bits && toInt bs in? rangeOfSint =>
    sintOfSlong (slong bs) = sint (suffix (bs, int_bits))

theorem sintOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits && toInt bs in? rangeOfSint =>
    sintOfSllong (sllong bs) = sint (suffix (bs, int_bits))

theorem slongOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits && ((toNat bs):Int) in? rangeOfSlong =>
    slongOfUllong (ullong bs) = slong (suffix (bs, long_bits))

theorem slongOfSllong_bit is
  fa(bs:Bits) length bs = llong_bits && toInt bs in? rangeOfSlong =>
    slongOfSllong (sllong bs) = slong (suffix (bs, long_bits))

theorem charOfUshort_bit is
  fa(bs:Bits) length bs = short_bits && ((toNat bs):Int) in? rangeOfChar =>
    charOfUshort (ushort bs) = char (suffix (bs, CHAR_BIT))

theorem charOfUint_bit is
  fa(bs:Bits) length bs = int_bits && ((toNat bs):Int) in? rangeOfChar =>
    charOfUint (uint bs) = char (suffix (bs, CHAR_BIT))

theorem charOfUlong_bit is
  fa(bs:Bits) length bs = long_bits && ((toNat bs):Int) in? rangeOfChar =>
    charOfUlong (ulong bs) = char (suffix (bs, CHAR_BIT))

theorem charOfUllong_bit is
  fa(bs:Bits) length bs = llong_bits && ((toNat bs):Int) in? rangeOfChar =>
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


%subsection (* Integer Operators *)

(* The unary operator + [ISO 6.5.3.3/2] promotes [ISO 6.3.1.1/2] its integer
operand and leaves it unchanged. Because promotion turns every integer of
integer conversion rank [ISO 6.3.1.1/1] lower than sint/uint into sint or uint,
we only need to define versions of unary + for sint/uint and types of higher
rank. The C code generator should not generate casts for conversion ops that
carry out the needed promotions. The '_1' part of the name of the following ops
serves to distinguish them from those for binary +, defined later. *)

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

op -_1_sint (x:Sint | - mathIntOfSint x in? rangeOfSint) : Sint =
 sintOfMathInt (- mathIntOfSint x)

op -_1_slong (x:Slong | - mathIntOfSlong  x in? rangeOfSlong) : Slong =
 slongOfMathInt (- mathIntOfSlong x)

op -_1_sllong (x:Sllong | - mathIntOfSllong x in? rangeOfSllong) : Sllong =
 sllongOfMathInt (- mathIntOfSllong x)

op -_1_uint (x:Uint) : Uint =
 uintOfMathInt ((- mathIntOfUint x) modF (1 + UINT_MAX))

op -_1_ulong (x:Ulong ) : Ulong =
 ulongOfMathInt ((- mathIntOfUlong x) modF (1 + ULONG_MAX))

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
signed, the ops are defined only if the result can be represented in the type,
because otherwise the behavior is undefined [ISO 6.5/5].

There are 30 ops (5 operators times 6 integer types). We factor commonalities of
(subsets of) the 30 ops into a few parameterized ops that are suitably
instantiated to define the 30 ops. A key parameter is the (exact) arithmetic
operation carried out by each of the 5 operators. *)

type ArithOp = Int * Int -> Int

(* The Metaslang ops +, -, and * have type ArithOp and can be used to
instantiate the ArithOp parameter. The Metaslang ops divT and modT do not have
type ArithOp due to the subtype restriction that the divisor is not 0. Thus,
we define two versions that return 0 (an arbitrary value) when the divisor is
0.  As defined later, the divisor is never 0 when these ops are actually
used. *)

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

proof isa -verbatim
declare C__fitsSint_p_def [simp add]
declare C__fitsSlong_p_def [simp add]
declare C__fitsSllong_p_def [simp add]
end-proof

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

Note that we cannot use '%' in an op name because '%' starts an end-of-line
comment in Metaslang. So we use '//' instead. *)

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

proof isa -verbatim

(* TODO more like this *)
theorem mathIntOfSint_le [simp]:
  "\<lbrakk> C__Sint__subtype_pred x\<rbrakk> \<Longrightarrow> C__mathIntOfSint x \<le> 2147483647"
  apply(case_tac x, simp)
  done

theorem mathIntOfSlong_le [simp]:
  "\<lbrakk> C__Slong__subtype_pred x\<rbrakk> \<Longrightarrow> C__mathIntOfSlong x \<le> 9223372036854775807"
  apply(case_tac x, simp)
  done

theorem mathIntOfSllong_le [simp]:
  "\<lbrakk> C__Sllong__subtype_pred x\<rbrakk> \<Longrightarrow> C__mathIntOfSllong x \<le> 170141183460469231731687303715884105727"
  apply(case_tac x, simp)
  done


theorem mathIntOfUint_le [simp]:
  "\<lbrakk> C__Uint__subtype_pred x\<rbrakk> \<Longrightarrow> C__mathIntOfUint x \<le> 4294967295"
  apply(case_tac x, simp)
  done

theorem mathIntOfUlong_le [simp]:
  "\<lbrakk> C__Ulong__subtype_pred x\<rbrakk> \<Longrightarrow> C__mathIntOfUlong x \<le> 18446744073709551615"
  apply(case_tac x, simp)
  done

theorem mathIntOfUllong_le [simp]:
  "\<lbrakk> C__Ullong__subtype_pred x\<rbrakk> \<Longrightarrow> C__mathIntOfUllong x \<le> 340282366920938463463374607431768211455"
  apply(case_tac x, simp)
  done

end-proof

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

(* In order to define relational and equality operators, we introduce
conversions between Bool and Sint. *)

op boolOfSint (x:Sint) : Bool = (x ~= sint0) 
op sintOfBool (x:Bool) : Sint = if x then sint1 else sint0

proof isa -verbatim

theorem sint1_not_sint0 [simp]:
  "\<not> C__sint1 = C__sint0"
apply(simp add: C__sintOfBool_def C__boolOfSint_def C__sint1_def C__sint0_def)
  apply(auto)
  apply(cut_tac x="C__sintOfMathInt (1\<Colon>int)" and y="C__sintOfMathInt (0\<Colon>int)" in C__mathIntOfSint_injective)
  apply(force)
  apply(force)
  apply(cut_tac i=1 in C__mathIntOfSint_sintOfMathInt, force)
  apply(cut_tac i=0 in C__mathIntOfSint_sintOfMathInt, force)
  apply(simp)
  done
end-proof

theorem boolOfSint_sintOfBool is
  fa(x:Bool) boolOfSint (sintOfBool x) = x

%% This op will be used to wrap the condition of each if-then-else operation:
op test : Sint -> Bool = boolOfSint

%% TODO How can I restrict the application of this theorem to ifs for which the
%% condition is not already wrapped in a call to test (and also is not a call to
%% || or &&)?
theorem fixup_if_condition is [a]
  fa(condition:Bool, thenpart:a, elsepart:a)
    (if condition then thenpart else elsepart) = 
    (if test (sintOfBool condition) then thenpart else elsepart)

theorem sintOfBool_<= is
  fa(i:Int, j:Int) (i in? rangeOfUint && j in? rangeOfUint) => 
    (sintOfBool (i <= j)) = 
    ((uintOfMathInt i) <=_uint (uintOfMathInt j))

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


%subsection (* Array Operators *)

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


%subsection (* Structure Operators *)

(* Given the correspondence between Metaslang records and C structures described
earlier, field selections in Metaslang correspond exactly to structure member
expressions (i.e. .' operator) in C [ISO 6.5.2.3]. *)


%section (* State *)

%subsection (* Global Variables *)

(* Global variables are represented as fields of a Metaslang record type called
'Global' -- this name distinguishes this Metaslang record type from other
Metaslang record types that represent C structures.

For each field in type Global, the C code generator should generate a global
variable declaration [ISO 6.7] that includes an initializer that sets the
variable to a default value, as follows:

- if the variable has integer type, it is initialized to 0;

- if the variable has an array type, its elements are initialized to the default
  value for the array element type;

- if the variable has a structure type, each field is initialized to the deafult
  value for the field's type.

The Metaslang functions that correspond to C functions, as explained later, will
have a value of type Global single-threaded through them. This value gives
access to the global variables.

The Metaslang dotted field notation, applied to the value of type Global,
corresponds to a read access to the global variable. The C code generator will
perform this translation. *)


%subsection (* Local Variables *)

(* Metaslang 'let' expressions correspond to local variable declarations [ISO
6.7]. The pattern of the 'let' must be a single variable, and the expression
assigned to the variable becomes the initializer of the local variable. *)


%subsection (* State Monad *)

(* To facilitate the single threading of the record of global variables through
the functions, a state monad can be used. The following type is parameterized
over a type variable for the state. *)

type StateMonad(s,a) = s -> s * a

op [s,a] stateMonadReturn (x:a) : StateMonad(s,a) = fn s:s -> (s,x)

op [s,a,b]
 stateMonadBind (m:StateMonad(s,a), f: a -> StateMonad(s,b)) : StateMonad(s,b) =
  fn s:s -> let (s',x) = m s in f x s'

(* Given a specific record type Global (which varies for different C programs),
a monad type with return and bind operators should be defined as follows:

 type M a = StateMonad (Global, a)

 op [a] return (x:a) : M a = stateMonadReturn x

 op [a,b] monadBind (m:M a, f: a -> M b) : M b = stateMonadBind (m, f)

The choice of the name 'M' is motivated by brevity. The choice of the name
'monadBind' makes Metaslang's specialized monadic syntax available.

The C code generator should translate monadic assignments '... <- ...' into
local variables with initializers, similarly to the treatment of 'let'. *)


%subsection (* Assignments *)

(* Assignments to global variables are represented via Metaslang's record update
notation 'rec << {x = ...}'. Only one field at a time can be updated.

Monadic functions can be defined and used, e.g.

 op get_x : M T = fn s:Global -> (s, s.x)
 op set_x (x':T) : M () = fn s:Global -> (s << {x = x'}, ())
*)


%section (* Function Definitions *)

%subsection (* Functions without Side Effects *)

(* A Metaslang function of type T1 * ... * Tn -> T, where n >= 0 and the Ti's
and T are all Metaslang types that correspond to C types, corresponds to a
side-effect-free C function [ISO 6.7.6.3, 6.9.1] with the corresponding argument
and result types. The Metaslang function must have explicit argument names and
its body must only use Metaslang operators that correspond to C operators, as
described above. The C code generator should create a C function whose body
consists of a 'return' followed by the C expression that corresponds to the
Metaslang expression.

For example, the Metaslang function

 op f (x:Sshort) : Slong = slongOfSint (-_1_sint (sintOfSshort x))

corresponds to the C function

 long f(short x) { return (-x); }

Note that the C code generator should not generate casts that correspond to the
conversion ops because the short is automatically promoted to an int by virtue
of the unary - operation, and the resulting int is automatically converted to
the return type of the function (a long) as if by assignment [ISO 6.8.6.4/3].
Generating the cast would be correct, but makes the code less readable. *)


%subsection (* Functions with Side Effects *)

(* A Metaslang function of type Global * T1 * ... * Tn -> Global * T, where the
Ti's and T are as above, represents a function that may have side effects.  In
this case, the result type T is allowed to be (), which represents 'void'.

The Global value must be single-threaded. The function must have a form like

 let s = s << {x = a} in
 let s = s << {y = s.x +_sint (sintConstant 3 dec)} in
 (s, (sintConstant 2 dec) *_sint s.y)

The function can use the monadic type T1 * ... * Tn -> M T, which is isomorphic
to the type given above. The function must use monadic constructs (which ensure
single-threadedness) like

 {set_x a;
  x <- get_x;
  set_y (x +_sint (sintConstant 3 dec));
  y <- get_y;
  return ((sintConstant 2 dec) *_sint y)}

The C code generator could optimize away 'x <- get_x' and 'y <- get_y' (whose
only purpose is to extract the value of global variables from the state). The
non-monadic and monadic examples above are equivalent, and the C code generator
should translate both to something like

 x = a;
 y = x + 3;
 return 2 * y;

*)


%section (* Proofs *)

(*************************************************************************)

(* START OF PROOFS *)

(*************************************************************************)

proof isa C__ucharOfMathInt_mathIntOfUchar_Obligation_subtype
  apply (cut_tac x=x in C__uchar_range, force, force)
end-proof

proof isa C__sshortOfMathInt_mathIntOfSshort_Obligation_subtype
  apply (cut_tac x=x in C__sshort_range, force, force)
end-proof

proof isa C__sintOfMathInt_mathIntOfSint_Obligation_subtype
  apply (cut_tac x=x in C__sint_range, force, force)
end-proof

proof isa C__slongOfMathInt_mathIntOfSlong_Obligation_subtype
  apply (cut_tac x=x in C__slong_range, force, force)
end-proof

proof isa C__sllongOfMathInt_mathIntOfSllong_Obligation_subtype
  apply (cut_tac x=x in C__sllong_range, force, force)
end-proof

proof isa charOfMathInt_mathIntOfChar_Obligation_subtype 
  by (rule C__char_range)
end-proof

proof isa C__mathIntOfUchar_injective [simp]
  apply(case_tac x, case_tac y, simp)
end-proof

proof isa C__mathIntOfSchar_injective [simp]
  apply(auto simp add: C__mathIntOfSchar.simps)
  apply(case_tac x)
  apply(case_tac y)
  apply(simp)
end-proof

proof isa C__mathIntOfSshort_injective [simp]
  apply(auto simp add: C__mathIntOfSshort.simps)
  apply(case_tac x)
  apply(case_tac y)
  apply(simp)
end-proof

proof isa C__mathIntOfSint_injective [simp]
  apply(auto simp add: C__mathIntOfSint.simps)
  apply(case_tac x)
  apply(case_tac y)
  apply(simp)
end-proof

proof isa C__mathIntOfSlong_injective [simp]
  apply(auto simp add: C__mathIntOfSlong.simps)
  apply(case_tac x)
  apply(case_tac y)
  apply(simp)
end-proof

proof isa C__mathIntOfSllong_injective [simp]
  apply(auto simp add: C__mathIntOfSllong.simps)
  apply(case_tac x)
  apply(case_tac y)
  apply(simp)
end-proof

proof isa C__mathIntOfChar_injective [simp]
  apply(case_tac x)
  apply(case_tac y)
  apply(auto simp add: C__mathIntOfChar.simps)
end-proof

proof isa C__uchar_range [simp]
   apply(simp add: C__rangeOfUchar_def )
   apply(case_tac "x", simp)
end-proof

proof isa C__ushort_range [simp]
   apply(simp add: C__rangeOfUshort_def )
   apply(case_tac "x", simp)
end-proof

proof isa C__uint_range isa [simp]
   apply(simp add: C__rangeOfUint_def )
   apply(case_tac "x", simp)
end-proof

proof isa C__ulong_range [simp]
   apply(simp add: C__rangeOfUlong_def )
   apply(case_tac "x", simp)
end-proof

proof isa C__ullong_range [simp]
   apply(simp add: C__rangeOfUllong_def )
   apply(case_tac "x", simp)
end-proof

proof isa C__schar_range [simp]
   apply(simp add: C__rangeOfSchar_def  C__SCHAR_MIN_def C__SCHAR_MAX_def)
   apply(case_tac "x", simp)
end-proof

proof isa C__sshort_range [simp]
   apply(simp add: C__rangeOfSshort_def  C__SSHORT_MIN_def C__SSHORT_MAX_def)
   apply(case_tac "x", simp)
end-proof

proof isa C__sint_range [simp]
   apply(simp add: C__rangeOfSint_def  C__SINT_MIN_def C__SINT_MAX_def)
   apply(case_tac "x", simp)
end-proof

proof isa C__slong_range [simp]
   apply(simp add: C__rangeOfSlong_def  C__SLONG_MIN_def C__SLONG_MAX_def)
   apply(case_tac "x", simp)
end-proof

proof isa C__sllong_range [simp]
   apply(simp add: C__rangeOfSllong_def  C__SLLONG_MIN_def C__SLLONG_MAX_def)
   apply(case_tac "x", simp)
end-proof

proof isa char_range [simp]
   apply(simp add: C__rangeOfChar_def )
   apply(case_tac "x", simp)
end-proof

proof isa C__mathIntOfUchar_Obligation_subtype
  apply (auto simp add: List__ofLength_p_def List__nonEmpty_p_def C__CHAR_BIT_def) 
end-proof

proof isa C__ucharOfMathInt_Obligation_the
  apply(auto)
  apply(rule exI [of _ "C__uchar (toBits ((nat i), C__CHAR_BIT))"])
  apply(simp add:C__rangeOfUchar_def)
end-proof

proof isa C__ushortOfMathInt_Obligation_the
  apply(auto)
  apply(rule exI [of _ "C__ushort (toBits ((nat i), C__short_bits))"])
  apply(simp add:C__rangeOfUshort_def)
end-proof

proof isa C__uintOfMathInt_Obligation_the
  apply(auto)
  apply(rule exI [of _ "C__uint (toBits ((nat i), C__int_bits))"])
  apply(simp add:C__rangeOfUint_def)
end-proof

proof isa C__ulongOfMathInt_Obligation_the
  apply(auto)
  apply(rule exI [of _ "C__ulong (toBits ((nat i), C__long_bits))"])
  apply(simp add:C__rangeOfUlong_def)
end-proof

proof isa C__ullongOfMathInt_Obligation_the
  apply(auto)
  apply(rule exI [of _ "C__ullong (toBits ((nat i), C__llong_bits))"])
  apply(simp add:C__rangeOfUllong_def)
end-proof

proof isa C__scharOfMathInt_Obligation_the 
  apply (auto)
  apply (rule exI [of _ "C__schar (TwosComplement__tcNumber (i, C__CHAR_BIT))"])
  apply (simp add:C__rangeOfSchar_def)
end-proof

proof isa C__sshortOfMathInt_Obligation_the 
  apply (auto)
  apply (rule exI [of _ "C__sshort (TwosComplement__tcNumber (i, C__short_bits))"])
  apply (simp add:C__rangeOfSshort_def)
end-proof

proof isa C__sintOfMathInt_Obligation_the 
  apply (auto)
  apply (rule exI [of _ "C__sint (TwosComplement__tcNumber (i, C__int_bits))"])
  apply (simp add:C__rangeOfSint_def)
end-proof

proof isa C__slongOfMathInt_Obligation_the 
  apply (auto)
  apply (rule exI [of _ "C__slong (TwosComplement__tcNumber (i, C__long_bits))"])
  apply (simp add:C__rangeOfSlong_def)
end-proof

proof isa C__sllongOfMathInt_Obligation_the 
  apply (auto)
  apply (rule exI [of _ "C__sllong (TwosComplement__tcNumber (i, C__llong_bits))"])
  apply (simp add:C__rangeOfSllong_def)
end-proof

proof isa charOfMathInt_Obligation_the 
  apply (auto)
  apply (rule exI [of _ "C__char (if C__plainCharsAreSigned then  (TwosComplement__tcNumber (i, C__CHAR_BIT)) else (toBits ((nat i), C__CHAR_BIT)))"])
  apply (case_tac "C__plainCharsAreSigned")
  apply (simp add:C__rangeOfChar_def TwosComplement__tcNumber_length TwosComplement__rangeForLength_def  TwosComplement__toInt_tcNumber_reduce TwosComplement__rangeForLength_def TwosComplement__minForLength_def TwosComplement__maxForLength_def )
  apply (simp add:C__rangeOfChar_def  TwosComplement__toInt_tcNumber_reduce )
end-proof

proof isa C__mathIntOfUchar_ucharOfMathInt [simp]
  apply (auto simp add:C__ucharOfMathInt_def)
  apply(cut_tac i=i in C__ucharOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Uchar) . (C__Uchar__subtype_pred x \<and> int (C__mathIntOfUchar x) = i)" in theI')
  apply(auto)
end-proof

proof isa C__mathIntOfUshort_ushortOfMathInt [simp]
  apply (auto simp add:C__ushortOfMathInt_def)
  apply(cut_tac i=i in C__ushortOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Ushort) . (C__Ushort__subtype_pred x \<and> (C__mathIntOfUshort x) = i)" in theI')
  apply(auto)
end-proof

proof isa C__mathIntOfUint_uintOfMathInt [simp]
  apply (auto simp add:C__uintOfMathInt_def)
  apply(cut_tac i=i in C__uintOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Uint) . (C__Uint__subtype_pred x \<and> C__mathIntOfUint x = i)" in theI')
  apply(auto)
end-proof

proof isa C__mathIntOfUlong_ulongOfMathInt [simp]
  apply (auto simp add:C__ulongOfMathInt_def)
  apply(cut_tac i=i in C__ulongOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Ulong) . (C__Ulong__subtype_pred x \<and> (C__mathIntOfUlong x) = i)" in theI')
  apply(auto)
end-proof

proof isa C__mathIntOfUllong_ullongOfMathInt [simp]
  apply (auto simp add:C__ullongOfMathInt_def)
  apply(cut_tac i=i in C__ullongOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Ullong) . (C__Ullong__subtype_pred x \<and> (C__mathIntOfUllong x) = i)" in theI')
  apply(auto)
end-proof

proof isa C__mathIntOfSchar_scharOfMathInt [simp]
  apply (auto simp add:C__scharOfMathInt_def)
  apply(cut_tac i=i in C__scharOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Schar) . (C__Schar__subtype_pred x \<and> (C__mathIntOfSchar x) = i)" in theI')
  apply(auto)
end-proof

proof isa C__mathIntOfSshort_sshortOfMathInt [simp]
  apply (auto simp add:C__sshortOfMathInt_def)
  apply(cut_tac i=i in C__sshortOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Sshort) . (C__Sshort__subtype_pred x \<and> (C__mathIntOfSshort x) = i)" in theI')
  apply(auto)
end-proof

proof isa C__mathIntOfSint_sintOfMathInt [simp]
  apply (auto simp add:C__sintOfMathInt_def)
  apply(cut_tac i=i in C__sintOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Sint) . (C__Sint__subtype_pred x \<and> (C__mathIntOfSint x) = i)" in theI')
  apply(auto)
end-proof

proof isa C__mathIntOfSlong_slongOfMathInt [simp]
  apply (auto simp add:C__slongOfMathInt_def)
  apply(cut_tac i=i in C__slongOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Slong) . (C__Slong__subtype_pred x \<and> (C__mathIntOfSlong x) = i)" in theI')
  apply(auto)
end-proof

proof isa C__mathIntOfSllong_sllongOfMathInt [simp]
  apply (auto simp add:C__sllongOfMathInt_def)
  apply(cut_tac i=i in C__sllongOfMathInt_Obligation_the)
  apply(simp)
  apply(cut_tac P="\<lambda> (x::C__Sllong) . (C__Sllong__subtype_pred x \<and> (C__mathIntOfSllong x) = i)" in theI')
  apply(auto)
end-proof

proof isa C__ucharOfMathInt_mathIntOfUchar [simp]
  apply(cut_tac x = "C__ucharOfMathInt (int (C__mathIntOfUchar x))" and y = x in C__mathIntOfUchar_injective)
  apply(auto simp add: C__mathIntOfUchar_ucharOfMathInt_2)
end-proof

proof isa C__ushortOfMathInt_mathIntOfUshort [simp]
  apply(cut_tac x = "C__ushortOfMathInt (C__mathIntOfUshort x)" and y = x in C__mathIntOfUshort_injective)
  apply(auto simp add: C__mathIntOfUshort_ushortOfMathInt_2)
end-proof

proof isa C__uintOfMathInt_mathIntOfUint [simp]
  apply(cut_tac x = "C__uintOfMathInt (C__mathIntOfUint x)" and y = x in C__mathIntOfUint_injective)
  apply(auto simp add: C__mathIntOfUint_uintOfMathInt_2)
end-proof

proof isa C__ulongOfMathInt_mathIntOfUlong [simp]
  apply(cut_tac x = "C__ulongOfMathInt (C__mathIntOfUlong x)" and y = x in C__mathIntOfUlong_injective)
  apply(auto simp add: C__mathIntOfUlong_ulongOfMathInt_2)
end-proof

proof isa C__ullongOfMathInt_mathIntOfUllong [simp]
  apply(cut_tac x = "C__ullongOfMathInt (C__mathIntOfUllong x)" and y = x in C__mathIntOfUllong_injective)
  apply(auto simp add: C__mathIntOfUllong_ullongOfMathInt_2)
end-proof

proof isa C__scharOfMathInt_mathIntOfSchar [simp]
  apply(cut_tac x = "C__scharOfMathInt (C__mathIntOfSchar x)" and y = x in C__mathIntOfSchar_injective)
  apply(auto simp add: C__mathIntOfSchar_scharOfMathInt)
end-proof

proof isa C__sshortOfMathInt_mathIntOfSshort [simp]
  apply(cut_tac x = "C__sshortOfMathInt (C__mathIntOfSshort x)" and y = x in C__mathIntOfSshort_injective)
  apply(auto simp add: C__mathIntOfSshort_sshortOfMathInt)
end-proof

proof isa C__sintOfMathInt_mathIntOfSint [simp]
  apply(cut_tac x = "C__sintOfMathInt (C__mathIntOfSint x)" and y = x in C__mathIntOfSint_injective)
  apply(auto simp add: C__mathIntOfSint_sintOfMathInt)
end-proof

proof isa C__slongOfMathInt_mathIntOfSlong [simp]
  apply(cut_tac x = "C__slongOfMathInt (C__mathIntOfSlong x)" and y = x in C__mathIntOfSlong_injective)
  apply(auto simp add: C__mathIntOfSlong_slongOfMathInt)
end-proof

proof isa C__sllongOfMathInt_mathIntOfSllong [simp]
  apply(cut_tac x = "C__sllongOfMathInt (C__mathIntOfSllong x)" and y = x in C__mathIntOfSllong_injective)
  apply(auto simp add: C__mathIntOfSllong_sllongOfMathInt)
end-proof

proof isa charOfMathInt_mathIntOfChar [simp]
  apply(cut_tac x = "C__charOfMathInt (C__mathIntOfChar x)" and y = x in C__mathIntOfChar_injective)
  apply(auto simp add: C__mathIntOfChar_charOfMathInt)
  end-proof

proof isa C__ushortOfUchar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__uintOfUchar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__uintOfUshort_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__ulongOfUchar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__ulongOfUshort_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__ulongOfUint_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__ullongOfUchar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__ullongOfUshort_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__ullongOfUint_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__ullongOfUlong_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__sshortOfUchar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__sshortOfSchar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__sshortOfChar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__sintOfUchar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__sintOfSchar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__sintOfSshort_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__sintOfChar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__slongOfUchar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__slongOfSchar_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__slongOfSshort_Obligation_subtype
  apply(case_tac "x", simp)
end-proof

proof isa C__slongOfSint_Obligation_subtype 
  apply(case_tac "x", simp)
end-proof

proof isa C__slongOfChar_Obligation_subtype 
  apply(case_tac "x", simp)
end-proof

proof isa C__sllongOfUchar_Obligation_subtype 
  apply(case_tac "x", simp)
end-proof

proof isa C__sllongOfSchar_Obligation_subtype 
  apply(case_tac "x", simp)
end-proof

proof isa C__sllongOfSshort_Obligation_subtype 
  apply(case_tac "x", simp)
end-proof

proof isa C__sllongOfSint_Obligation_subtype 
  apply(case_tac "x", simp)
end-proof

proof isa C__sllongOfSlong_Obligation_subtype 
  apply(case_tac "x", simp)
end-proof

proof isa C__sllongOfChar_Obligation_subtype 
  apply(case_tac "x", simp)
end-proof

proof isa charOfUshort_Obligation_subtype
  apply(case_tac "x", auto)
end-proof

proof isa charOfSchar_Obligation_subtype
  apply(case_tac "x", auto)
end-proof

proof isa C__ucharOfSchar_bits
  apply(simp add: C__ucharOfSchar_def)
  apply(rule C__mathIntOfUchar_injective_fw)
  apply(force, force)
  apply(simp add:TwosComplement__toInt_def)
end-proof

proof isa C__ucharOfChar_bits
  apply(simp add: C__ucharOfChar_def)
  apply(auto)
  apply(rule C__mathIntOfUchar_injective_fw)
  apply(force, force)
  apply(simp add:TwosComplement__toInt_def)
  apply(cut_tac a="int (toNat bs)" and b = 256 in Divides.mod_pos_pos_trivial)
  apply(force, force)
  apply(simp del: mod_does_nothing_rewrite)
  apply(rule C__mathIntOfUchar_injective_fw)
  apply(force, force)
  apply(simp add:TwosComplement__toInt_def)
end-proof

proof isa C__mathIntOfUshort_injective [simp]
  apply(case_tac x, case_tac y, simp)
end-proof

proof isa C__mathIntOfUint_injective [simp]
  apply(case_tac x, case_tac y, simp)
end-proof

proof isa C__mathIntOfUlong_injective [simp]
  apply(case_tac x, case_tac y, simp)
end-proof

proof isa C__mathIntOfUllong_injective [simp]
  apply(case_tac x, case_tac y, simp)
end-proof

proof isa C__scharOfUchar_bits
  apply(simp add: C__scharOfUchar_def)
  apply(rule C__mathIntOfSchar_injective_fw)
  apply(force, force)
  apply(simp add:TwosComplement__toInt_def TwosComplement__nonNegative_p_def)
  apply(cut_tac bs=bs in not_negative_from_bound, force, force)
  apply(simp add:TwosComplement__nonNegative_p_def)
end-proof

proof isa C__scharOfChar_bits 
  apply(simp add: C__scharOfChar_def)
  apply(case_tac C__plainCharsAreSigned)
  apply(simp) 
  apply(rule C__mathIntOfSchar_injective_fw, force, force)
  apply(force)
  apply(simp)
  apply(rule C__mathIntOfSchar_injective_fw, force, force)
  apply(simp del:C__mathIntOfSchar_injective add: TwosComplement__toInt_def)
  apply(cut_tac bs=bs in not_negative_from_bound, force, force, force)
end-proof

proof isa C__charOfUchar_bits 
  apply(simp add: C__charOfUchar_def)
  apply(case_tac C__plainCharsAreSigned)
  apply(simp) 
  apply(rule C__mathIntOfChar_injective_fw, force, force)
  apply(simp del:C__mathIntOfSchar_injective add: TwosComplement__toInt_def)
  apply(cut_tac bs=bs in not_negative_from_bound, force, force, force)  
  apply(simp)
  apply(rule C__mathIntOfChar_injective_fw, force, force)
  apply(simp del:C__mathIntOfSchar_injective add: TwosComplement__toInt_def)
end-proof

proof isa C__charOfSchar_bits 
  apply(simp add: C__charOfSchar_def)
  apply(case_tac C__plainCharsAreSigned)
  apply(simp) 
  apply(rule C__mathIntOfChar_injective_fw, force, force)
  apply(simp del:C__mathIntOfChar_injective)
  apply(simp)
  apply(rule C__mathIntOfChar_injective_fw, force, force)
  apply(simp del:C__mathIntOfChar_injective)
  end-proof

proof isa C__ushortOfSshort_bits 
  apply(simp add: C__ushortOfSshort_def)
  apply(rule C__mathIntOfUshort_injective_fw, force, force)
  apply(simp del:C__mathIntOfChar_injective)
end-proof

proof isa C__sshortOfUshort_bits 
  apply(simp add: C__sshortOfUshort_def)
  apply(rule C__mathIntOfSshort_injective_fw)
  apply(force, force)
  apply(simp add:TwosComplement__toInt_def)
  apply(rule not_negative_from_bound_gen, force, force)
end-proof

proof isa C__uintOfSint_bits 
  apply(simp add: C__uintOfSint_def)
  apply(rule C__mathIntOfUint_injective_fw, force, force)
  apply(simp del:C__mathIntOfChar_injective)
end-proof

proof isa C__sintOfUint_bits 
  apply(simp add: C__sintOfUint_def)
  apply(rule C__mathIntOfSint_injective_fw)
  apply(force, force)
  apply(simp add:TwosComplement__toInt_def)
  apply(rule not_negative_from_bound_gen, force, force)
end-proof

proof isa C__ulongOfSlong_bits 
  apply(simp add: C__ulongOfSlong_def)
  apply(rule C__mathIntOfUlong_injective_fw, force, force)
  apply(simp del:C__mathIntOfChar_injective)
end-proof

proof isa C__slongOfUlong_bits 
  apply(simp add: C__slongOfUlong_def)
  apply(rule C__mathIntOfSlong_injective_fw)
  apply(force, force)
  apply(simp add:TwosComplement__toInt_def)
  apply(rule not_negative_from_bound_gen, force, force)
end-proof

proof isa C__ullongOfSllong_bits 
  apply(simp add: C__ullongOfSllong_def)
  apply(rule C__mathIntOfUllong_injective_fw, force, force)
  apply(simp del:C__mathIntOfChar_injective)
end-proof

proof isa C__sllongOfUllong_bits 
  apply(simp add: C__sllongOfUllong_def)
  apply(rule C__mathIntOfSllong_injective_fw)
  apply(force, force)
  apply(simp add:TwosComplement__toInt_def)
  apply(rule not_negative_from_bound_gen, force, force)
end-proof

proof isa C__ushortOfUchar_bits 
  apply(simp add: C__ushortOfUchar_def C__ushortOfMathInt__1__obligation_refine_def C__ushortOfMathInt__1_def)
  apply(rule toBits_toNat_extend, force, force)
end-proof

proof isa C__uintOfUchar_bits 
  apply(simp add: C__uintOfUchar_def C__uintOfMathInt__1__obligation_refine_def C__uintOfMathInt__1_def)
  apply(rule toBits_toNat_extend, force, force)
end-proof

proof isa C__ulongOfUchar_bits 
  apply(simp add: C__ulongOfUchar_def C__ulongOfMathInt__1__obligation_refine_def C__ulongOfMathInt__1_def)
  apply(rule toBits_toNat_extend, force, force)
end-proof

proof isa C__ullongOfUchar_bits 
  apply(simp add: C__ullongOfUchar_def C__ullongOfMathInt__1__obligation_refine_def C__ullongOfMathInt__1_def)
  apply(rule toBits_toNat_extend, force, force)
end-proof

proof isa C__uintOfUshort_bits 
  apply(simp add: C__uintOfUshort_def C__uintOfMathInt__1__obligation_refine_def C__uintOfMathInt__1_def)
  apply(rule toBits_toNat_extend, force, force)
end-proof

proof isa C__ulongOfUshort_bits 
  apply(simp add: C__ulongOfUshort_def C__ulongOfMathInt__1__obligation_refine_def C__ulongOfMathInt__1_def)
  apply(rule toBits_toNat_extend, force, force)
end-proof

proof isa C__ullongOfUshort_bits 
  apply(simp add: C__ullongOfUshort_def C__ullongOfMathInt__1__obligation_refine_def C__ullongOfMathInt__1_def)
  apply(rule toBits_toNat_extend, force, force)
end-proof

proof isa C__ulongOfUint_bits 
  apply(simp add: C__ulongOfUint_def C__ulongOfMathInt__1__obligation_refine_def C__ulongOfMathInt__1_def)
  apply(rule toBits_toNat_extend, force, force)
end-proof

proof isa C__ullongOfUint_bits 
  apply(simp add: C__ullongOfUint_def C__ullongOfMathInt__1__obligation_refine_def C__ullongOfMathInt__1_def)
  apply(rule toBits_toNat_extend, force, force)
end-proof

proof isa C__ullongOfUlong_bits 
  apply(simp add: C__ullongOfUlong_def C__ullongOfMathInt__1__obligation_refine_def C__ullongOfMathInt__1_def)
  apply(rule toBits_toNat_extend, force, force)
end-proof

proof isa C__ucharOfMathInt__1__obligation_refine_def
  apply(cut_tac x="(C__ucharOfMathInt i)" and y="C__uchar (toBits(nat i, C__CHAR_BIT))" in C__mathIntOfUchar_injective, force)
  apply(simp add: Bits__bits_length)
  apply(simp)
  apply(simp del:C__mathIntOfUchar_injective add:C__mathIntOfUchar_ucharOfMathInt_2 C__ucharOfMathInt__1_def)
end-proof

proof isa C__ushortOfMathInt__1__obligation_refine_def
  apply(cut_tac x="(C__ushortOfMathInt i)" and y="C__ushort (toBits(nat i, C__short_bits))" in C__mathIntOfUshort_injective, force)
  apply(simp add: Bits__bits_length)
  apply(simp)
  apply(simp del:C__mathIntOfUshort_injective add:C__mathIntOfUshort_ushortOfMathInt_2 C__ushortOfMathInt__1_def)
end-proof

proof isa C__uintOfMathInt__1__obligation_refine_def
  apply(cut_tac x="(C__uintOfMathInt i)" and y="C__uint (toBits(nat i, C__int_bits))" in C__mathIntOfUint_injective, force)
  apply(simp add: Bits__bits_length)
  apply(simp)
  apply(simp del:C__mathIntOfUint_injective add:C__mathIntOfUint_uintOfMathInt_2 C__uintOfMathInt__1_def)
end-proof

proof isa C__ulongOfMathInt__1__obligation_refine_def
  apply(cut_tac x="(C__ulongOfMathInt i)" and y="C__ulong (toBits(nat i, C__long_bits))" in C__mathIntOfUlong_injective, force)
  apply(simp add: Bits__bits_length)
  apply(simp)
  apply(simp del:C__mathIntOfUlong_injective add:C__mathIntOfUlong_ulongOfMathInt_2 C__ulongOfMathInt__1_def)
end-proof

proof isa C__ullongOfMathInt__1__obligation_refine_def
  apply(cut_tac x="(C__ullongOfMathInt i)" and y="C__ullong (toBits(nat i, C__llong_bits))" in C__mathIntOfUllong_injective, force)
  apply(simp add: Bits__bits_length)
  apply(simp)
  apply(simp del:C__mathIntOfUllong_injective add:C__mathIntOfUllong_ullongOfMathInt_2 C__ullongOfMathInt__1_def)
end-proof

proof isa C__ushortOfSchar_bits
  apply(simp add: C__ushortOfSchar_def C__ushortOfMathInt__1__obligation_refine_def C__ushortOfMathInt__1_def TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
end-proof

proof isa C__uintOfSchar_bits
  apply(simp add: C__uintOfSchar_def C__uintOfMathInt__1__obligation_refine_def C__uintOfMathInt__1_def TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
end-proof

proof isa C__ulongOfSchar_bits
  apply(simp add: C__ulongOfSchar_def C__ulongOfMathInt__1__obligation_refine_def C__ulongOfMathInt__1_def TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
end-proof

proof isa C__ullongOfSchar_bits
  apply(simp add: C__ullongOfSchar_def C__ullongOfMathInt__1__obligation_refine_def C__ullongOfMathInt__1_def TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
end-proof

proof isa C__uintOfSshort_bits
  apply(simp add: C__uintOfSshort_def C__uintOfMathInt__1__obligation_refine_def C__uintOfMathInt__1_def TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
end-proof

proof isa C__ulongOfSshort_bits
  apply(simp add: C__ulongOfSshort_def C__ulongOfMathInt__1__obligation_refine_def C__ulongOfMathInt__1_def TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
end-proof

proof isa C__ullongOfSshort_bits
  apply(simp add: C__ullongOfSshort_def C__ullongOfMathInt__1__obligation_refine_def C__ullongOfMathInt__1_def TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
end-proof

proof isa C__ulongOfSint_bits
  apply(simp add: C__ulongOfSint_def C__ulongOfMathInt__1__obligation_refine_def C__ulongOfMathInt__1_def TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
  end-proof

proof isa C__ullongOfSint_bits
  apply(simp add: C__ullongOfSint_def C__ullongOfMathInt__1__obligation_refine_def C__ullongOfMathInt__1_def TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
end-proof

proof isa C__ullongOfSlong_bits
  apply(simp add: C__ullongOfSlong_def C__ullongOfMathInt__1__obligation_refine_def C__ullongOfMathInt__1_def TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
end-proof

proof isa C__ushortOfChar_bits
  apply(simp add: C__ushortOfChar_def C__ushortOfMathInt__1__obligation_refine_def C__ushortOfMathInt__1_def)
  apply(case_tac "C__plainCharsAreSigned", simp_all)
  apply(simp add: TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
  (* done with goal 1 *)
  defer 1
  apply(simp add: toBits_toNat_extend Divides.mod_pos_pos_trivial)
end-proof

proof isa C__uintOfChar_bits
  apply(simp add: C__uintOfChar_def C__uintOfMathInt__1__obligation_refine_def C__uintOfMathInt__1_def)
  apply(case_tac "C__plainCharsAreSigned", simp_all)
  apply(simp add: TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
  (* done with goal 1 *)
  defer 1
  apply(simp add: toBits_toNat_extend Divides.mod_pos_pos_trivial)
end-proof

proof isa C__ulongOfChar_bits
  apply(simp add: C__ulongOfChar_def C__ulongOfMathInt__1__obligation_refine_def C__ulongOfMathInt__1_def)
  apply(case_tac "C__plainCharsAreSigned", simp_all)
  apply(simp add: TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
  (* done with goal 1 *)
  defer 1
  apply(simp add: toBits_toNat_extend Divides.mod_pos_pos_trivial)
end-proof

proof isa C__ullongOfChar_bits
  apply(simp add: C__ullongOfChar_def C__ullongOfMathInt__1__obligation_refine_def C__ullongOfMathInt__1_def)
  apply(case_tac "C__plainCharsAreSigned", simp_all)
  apply(simp add: TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs", simp_all)
  apply(simp add: Divides.mod_pos_pos_trivial toBits_toNat_extend TwosComplement__nonNegative_p_alt_def)
  apply(simp add: toBits_move)
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def toNat__signExtend_when_negative nat_move)
  apply(rule mod_known, force, force)
  apply(rule mod_same_lemma)
  apply(simp)
  (* done with goal 1 *)
  defer 1
  apply(simp add: toBits_toNat_extend Divides.mod_pos_pos_trivial)
end-proof

proof isa C__scharOfMathInt__1_Obligation_subtype1
  apply(simp only: List__ofLength_p_def C__short_bits_def C__sizeof_short_def C__CHAR_BIT_def)
  apply(rule TwosComplement__tcNumber_length)
  apply(simp only:)
  apply(simp add: rangeOfSchar_alt_def)
end-proof

proof isa C__scharOfMathInt__1_Obligation_subtype
  apply(auto simp add: rangeOfSchar_alt_def)
end-proof

proof isa C__scharOfMathInt__1__obligation_refine_def
  apply(cut_tac x="(C__scharOfMathInt i)" and y="C__schar (TwosComplement__tcNumber(i, C__CHAR_BIT))" in C__mathIntOfSchar_injective)
  apply(simp add: Bits__bits_length)
  apply(simp add: rangeOfSchar_alt_def)
  apply(simp del:C__mathIntOfSchar_injective add:C__mathIntOfSchar_scharOfMathInt C__scharOfMathInt__1_def rangeOfSchar_alt_def)
end-proof

(* was quite slow without the uses of only: *)
proof isa C__sshortOfMathInt__1_Obligation_subtype1
  apply(simp only: List__ofLength_p_def C__short_bits_def C__sizeof_short_def C__CHAR_BIT_def)
  apply(rule TwosComplement__tcNumber_length)
  apply(simp only:)
  apply(simp add: rangeOfSshort_alt_def)
end-proof

proof isa C__sshortOfMathInt__1_Obligation_subtype
  apply(auto simp add: rangeOfSshort_alt_def)
end-proof

proof isa C__sshortOfMathInt__1__obligation_refine_def
  apply(cut_tac x="(C__sshortOfMathInt i)" and y="C__sshort (TwosComplement__tcNumber(i, C__short_bits))" in C__mathIntOfSshort_injective)
  apply(simp add: Bits__bits_length)
  apply(simp add: rangeOfSshort_alt_def)
  apply(simp del:C__mathIntOfSshort_injective add:C__mathIntOfSshort_sshortOfMathInt C__sshortOfMathInt__1_def rangeOfSshort_alt_def)
end-proof

proof isa C__sintOfMathInt__1_Obligation_subtype1
  apply(simp only: List__ofLength_p_def C__int_bits_def C__sizeof_int_def C__CHAR_BIT_def)
  apply(rule TwosComplement__tcNumber_length)
  apply(simp only:)
  apply(simp add: rangeOfSint_alt_def)
end-proof

proof isa C__sintOfMathInt__1_Obligation_subtype
  apply(auto simp add: rangeOfSint_alt_def)
end-proof

proof isa C__sintOfMathInt__1__obligation_refine_def
  apply(cut_tac x="(C__sintOfMathInt i)" and y="C__sint (TwosComplement__tcNumber(i, C__int_bits))" in C__mathIntOfSint_injective)
  apply(simp add: Bits__bits_length)
  apply(simp add: rangeOfSint_alt_def)
  apply(simp del:C__mathIntOfSint_injective add:C__mathIntOfSint_sintOfMathInt C__sintOfMathInt__1_def rangeOfSint_alt_def)
end-proof

proof isa C__slongOfMathInt__1_Obligation_subtype1
  apply(simp only: List__ofLength_p_def C__long_bits_def C__sizeof_long_def C__CHAR_BIT_def)
  apply(rule TwosComplement__tcNumber_length)
  apply(simp only:)
  apply(simp add: rangeOfSlong_alt_def)
end-proof

proof isa C__slongOfMathInt__1_Obligation_subtype
  apply(auto simp add: rangeOfSlong_alt_def)
end-proof

proof isa C__slongOfMathInt__1__obligation_refine_def
  apply(cut_tac x="(C__slongOfMathInt i)" and y="C__slong (TwosComplement__tcNumber(i, C__long_bits))" in C__mathIntOfSlong_injective)
  apply(simp add: Bits__bits_length)
  apply(simp add: rangeOfSlong_alt_def)
  apply(simp del:C__mathIntOfSlong_injective add:C__mathIntOfSlong_slongOfMathInt C__slongOfMathInt__1_def rangeOfSlong_alt_def)
end-proof

proof isa C__sllongOfMathInt__1_Obligation_subtype1
  apply(simp only: List__ofLength_p_def C__llong_bits_def C__sizeof_llong_def C__CHAR_BIT_def)
  apply(rule TwosComplement__tcNumber_length)
  apply(simp only:)
  apply(simp add: rangeOfSllong_alt_def)
end-proof

proof isa C__sllongOfMathInt__1_Obligation_subtype
  apply(auto simp add: rangeOfSllong_alt_def)
end-proof

proof isa C__sllongOfMathInt__1__obligation_refine_def
  apply(cut_tac x="(C__sllongOfMathInt i)" and y="C__sllong (TwosComplement__tcNumber(i, C__llong_bits))" in C__mathIntOfSllong_injective)
  apply(simp add: Bits__bits_length)
  apply(simp add: rangeOfSllong_alt_def)
  apply(simp del:C__mathIntOfSllong_injective add:C__mathIntOfSllong_sllongOfMathInt C__sllongOfMathInt__1_def rangeOfSllong_alt_def)
end-proof

proof isa C__sshortOfUchar_bits
  apply(simp add:C__sshortOfUchar_def C__sshortOfMathInt__1__obligation_refine_def C__sshortOfMathInt__1_def TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__sintOfUchar_bits
  apply(simp add:C__sintOfUchar_def C__sintOfMathInt__1__obligation_refine_def C__sintOfMathInt__1_def TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__slongOfUchar_bits
  apply(simp add:C__slongOfUchar_def C__slongOfMathInt__1__obligation_refine_def C__slongOfMathInt__1_def TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__sllongOfUchar_bits
  apply(simp add:C__sllongOfUchar_def C__sllongOfMathInt__1__obligation_refine_def C__sllongOfMathInt__1_def TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__sintOfUshort_bits
  apply(simp add:C__sintOfUshort_def C__sintOfMathInt__1__obligation_refine_def C__sintOfMathInt__1_def TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__slongOfUshort_bits
  apply(simp add:C__slongOfUshort_def C__slongOfMathInt__1__obligation_refine_def C__slongOfMathInt__1_def TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__sllongOfUshort_bits
  apply(simp add:C__sllongOfUshort_def C__sllongOfMathInt__1__obligation_refine_def C__sllongOfMathInt__1_def TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__slongOfUint_bits
  apply(simp add:C__slongOfUint_def C__slongOfMathInt__1__obligation_refine_def C__slongOfMathInt__1_def TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__sllongOfUint_bits
  apply(simp add:C__sllongOfUint_def C__sllongOfMathInt__1__obligation_refine_def C__sllongOfMathInt__1_def TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__sllongOfUlong_bits
  apply(simp add:C__sllongOfUlong_def C__sllongOfMathInt__1__obligation_refine_def C__sllongOfMathInt__1_def TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__sshortOfChar_bits_unsigned
  apply(simp add: C__sshortOfChar_def C__plainCharsAreUnsigned_def C__sshortOfMathInt__1__obligation_refine_def C__sshortOfMathInt__1_def  TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__sintOfChar_bits_unsigned
  apply(simp add: C__sintOfChar_def C__plainCharsAreUnsigned_def C__sintOfMathInt__1__obligation_refine_def C__sintOfMathInt__1_def  TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__slongOfChar_bits_unsigned
  apply(simp add: C__slongOfChar_def C__plainCharsAreUnsigned_def C__slongOfMathInt__1__obligation_refine_def C__slongOfMathInt__1_def  TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__sllongOfChar_bits_unsigned
  apply(simp add: C__sllongOfChar_def C__plainCharsAreUnsigned_def C__sllongOfMathInt__1__obligation_refine_def C__sllongOfMathInt__1_def  TwosComplement__tcNumber__2__obligation_refine_def TwosComplement__tcNumber__2_def Divides.mod_pos_pos_trivial toBits_toNat_extend)
end-proof

proof isa C__sshortOfSchar_bits
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
  end-proof

proof isa C__sshortOfChar_bits_signed
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__sintOfSchar_bits
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__sintOfChar_bits_signed
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__sintOfSshort_bits
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__slongOfSchar_bits
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__slongOfChar_bits_signed
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__slongOfSshort_bits
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__slongOfSint_bits
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
  end-proof

proof isa C__sllongOfSchar_bits
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__sllongOfChar_bits_signed
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__sllongOfSshort_bits
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__sllongOfSint_bits
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__sllongOfSlong_bits
  apply(auto simp add: Conversions)
  apply(rule TwosComplement__toInt_inject_rule)
  defer 1
  apply(force, force)
  apply(simp add: TwosComplement__sign_extension_does_not_change_value TwosComplement__minForLength_def TwosComplement__maxForLength_def  del: TwosComplement__toInt_inject)
end-proof

proof isa C__ucharOfUshort_bit
  apply(simp add: C__ucharOfUshort_def C__ucharOfMathInt__1__obligation_refine_def C__ucharOfMathInt__1_def toNat_mod)
  apply(cut_tac n=8 and bs=bs in toBits_mod_toNat, force, force)
  apply(simp add: Divides.nat_mod_distrib)
end-proof

proof isa C__ucharOfUint_bit
  apply(simp add: C__ucharOfUint_def C__ucharOfMathInt__1__obligation_refine_def C__ucharOfMathInt__1_def toNat_mod)
  apply(cut_tac n=8 and bs=bs in toBits_mod_toNat, force, force)
  apply(simp add: Divides.nat_mod_distrib)
end-proof

proof isa C__ucharOfUlong_bit
  apply(simp add: C__ucharOfUlong_def C__ucharOfMathInt__1__obligation_refine_def C__ucharOfMathInt__1_def)
  apply(cut_tac n=8 and bs=bs in toBits_mod_toNat, force, force)
  apply(simp add: Divides.nat_mod_distrib)
end-proof

proof isa C__ucharOfUllong_bit
  apply(simp add: C__ucharOfUllong_def C__ucharOfMathInt__1__obligation_refine_def C__ucharOfMathInt__1_def)
  apply(cut_tac n=8 and bs=bs in toBits_mod_toNat, force, force)
  apply(simp add: Divides.nat_mod_distrib)
end-proof

proof isa C__ucharOfSshort_bit
  apply(simp add: C__ucharOfSshort_def C__ucharOfMathInt__1__obligation_refine_def C__ucharOfMathInt__1_def)
  apply(cut_tac n=8 and bs=bs in toBits_mod_toNat)
  apply(simp_all)
  end-proof

proof isa C__ucharOfSint_bit
  apply(simp add: C__ucharOfSint_def C__ucharOfMathInt__1__obligation_refine_def C__ucharOfMathInt__1_def)
  apply(cut_tac n=8 and bs=bs in toBits_mod_toNat)
  apply(simp_all)
end-proof

proof isa C__ucharOfSlong_bit
  apply(simp add: C__ucharOfSlong_def C__ucharOfMathInt__1__obligation_refine_def C__ucharOfMathInt__1_def)
  apply(cut_tac n=8 and bs=bs in toBits_mod_toNat)
  apply(simp_all)
end-proof

proof isa C__ucharOfSllong_bit
  apply(simp add: C__ucharOfSllong_def C__ucharOfMathInt__1__obligation_refine_def C__ucharOfMathInt__1_def)
  apply(cut_tac n=8 and bs=bs in toBits_mod_toNat)
  apply(simp_all)
end-proof

proof isa C__ushortOfUint_bit
  apply(simp add: C__ushortOfUint_def C__ushortOfMathInt__1__obligation_refine_def C__ushortOfMathInt__1_def)
  apply(cut_tac n=16 and bs=bs in toBits_mod_toNat, force, force)
  apply(simp add: Divides.nat_mod_distrib)
end-proof

proof isa C__ushortOfUlong_bit
  apply(simp add: C__ushortOfUlong_def C__ushortOfMathInt__1__obligation_refine_def C__ushortOfMathInt__1_def)
  apply(cut_tac n=16 and bs=bs in toBits_mod_toNat, force, force)
  apply(simp add: Divides.nat_mod_distrib)
end-proof

proof isa C__ushortOfUllong_bit
  apply(simp add: C__ushortOfUllong_def C__ushortOfMathInt__1__obligation_refine_def C__ushortOfMathInt__1_def)
  apply(cut_tac n=16 and bs=bs in toBits_mod_toNat, force, force)
  apply(simp add: Divides.nat_mod_distrib)
end-proof

proof isa C__ushortOfSint_bit
  apply(simp add: Conversions2)
  apply(cut_tac n=16 and bs=bs in toBits_mod_toNat)
  apply(simp_all)
end-proof

proof isa C__ushortOfSlong_bit
  apply(simp add: Conversions2)
  apply(cut_tac n=16 and bs=bs in toBits_mod_toNat)
  apply(simp_all)
end-proof

proof isa C__ushortOfSllong_bit
  apply(simp add: Conversions2)
  apply(cut_tac n=16 and bs=bs in toBits_mod_toNat)
  apply(simp_all)
end-proof

proof isa C__uintOfUlong_bit
  apply(simp add: Conversions2)
  apply(cut_tac n=32 and bs=bs in toBits_mod_toNat)
  apply(simp_all add: Divides.nat_mod_distrib)
end-proof

proof isa C__uintOfUllong_bit
  apply(simp add: Conversions2)
  apply(cut_tac n=32 and bs=bs in toBits_mod_toNat)
  apply(simp_all add: Divides.nat_mod_distrib)
end-proof

proof isa C__uintOfSlong_bit
  apply(simp add: Conversions2)
  apply(cut_tac n=32 and bs=bs in toBits_mod_toNat)
  apply(simp_all)
end-proof

proof isa C__uintOfSllong_bit
  apply(simp add: Conversions2)
  apply(cut_tac n=32 and bs=bs in toBits_mod_toNat)
  apply(simp_all)
end-proof

proof isa C__ulongOfUllong_bit
  apply(simp add: Conversions2)
  apply(cut_tac n=64 and bs=bs in toBits_mod_toNat)
  apply(simp_all add: Divides.nat_mod_distrib)
end-proof

proof isa C__ulongOfSllong_bit
  apply(simp add: Conversions2)
  apply(cut_tac n=64 and bs=bs in toBits_mod_toNat)
  apply(simp_all)
end-proof

proof isa C__scharOfUshort_bit
  apply(simp add: Conversions2)
  apply(rule TwosComplement__toInt_inject_rule)
  apply(simp_all add: TwosComplement__toInt_tcNumber_reduce)
  apply(simp add: TwosComplement__toInt_def TC_lemmas toNat_suffix)
end-proof

proof isa C__scharOfUint_bit
  apply(simp add: Conversions2)
  apply(rule TwosComplement__toInt_inject_rule)
  apply(simp_all add: TwosComplement__toInt_tcNumber_reduce)
  apply(simp add: TwosComplement__toInt_def TC_lemmas toNat_suffix)
end-proof

proof isa C__scharOfUlong_bit
  apply(simp add: Conversions2)
  apply(rule TwosComplement__toInt_inject_rule)
  apply(simp_all add: TwosComplement__toInt_tcNumber_reduce)
  apply(simp add: TwosComplement__toInt_def TC_lemmas toNat_suffix)
end-proof

proof isa C__scharOfUllong_bit
  apply(simp add: Conversions2)
  apply(rule TwosComplement__toInt_inject_rule)
  apply(simp_all add: TwosComplement__toInt_tcNumber_reduce)
  apply(simp add: TwosComplement__toInt_def TC_lemmas toNat_suffix)
end-proof

proof isa C__scharOfSshort_bit
  apply(simp add: Conversions2 Conversions3)
  apply(cut_tac bs=bs and n=8 in toInt_suffix, auto)
  apply(cut_tac x="List__suffix (bs, 8\<Colon>nat)" 
        in TwosComplement__tcNumber_toInt_reduce, auto)
end-proof

proof isa C__scharOfSint_bit
  apply(simp add: Conversions2 Conversions3)
  apply(cut_tac bs=bs and n=8 in toInt_suffix, auto)
  apply(cut_tac x="List__suffix (bs, 8\<Colon>nat)" 
        in TwosComplement__tcNumber_toInt_reduce, auto)
end-proof

proof isa C__scharOfSlong_bit
  apply(simp add: Conversions2 Conversions3)
  apply(cut_tac bs=bs and n=8 in toInt_suffix, auto)
  apply(cut_tac x="List__suffix (bs, 8\<Colon>nat)" 
        in TwosComplement__tcNumber_toInt_reduce, auto)
end-proof

proof isa C__scharOfSllong_bit
  apply(simp add: Conversions2 Conversions3)
  apply(cut_tac bs=bs and n=8 in toInt_suffix, auto)
  apply(cut_tac x="List__suffix (bs, 8\<Colon>nat)" 
        in TwosComplement__tcNumber_toInt_reduce, auto)
end-proof

proof isa C__sshortOfUint_bit
  apply(simp add: Conversions2 Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=16 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__sshortOfUlong_bit
  apply(simp add: Conversions2 Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=16 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__sshortOfUllong_bit
  apply(simp add: Conversions2 Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=16 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__sshortOfSint_bit
  apply(simp add: C__sshortOfSint_def Conversions2  Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=16 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__sshortOfSlong_bit
  apply(simp add: C__sshortOfSlong_def Conversions2  Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=16 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__sshortOfSllong_bit
  apply(simp add: C__sshortOfSllong_def Conversions2  Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=16 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__sintOfUlong_bit
  apply(simp add: Conversions2  Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=32 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__sintOfUllong_bit
  apply(simp add: Conversions2  Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=32 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)   
end-proof

proof isa C__sintOfSlong_bit
  apply(simp add: C__sintOfSlong_def Conversions2  Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=32 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__sintOfSllong_bit
  apply(simp add: C__sintOfSllong_def Conversions2  Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=32 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__slongOfUllong_bit
  apply(simp add: C__sintOfUllong_def Conversions2  Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=64 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__slongOfSllong_bit
  apply(simp add: C__slongOfSllong_def Conversions2  Conversions3)
  apply(rule TwosComplement__tcNumber_inverse_fwd [symmetric], auto)
  apply(cut_tac bs=bs and n=64 in toInt_suffix,
        auto simp add: TwosComplement__toInt_def TC_lemmas)
end-proof

proof isa C__charOfUshort_bit
by (simp add: C__charOfUshort_def C__plainCharsAreSigned_def charOfMathInt_suffix)
end-proof

proof isa C__charOfUint_bit
by (simp add: C__charOfUint_def C__plainCharsAreSigned_def charOfMathInt_suffix)
end-proof

proof isa C__charOfUlong_bit
by (simp add: C__charOfUlong_def C__plainCharsAreSigned_def charOfMathInt_suffix)
end-proof

proof isa C__charOfUllong_bit
by (simp add: C__charOfUllong_def C__plainCharsAreSigned_def charOfMathInt_suffix)
end-proof

proof isa C__charOfSshort_bit
apply (auto simp add: C__charOfSshort_def C__plainCharsAreSigned_def 
                 TwosComplement__toInt_def TC_lemmas charOfMathInt_suffix)
  apply (drule toNat_int_bound, auto)
end-proof

proof isa C__charOfSint_bit
apply (auto simp add: C__charOfSint_def C__plainCharsAreSigned_def 
                 TwosComplement__toInt_def TC_lemmas charOfMathInt_suffix)
  apply (drule toNat_int_bound, auto)
end-proof

proof isa C__charOfSlong_bit
apply (auto simp add: C__charOfSlong_def C__plainCharsAreSigned_def 
                 TwosComplement__toInt_def TC_lemmas charOfMathInt_suffix)
  apply (drule toNat_int_bound, auto)
end-proof

proof isa C__charOfSllong_bit
apply (auto simp add: C__charOfSllong_def C__plainCharsAreSigned_def 
                 TwosComplement__toInt_def TC_lemmas charOfMathInt_suffix)
  apply (drule toNat_int_bound, auto)
end-proof

proof isa C__e_gt_gt_sint_sint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sint_slong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sint_sllong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sint_uint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sint_ulong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sint_ullong_Obligation_subtype1
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_slong_sint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_slong_slong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_slong_sllong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_slong_uint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_slong_ulong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_slong_ullong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sllong_sint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sllong_slong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sllong_sllong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sllong_uint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sllong_ulong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_sllong_ullong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_uint_sint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(rule IsabelleExtensions.divT_pos_pos_le, force, force)
  apply(subst divT_is_div_if_non_neg)
  apply(force)
  apply(force)
  apply(rule zdiv_le_dividend_rule, force, force, force)
end-proof

proof isa C__e_gt_gt_uint_slong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_uint_sllong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_uint_uint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_uint_ulong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_uint_ullong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ulong_sint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ulong_slong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ulong_sllong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ulong_uint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ulong_ulong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ulong_ullong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ullong_sint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ullong_slong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ullong_sllong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ullong_uint_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ullong_ulong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__e_gt_gt_ullong_ullong_Obligation_subtype1
  apply(auto)
  apply(case_tac y, simp)
  apply(case_tac x, simp)
  apply(auto simp add:divT_pos)
  apply(rule zdiv_le_dividend_rule, simp_all)
end-proof

proof isa C__boolOfSint_sintOfBool
  apply(simp add: C__sintOfBool_def C__boolOfSint_def C__sint1_def C__sint0_def)
  apply(auto)
  apply(cut_tac x="C__sintOfMathInt (1\<Colon>int)" and y="C__sintOfMathInt (0\<Colon>int)" in C__mathIntOfSint_injective)
  apply(force)
  apply(force)
  apply(cut_tac i=1 in C__mathIntOfSint_sintOfMathInt, force)
  apply(cut_tac i=0 in C__mathIntOfSint_sintOfMathInt, force)
  apply(simp)
end-proof

proof isa C__fixup_if_condition
  apply(simp add: C__sintOfBool_def C__test_def C__boolOfSint_def)
end-proof

proof isa C__sintOfBool__lt_eq
  apply(auto simp add: C__sintOfBool_def C__e_lt_eq_uint_def C__compUint_def C__mathIntOfUint_uintOfMathInt_2)
end-proof

proof isa C__e_amp_sint_Obligation_exhaustive
  by (cut_tac C__Sint.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_amp_slong_Obligation_exhaustive
  by (cut_tac C__Slong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_amp_sllong_Obligation_exhaustive
  by (cut_tac C__Sllong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_amp_uint_Obligation_exhaustive
  by (cut_tac C__Uint.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_amp_ulong_Obligation_exhaustive
  by (cut_tac C__Ulong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_amp_ullong_Obligation_exhaustive
  by (cut_tac C__Ullong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_crt_sint_Obligation_exhaustive
  by (cut_tac C__Sint.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_crt_slong_Obligation_exhaustive
  by (cut_tac C__Slong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_crt_sllong_Obligation_exhaustive
  by (cut_tac C__Sllong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_crt_uint_Obligation_exhaustive
  by (cut_tac C__Uint.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_crt_ulong_Obligation_exhaustive
  by (cut_tac C__Ulong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_crt_ullong_Obligation_exhaustive
  by (cut_tac C__Ullong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_bar_sint_Obligation_exhaustive
  by (cut_tac C__Sint.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_bar_slong_Obligation_exhaustive
  by (cut_tac C__Slong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_bar_sllong_Obligation_exhaustive
  by (cut_tac C__Sllong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_bar_uint_Obligation_exhaustive
  by (cut_tac C__Uint.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_bar_ulong_Obligation_exhaustive
  by (cut_tac C__Ulong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__e_bar_ullong_Obligation_exhaustive
  by (cut_tac C__Ullong.nchotomy, 
      frule_tac x=x_1 in spec, drule_tac x=x_2 in spec, 
      auto)
end-proof

proof isa C__mathIntOfUint_Obligation_subtype0
  apply(auto simp add:  C__rangeOfUint_def)
end-proof

proof isa C__mathIntOfUshort_Obligation_subtype0
  apply(auto simp add:  C__rangeOfUshort_def)
end-proof

proof isa C__mathIntOfUlong_Obligation_subtype0
  apply(auto simp add:  C__rangeOfUlong_def)
end-proof

proof isa C__mathIntOfUllong_Obligation_subtype0
  apply(auto simp add:  C__rangeOfUllong_def)
end-proof

proof isa C__e_at_ushort_Obligation_subtype0
  apply( auto simp add: Int.nat_less_iff)
end-proof
proof isa C__e_at_uint_Obligation_subtype0
  apply( auto simp add: Int.nat_less_iff)
end-proof
proof isa C__e_at_ulong_Obligation_subtype0
  apply( auto simp add: Int.nat_less_iff)
end-proof
proof isa C__e_at_ullong_Obligation_subtype0
  apply( auto simp add: Int.nat_less_iff)
end-proof

proof isa mathIntOfUshort_non_neg [simp]
  apply(case_tac x, simp)
end-proof
proof isa mathIntOfUint_non_neg [simp]
  apply(case_tac x, simp)
end-proof
proof isa mathIntOfUlong_non_neg [simp]
  apply(case_tac x, simp)
end-proof
proof isa mathIntOfUllong_non_neg [simp]
  apply(case_tac x, simp)
end-proof

proof isa C__e_lt_lt_sint_sint_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sint_slong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sint_sllong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sint_uint_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sint_ulong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sint_ullong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_slong_sint_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_slong_slong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_slong_sllong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_slong_uint_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_slong_ulong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_slong_ullong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sllong_sint_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sllong_slong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sllong_sllong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sllong_uint_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sllong_ulong_Obligation_exhaustive
by auto
end-proof

proof isa C__e_lt_lt_sllong_ullong_Obligation_exhaustive
by auto
end-proof


endspec
