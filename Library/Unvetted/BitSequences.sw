(* $Id$ *)

(*
2005:03:18
AC
This spec defines bit sequences, in particular bytes, nibble, and words of
various sizes, along with some conversions between these. It also includes
bitwise logical operations over sequences of the same length. It also defines
a conversion to natural numbers in the obvious way, according to the big
endian order.

2005:10:19
AC
Added conversion from bit sequences to byte sequences.

2005:11:02
AC
Added conversions from natural numbers to bit sequences.

2006:11:11
AC
Changed definition of subtypes to use predicate ofLength?, newly introduced in
the library spec for finite sequences.

2007:06:30
AC
Added sum of bit sequences as unsigned numbers in modular arithmetic.

ISSUE:
There should probably be additional conversions among nibbles, bytes, and
words.
*)


BitSeq qualifying spec

  import Bits, IntegerExt, /Library/General/FiniteSequences

  % bitwise logical operations:

  op not (bs: FSeq Bit) : FSeq Bit = map not bs

  op and (bs1: FSeq Bit, bs2:FSeq Bit | bs1 equiLong bs2) infixl 25 : FSeq Bit =
    map2 (and) (bs1, bs2)

  op ior (bs1: FSeq Bit, bs2:FSeq Bit | bs1 equiLong bs2) infixl 24 : FSeq Bit =
    map2 (ior) (bs1, bs2)

  op xor (bs1: FSeq Bit, bs2:FSeq Bit | bs1 equiLong bs2) infixl 24 : FSeq Bit =
    map2 (xor) (bs1, bs2)

  op nand (bs1: FSeq Bit, bs2:FSeq Bit | bs1 equiLong bs2) infixl 25 : FSeq Bit =
    map2 (nand) (bs1, bs2)

  op nor (bs1: FSeq Bit, bs2:FSeq Bit | bs1 equiLong bs2) infixl 24 : FSeq Bit =
    map2 (nor) (bs1, bs2)

  % nibbles, bytes, and words (since the size of words is not very standard,
  % we introduce different types with explicit sizes in their names):

  type Nibble = (FSeq Bit | ofLength? 4)
  type Byte   = (FSeq Bit | ofLength? 8)
  type Word16 = (FSeq Bit | ofLength? 16)
  type Word32 = (FSeq Bit | ofLength? 32)
  type Word64 = (FSeq Bit | ofLength? 64)

  op byteToNibbles : Byte -> Nibble * Nibble =
    inverse (fn(nib1,nib2) -> nib1 ++ nib2)

  op word16ToBytes : Word16 -> Byte * Byte =
    inverse (fn(byt1,byt2) -> byt1 ++ byt2)

  op word32ToBytes : Word32 -> Byte * Byte * Byte * Byte =
    inverse (fn(byt1,byt2,byt3,byt4) -> byt1 ++ byt2 ++ byt3 ++ byt4)

  op word64ToBytes : Word64 ->
                     Byte * Byte * Byte * Byte * Byte * Byte * Byte * Byte =
    inverse (fn(byt1,byt2,byt3,byt4,byt5,byt6,byt7,byt8) ->
                byt1 ++ byt2 ++ byt3 ++ byt4 ++ byt5 ++ byt6 ++ byt7 ++ byt8)

  % convert bit sequence to byte sequence
  % (bit sequence length must be multiple of 8):

  op bitsToBytes (bits: FSeq Bit | (length bits) rem 8 = 0) : FSeq Byte =
    the(bytes) (flatten bytes = bits)

  % relationship with natural numbers (big endian; for little endian, reverse):

  op toNat (bs: FSeq Bit) : Nat = if bs = empty then 0
                                  else toNat (ltail bs) * 2 + last bs

  op fromNat (n:Nat, len:Nat | n < 2 ** len) : FSeq Bit =
    the(bs) length bs = len && toNat bs = n

  op toNibble (n:Nat | n < 2 ** 4) : Nibble = fromNat (n, 4)

  op toByte   (n:Nat | n < 2 ** 8) : Byte   = fromNat (n, 8)

  op toWord16 (n:Nat | n < 2 ** 16) : Word16 = fromNat (n, 16)

  op toWord32 (n:Nat | n < 2 ** 32) : Word32 = fromNat (n, 32)

  op toWord64 (n:Nat | n < 2 ** 64) : Word64 = fromNat (n, 64)

  % add bit sequences of same length as unsigned numbers (in modular
  % arithmetic):

  op PLUS ((bs1,bs2) : (FSeq Bit * FSeq Bit | equiLong)) infixl 25 : FSeq Bit =
    let n = length bs1 (* = length bs2 *) in
    fromNat ((toNat bs1 + toNat bs2) rem 2 ** n, n)

endspec
