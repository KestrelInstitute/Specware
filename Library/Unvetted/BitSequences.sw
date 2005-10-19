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

ISSUE:
There should probably be additional conversions among nibbles, bytes, and
words.

*)


BitSeq qualifying spec

  import Bits, /Library/General/FiniteSequences

  % bitwise logical operations:

  op not : FSeq Bit -> FSeq Bit
  def not bs = map not bs

  op and infixl 25 : ((FSeq Bit * FSeq Bit) | equiLong) -> FSeq Bit
  def and (bs1,bs2) = map2 (and) (bs1, bs2)

  op ior infixl 24 : ((FSeq Bit * FSeq Bit) | equiLong) -> FSeq Bit
  def ior (bs1,bs2) = map2 (ior) (bs1, bs2)

  op xor infixl 24 : ((FSeq Bit * FSeq Bit) | equiLong) -> FSeq Bit
  def xor (bs1,bs2) = map2 (xor) (bs1, bs2)

  op nand infixl 25 : ((FSeq Bit * FSeq Bit) | equiLong) -> FSeq Bit
  def nand (bs1,bs2) = map2 (nand) (bs1, bs2)

  op nor infixl 24 : ((FSeq Bit * FSeq Bit) | equiLong) -> FSeq Bit
  def nor (bs1,bs2) = map2 (nor) (bs1, bs2)

  % nibbles, bytes, and words (since the size of words is not very standard,
  % we introduce different types with explicit sizes in their names):

  type Nibble = {bs : FSeq Bit | length bs = 4}
  type Byte   = {bs : FSeq Bit | length bs = 8}
  type Word16 = {bs : FSeq Bit | length bs = 16}
  type Word32 = {bs : FSeq Bit | length bs = 32}
  type Word64 = {bs : FSeq Bit | length bs = 64}

  op byteToNibbles : Byte -> Nibble * Nibble
  def byteToNibbles = inverse (fn(nib1,nib2) -> nib1 ++ nib2)

  op word16ToBytes : Word16 -> Byte * Byte
  def word16ToBytes = inverse (fn(byt1,byt2) -> byt1 ++ byt2)

  op word32ToBytes : Word32 -> Byte * Byte * Byte * Byte
  def word32ToBytes =
    inverse (fn(byt1,byt2,byt3,byt4) -> byt1 ++ byt2 ++ byt3 ++ byt4)

  op word64ToBytes :
     Word64 -> Byte * Byte * Byte * Byte * Byte * Byte * Byte * Byte
  def word64ToBytes =
    inverse (fn(byt1,byt2,byt3,byt4,byt5,byt6,byt7,byt8) ->
                byt1 ++ byt2 ++ byt3 ++ byt4 ++ byt5 ++ byt6 ++ byt7 ++ byt8)

  % convert bit sequence to byte sequence
  % (bit sequence length must be multiple of 8):

  op bitsToBytes : {bits : FSeq Bit | (length bits) rem 8 = 0} -> FSeq Byte
  def bitsToBytes bits = the(bytes) (flatten bytes = bits)

  % relationship with natural numbers (big endian; for little endian, reverse):

  op toNat : FSeq Bit -> Nat
  def toNat bs =
    if bs = empty then 0
    else toNat (ltail bs) * 2 + last bs

endspec
