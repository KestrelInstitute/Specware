(*
2007:07:28
AC
A spec for Abstract Syntax Notation One (ASN.1).

2007:10:01
AC
Added some encodings for DER and defined some BER encodings to coincide with
DER, with the precisation that they are only one of the possibilities allowed
by BER.

ISSUE:
This spec is very preliminary, it only contains very few concepts of ASN.1.
*)


ASN1 qualifying spec

  (* This is a very preliminary spec for Abstract Syntax Notation One (ASN.1).
  For now it only contains very few concepts of ASN.1, but it is of course
  amenable to expansion. *)

  import TwosComplementNumbers

  % there are four tag classes in ASN.1:

  type TagClass =
    | universal
    | application
    | contextSpecific
    | private

  % a tag includes an indication of whether a value is primitive or constructed:

  type TagForm =
    | primitive
    | constructed

  % encoding of tag according to Basic Encoding Rules (BER):

  op tagBER (class:TagClass, form:TagForm, tag:Nat) : FSeq Byte =
    % the first two bits encode the class as follows:
    let classBits: (FSeq Bit | ofLength? 2) =
        case class of
        | universal       -> single 0 <| 0
        | application     -> single 0 <| 1
        | contextSpecific -> single 1 <| 0
        | private         -> single 1 <| 1
        in
    % the third bit encodes the form as follows:
    let formBit:Bit =
        case form of
        | primitive   -> 0
        | constructed -> 1
        in
    % a tag that does not exceed 30 is encoded in the next 5 bits, which
    % together with the class and form bits form one byte:
    if tag <= 30 then
      single (classBits ++ formBit |> fromNat (tag, 5))
    else
    % a tag larger than 30 is encoded as a sequence of bytes:
      let tagBytes: NonEmptyFSeq Byte = the(tagBytes)
    % where the leftmost bit of each byte is 1:
          (fa(byte) byte in? tagBytes => first byte = 1) &&
    % and such that the concatenation of the 7-bit sequences obtained by
    % removing the lefmost bits from the bytes has the value of the tag,
    % i.e. the bytes have the form 1X 1Y ... (where X, Y, ... are 7-bit
    % sequences) and XY... is the tag in binary:
          toNat (flatten (map rtail tagBytes)) = tag &&
    % and the first byte is not 10000000 (i.e. we use the minimum number of
    % bytes to encode the tag:
          first tagBytes ~= (1 |> repeat 0 7) in
    % the bytes that encode the tag as defined above are preceded by one
    % byte that consists of the class bits, the form bit, and 11111:
      (classBits ++ formBit |> repeat 1 5) |> tagBytes

  % encoding of tag according to Distinguished Encoding Rules (DER):

  op tagDER : TagClass * TagForm * Nat -> FSeq Byte = tagBER

  % encoding of a short definite length in BER (length must not exceed 127):

  op shortDefiniteLengthBER (l:Nat | l <= 127) : FSeq Byte =
    % a single byte containing the length in binary (note that the leftmost
    % bit is 0):
    single (toByte l)

  % encoding of a long definite length in BER (length must not exceed
  % 256^126-1, which is a very large number):

  op longDefiniteLengthBER (l:Nat | l <= 256**126 - 1) : FSeq Byte =
    % the length is encoded in binary into the shortest possible sequence of
    % bytes (if the length is 0, we use a single 0 byte):
    let lenBytes: NonEmptyFSeq Byte = the(lenBytes)
        if l = 0 then
          lenBytes = single (toByte 0)
        else
          toNat (flatten lenBytes) = l &&
          first lenBytes ~= toByte 0
        in
    % the bytes that encode the length are preceded by one byte whose leftmost
    % bit is 1 and whose other 7 bits encode the number of bytes that encode
    % the length (which must not exceed 127, because of the 256^126-1 max; so
    % the first byte is not 11111111):
    let firstByte:Byte = 1 |> fromNat (length lenBytes, 7) in
    firstByte |> lenBytes

  % DER always encodes definite length (never indefinite length) in the minimum
  % number of bytes (so the length cannot exceed 256^126-1, see above):

  op lengthDER (l:Nat | l <= 256**126 - 1) : FSeq Byte =
    if l <= 127 then shortDefiniteLengthBER l
                else  longDefiniteLengthBER l

  % encoding of an integer in DER:

  op integerDER (i:Integer |
                 (* The integer is encoded in TLV (tag-length-value) format,
                 where V encodes the integer itself, T tags it, and L encodes
                 the length of V. As defined below, V is simply the two's
                 complement binary representation of the integer. Since for L we
                 can only use a short or long definite length as defined above,
                 the number of bytes that comprise V cannot exceed 256^126-1. In
                 other words, the number of bits that comprise V cannot exceed
                 8*(256^126-1). In n bits, we can represent two's complement
                 numbers from 2^(n-1) inclusive to 2^(n-1) exclusive. *)
                 let maxLength = 8 * (256**126-1) in
                 -2**(maxLength-1) <= i && i < 2**(maxLength-1)) : FSeq Byte =
    % convert i to two's complement number:
    let tc:TCNumber = fromInteger i in
    % since we want to use a whole number of bytes, we need to align the two's
    % complement number, by sign-extending it to make its length a multiple of
    % 8 (if it is already a multiple of 8, no sign extension takes place):
    let alignedLengthOfTC = (((length tc - 1) div 8) + 1) * 8 in
    let alignedTC = signExtend (tc, alignedLengthOfTC) in
    % group bits of (byte-aligned) two's complement number into bytes:
    let valueBytes: FSeq Byte = the(valueBytes)
        flatten valueBytes = alignedTC in
    % (T) tag for integers:
    tagDER (universal, primitive, 2) ++
    % (L) length:
    lengthDER (length valueBytes) ++
    % (V) actual integer:
    valueBytes

  % encoding of an octet string in DER:

  op octetStringDER (octs: FSeq Byte | length octs <= 256**126 - 1)
                    : FSeq Byte =
    % (T) tag for octet strings:
    tagDER (universal, primitive, 4) ++
    % (L) length:
    lengthDER (length octs) ++
    % (V) the octects themselves
    octs

  % encoding of a sequence in DER (we assume that each element of the argument
  % sequence is the DER encoding of some value of the sequence):

  op sequenceDER (elements: FSeq (FSeq Byte) |
                  % we can only encode short and long definite lengths:
                  length (flatten elements) <= 256**126-1) : FSeq Byte =
    % reduce all elements into one byte sequence:
    let flatElements = flatten elements in
    % (T) tag for sequences:
    tagBER (universal, constructed, 16) ++
    % (L) length:
    lengthDER (length flatElements) ++
    % (V) elements:
    flatElements

  (* BER encoding includes DER encoding, plus others. For now, we define the
  following BER encodings to coincide with the DER encodings. Eventually we will
  generalize this spec to cover all the other possibilities. *)

  % encoding of an integer in BER:

  op integerBER : {i:Integer | let maxLength = 8 * (256**126-1) in
                               -2**(maxLength-1) <= i && i < 2**(maxLength-1)}
                  -> FSeq Byte = integerDER

  % encoding of an octet string in BER:

  op octetStringBER : {octs: FSeq Byte | length octs <= 256**126 - 1}
                      -> FSeq Byte = octetStringDER

  % encoding of a sequence in BER (we assume that each element of the argument
  % sequence is the BER encoding of some value of the sequence):

  op sequenceBER : {elements: FSeq (FSeq Byte) |
                    length (flatten elements) <= 256**126 - 1} -> FSeq Byte =
    sequenceDER

endspec
