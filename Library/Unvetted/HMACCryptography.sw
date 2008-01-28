(*
2007:10:17
AC
A spec for HMAC.

ISSUE:
This spec should be parameterized over more hash functions than just
SHA-1/256/384/512.

*)


HMAC qualifying spec

  (* This spec formalizes the Keyed-Hash Message Authentication Code (HMAC)
  described in NIST's FIPS PUB 198, "The Keyed-Hash Message Authentication Code
  (HMAC)". In the comments in this spec, we refer to that document as "[FIPS]",
  possibly extended with references to (sub)sections, e.g. "[FIPS 3]". This spec
  is meant to be read in conjunction with [FIPS]: the comments in this spec are
  not meant to provide a self-contained of HMAC. *)

  import SHACryptography

  (* HMAC is parameterized over an arbitrary hash function. For now we only
  cover SHA-1, SHA-256, SHA-384, and SHA-512. In the future, we should extend
  this spec to cover arbitrary hash functions. For now, we the following type
  captures the SHA-v variants used in this spec. *)

  type SHAVariant = {v:Nat | v = 1 || v = 256 || v = 384 || v = 512}

  (* [FIPS] describes all data as byte sequences. However, since our library
  defines SHA ops on bit sequences, and also exclusive-or is defined on bit
  sequences in our library, it is more convenient, in this spec, to describe all
  data as bit sequences. *)

  % block size (in bits) of SHA variants (see library spec for SHA) [FIPS 2.3]:

  op B : SHAVariant -> Nat = fn
    | 1   ->  512
    | 256 ->  512
    | 384 -> 1024
    | 512 -> 1024

  % size (in bits) of output of SHA variants [FIPS 2.3]:

  op L : SHAVariant -> Nat = fn
    | 1   -> 160
    | 256 -> 256
    | 384 -> 384
    | 512 -> 512

  % inner and outer pads (depend on B and therefore on SHA variant) [FIPS 2.3]:

  op ipad (v:SHAVariant) : FSeq Bit =
    % construct sequence of B/8 0x36 bytes and flatten into B bits:
    flatten (repeat (toByte 0x36) ((B v) div 8))

  op opad (v:SHAVariant) : FSeq Bit =
    % construct sequence of B/8 0x5c bytes and flatten into B bits:
    flatten (repeat (toByte 0x5c) ((B v) div 8))

  (* An HMAC key is an arbitrary sequence of bytes [FIPS], which we model as an
  byte-aligned sequence of bits. It can have any length. We even allow the
  length to be 0; this would not make sense in practice but mathematically the
  operations below are still well defined. *)

  type Key = {K: FSeq Bit | length K rem 8 = 0}

  (* The following op captures HMAC computation [FIPS 5]. The length of the key
  must be at least L/2 [FIPS 3]; note that this constraint is expressed in the
  same way whether we measure sizes in bits or in bytes. The length of the text
  in bits must be less than 2^B - 8*B [FIPS 2.3], where B is measured in bytes,
  so the limit becomes 2^(B/8) - B if B is measured in bits. Since [FIPS]
  measures t in bytes, while here we measure it in bits, we require it to be a
  multiple of 8. In addition, it must be at least 4 bytes (= 4*8 bits) [FIPS 3].
  Also, t cannot exceed L; note that this constraint is expressed in the same
  way whether we measure the sizes in bits or in bytes. [FIPS 4] also says that
  t should be at least L/2, but allows an exception ("unless an application or
  protocol makes numerous trials impractical"); accordingly, we do not impose
  that constraint. All these constraints are expressed in the subtype. *)

  op hmac (v:SHAVariant, K:Key, text: FSeq Bit, t:Nat |
           length K >= (L v) div 2 &&
           length text < 2 ** ((B v) div 8) - (B v) &&
           t rem 8 = 0 &&
           4 * 8 <= t && t <= (L v)) : FSeq Bit =
    % abbreviation:
    let B = B v in
    % step 1:
    let K0 = if length K = B then
               K
    % step 2:
        else if length K > B then
               let hashedK = case v of
                   | 1   -> sha1   K
                   | 256 -> sha256 K
                   | 384 -> sha384 K
                   | 512 -> sha512 K in
               extendRight (hashedK, 0, B)
    % step 3:
        else (* length K > B *)
               extendRight (K, 0, B) in
    % steps 4-9:
    let step4 = K0 xor (ipad v) in
    let step5 = step4 ++ text in
    let step6 = case v of
                | 1   -> sha1   step5
                | 256 -> sha256 step5
                | 384 -> sha384 step5
                | 512 -> sha512 step5 in
    let step7 = K0 xor (opad v) in
    let step8 = step6 ++ step7 in
    let step9 = case v of
                | 1   -> sha1   step8
                | 256 -> sha256 step8
                | 384 -> sha384 step8
                | 512 -> sha512 step8 in
    % step 10:
    prefix (step9, t)

endspec
