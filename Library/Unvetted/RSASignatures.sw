(*
2007:10:02
AC
A spec for RSA signatures.

2007:10:12
AC
Added SHA-256/384/512 variants.

ISSUE:
More signatures should be formalized.

*)


RSA qualifying spec

  (* The intent of this spec is to formalize various RSA signature schemes. For
  now, it only formalizes one, namely RSASSA-PKCS1-v1_5 as officially specified
  in the document "PKCS #1 v2.1: RSA Cryptography Standard" by RSA Labs. In the
  comments in this spec, We refer to that document as "[PKCS1]", possibly
  extended with reference to (sub)sections, e.g. "[PKCS1 9.2]". *)

  import RSACryptography, SHACryptography, AbstractSyntaxNotationOne

  % SHA-v variants used in this spec:

  type SHAVariant = {v:Nat | v = 1 || v = 256 || v = 384 || v = 512}

  % DER encoding of SHA algorithm identifiers [PKCS1 9.2]:

  op algIdDERsha : SHAVariant -> FSeq Byte = fn
    | 1   -> map toByte (empty <| 0x30 <| 0x21 <| 0x30 <| 0x09 <| 0x06
                               <| 0x05 <| 0x2b <| 0x0e <| 0x03 <| 0x02
                               <| 0x1a <| 0x05 <| 0x00 <| 0x04 <| 0x14)
    | 256 -> map toByte (empty <| 0x30 <| 0x31 <| 0x30 <| 0x0d <| 0x06
                               <| 0x09 <| 0x60 <| 0x86 <| 0x48 <| 0x01
                               <| 0x65 <| 0x03 <| 0x04 <| 0x02 <| 0x01
                               <| 0x05 <| 0x00 <| 0x04 <| 0x20)
    | 384 -> map toByte (empty <| 0x30 <| 0x41 <| 0x30 <| 0x0d <| 0x06
                               <| 0x09 <| 0x60 <| 0x86 <| 0x48 <| 0x01
                               <| 0x65 <| 0x03 <| 0x04 <| 0x02 <| 0x02
                               <| 0x05 <| 0x00 <| 0x04 <| 0x30)
    | 512 -> map toByte (empty <| 0x30 <| 0x51 <| 0x30 <| 0x0d <| 0x06
                               <| 0x09 <| 0x60 <| 0x86 <| 0x48 <| 0x01
                               <| 0x65 <| 0x03 <| 0x04 <| 0x02 <| 0x03
                               <| 0x05 <| 0x00 <| 0x04 <| 0x40)

  (* The following op formalizes the encoding method specified in [PKCS1 9.2],
  assuming that the hash function is a SHA variant (in the future, we could add
  similar ops for different hash functions, or better we could generalize this
  op to take a hash function as parameter). We model the possible occurrence of
  errors via Option (so we do not distinguish among different errors for
  now). We use the same symbols used in [PKCS1 9.2]. *)

  op encodePKCS15sha
     (v:SHAVariant) (M: FSeq Byte, emLen:Nat) : Option (FSeq Byte) =
    % since the SHA ops defined in our library operate on bits, we flatten bytes
    % to bits first:
    let M = flatten M in
    % error if "message too long" for the SHA variant:
    let maxSize:Nat = if      v = 1   || v = 256 then 2**64-1
                      else (* v = 384 || v = 512 *)   2**128-1 in
    if length M > maxSize then None else
    % apply hash (SHA variant):
    let H = case v of 1   -> sha1   M
                    | 256 -> sha256 M
                    | 384 -> sha384 M
                    | 512 -> sha512 M in
    % since the SHA ops defined in our library returns bits, we group them into
    % bytes:
    let H = bitsToBytes H in
    % encode DigestInfo with DER:
    let T = sequenceDER (empty <| algIdDERsha v <| octetStringDER H) in
    % error if "intended encoded message length too short":
    let tLen = length T in
    if emLen < tLen + 11 then None else
    % output:
    let PS = repeat (toByte 0xff) (emLen - tLen - 3) in
    let EM = toByte 0x00 |> toByte 0x01 |> PS <| toByte 0x00 ++ T in
    Some EM

  (* The following op formalizes the signature generation operation specified in
  [PKCS1 8.2.1], assuming that the hash function is a SHA variant (in the
  future, we could add similar ops for different hash functions, or better we
  could generalize this op to take a hash function as parameter). We model the
  possible occurrence of errors via Option (so we do not distinguish among
  different errors for now). We use the same symbols used in [PKCS1 8.2.1]. We
  include the length of the modulus k as an extra explicit parameter, for
  greater flexibility (so that we can also deal with perhaps "degenerate" moduli
  whose most significant byte is 0, which may happen in actual implementations).
  However, we require the modulus to fit the given length. We also require the
  modulus to be non-zero, so that the key can be applied. *)

  op signPKCS15sha
     (v:SHAVariant)
     (K:Key, k:Nat, M: FSeq Byte | nonZeroModulus? K && K.modulus <= 256**k)
     : Option (FSeq Byte) =
    % encode message first, propagating any encoding error (since we only
    % formalize one kind of error, we need not formalize the conversion of
    % the "intended encoded message length too short" into "RSA modulus too
    % short"):
    case encodePKCS15sha v (M, k) of
    | None -> None
    | Some EM ->
    % apply key to encoded message:
      let m = toNat (flatten EM) in
      let s = apply K m in
      let S = bitsToBytes (fromNat (s, k*8)) in
      Some S

  (* The following op formalizes the signature verification operation specified
  in [PKCS1 8.2.2], assuming that the hash function is a SHA variant (in the
  future, we could add similar ops for different hash functions, or better we
  could generalize this op to take a hash function as parameter). We model the
  possible occurrence of errors via Option (so we do not distinguish among
  different errors for now). We use the same symbols used in [PKCS1 8.2.2]. We
  include the length of the modulus k as an extra explicit parameter, for
  greater flexibility (so that we can also deal with perhaps "degenerate" moduli
  whose most significant byte is 0, which may happen in actual implementations).
  However, we require the modulus to fit the given length. We also require the
  modulus to be non-zero, so that the key can be applied. *)

  op verifyPKCS15sha
     (v:SHAVariant)
     (K:Key, k:Nat, M: FSeq Byte, S: FSeq Byte |
      nonZeroModulus? K && K.modulus <= 256**k) : Option Boolean =
    % invalid signature if S is not k octets long:
    if k ~= length S then Some false else
    % apply key to signature, obtaining encoded message:
    let s = toNat (flatten S) in
    let m = apply K s in
    let EM = bitsToBytes (fromNat (m, k*8)) in
    % encode message and compare with the one obtained from the signature,
    % propagating any encoding errors (since we only formalize one kind of
    % error, we need not formalize the conversion of the "intended encoded
    % message length too short" into "RSA modulus too short"):
    case encodePKCS15sha v (M, k) of
    | None -> None
    | Some EM' -> Some (EM' = EM)

endspec
