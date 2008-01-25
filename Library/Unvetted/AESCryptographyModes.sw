(*
2007:07:15
AC
A spec for ECB and CBC modes of operation for AES.

ISSUE:
Other modes should be added (e.g. CFB, OFB).

*)


AES qualifying spec

  (* We extend basic AES cryptography with AES modes of operations. These are
  all instances of block cipher modes that are specified generically in spec
  BlockCipherModes. In order to instantiate that generic spec to AES, we need to
  set the block size and to pass the appropriate block encryption/decryption
  functions to the generic data encryption/decryption functions defined in spec
  BlockCipherModes.

  In order to set the block size, we simply import spec BlockCipherModes and add
  a def for the uninterpreted op blockSize. This is fine because spec
  BlockCipherModes does not put any constraints on op blockSize other than its
  type. If there were constraints expressed as axioms, then a better way to set
  the block size is via spec substitution: the subspec of spec BlockCipherModes
  that consists of the declaration of op blockSize along with all its
  constraining axioms would be replaced with a spec that defines op blockSize.
  The morphism used for the substitution would have associated proof obligations
  ensuring (once discharged) that the definition supplied for op blockSize
  satisfies all the constraints states in spec BlockCipherModes. If we just
  added a def instead, no proof obligation would be generated and the def might
  fail to satisfy some of the constraining axioms, resulting in an inconsistent
  spec. However, in this particular case, there are no constraining axioms and
  so we avoid the verbosity of spec substitution and just add a def. Actually,
  in the future we may extend Metaslang with more concise syntax for this kind
  of mundane substitutions, and then we would use spec substitution as a matter
  of style, given the general dangers of "just adding a def" to a spec. *)

  import AESCryptographyBasics,
         AESModes qualifying BlockCipherModes

  def AESModes.blockSize = 128  % block size in AES

  % AES in ECB mode
  % (the AESModes qualifier is unnecessary, but we use for clarity):

  op encryptECB (key:Key) : BlockAlignedData -> BlockAlignedData =
    AESModes.encryptECB (encryptBlock key)

  op decryptECB (key:Key) : BlockAlignedData -> BlockAlignedData =
    AESModes.decryptECB (decryptBlock key)

  % DES in CBC mode
  % (the AESModes qualifier is unnecessary, but we use for clarity):

  op encryptCBC (key:Key) : InitVector -> BlockAlignedData ->
                            BlockAlignedData * InitVector =
    AESModes.encryptCBC (encryptBlock key)

  op decryptCBC (key:Key) : InitVector -> BlockAlignedData ->
                            BlockAlignedData * InitVector =
    AESModes.decryptCBC (decryptBlock key)

endspec
