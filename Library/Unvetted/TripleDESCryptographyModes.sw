(*
2007:07:05
AC
A spec for ECB and CBC modes of operation for triple DES.

ISSUE:
Other modes should be added (e.g. CFB, OFB).

*)


TDES qualifying spec

  (* This spec is very analogous to spec DESCryptographyModes, but for 3DES
  instead of DES. Refer to the explanatory comments in that spec, which apply,
  mutatis mutandis, to this spec. *)

  import TripleDESCryptographyBasics, BlockCipherModes

  def BlockCipher.blockSize = 64  % block size in 3DES

  % 3DES in ECB mode:

  op encryptECB (key:TDES.Key) : BlockAlignedData -> BlockAlignedData =
    BlockCipher.encryptECB (encryptBlock key)

  op decryptECB (key:TDES.Key) : BlockAlignedData -> BlockAlignedData =
    BlockCipher.decryptECB (decryptBlock key)

  % 3DES in CBC mode:

  op encryptCBC (key:TDES.Key) : InitVector -> BlockAlignedData ->
                                 BlockAlignedData * InitVector =
    BlockCipher.encryptCBC (encryptBlock key)

  op decryptCBC (key:TDES.Key) : InitVector -> BlockAlignedData ->
                                 BlockAlignedData * InitVector =
    BlockCipher.decryptCBC (decryptBlock key)

  (* 3DES CBC mode as defined above is sometimes called "outer CBC", as
  opposed to "inner CBC". Outer CBC performs the chaining at the outer level
  in the sense that the application of the 3 DES keys that comprise the 3DES
  key are applied to a block as at atomic transformation. Inner CBC instead
  performs the chaining also in each of the 3 steps (EDE or DED). Outer CBC is
  the de facto standards; inner CBC has been found to be less secure than
  outer CBC. For now, we do not specify inner CBC, and consider CBC as defined
  above to the the common outer CBC. *)

endspec
