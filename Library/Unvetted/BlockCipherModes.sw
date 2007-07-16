(* $Id$ *)

(*
2007:07:05
AC
A generic spec for block ciphers, which can be instantiated to e.g. DES and AES.

ISSUE:
Other modes should be added (e.g. CFB, OFB).

*)


spec

  (* A block cipher is an encryption/decryption method that operates on blocks
  of fixed size. An example of block cipher is DES. A block cipher can be
  applied to data whose size may differ from the block size in various ways,
  called "modes". Block cipher modes are independent from the details of the
  block cipher and can therefore be specified generically and instantiated to
  different block ciphers. This spec provides such a generic spec.

  For better understanding of this formal spec, it is recommended to refer to
  graphical representations of the computations of these block cipher modes,
  which can be easily found in a variety of textbooks and online resources,
  such as the Wikipedia page titled "Block cipher modes of operation" (as of
  November 11, 2006), available at URL http://en.wikipedia.org/wiki/
  Block_cipher_modes_of_operation. In regard to such graphical
  representations, in the future it would be interesting to try to formalize
  directly those graphical representations and use them to specify block
  cipher modes in this spec. *)

  import BitSequences

  (* The following uninterpreted constant represents the size of the block.
  When this spec is instantiated for use with a particular block cipher, this
  constant must be instantiated with a concrete value. *)

  op blockSize : PosNat

  (* A block is a sequence of blockSize bits. *)

  type Block = (FSeq Bit | ofLength? blockSize)

  (* We consider data to be any sequence of bits, and we introduce a subtype
  for block-aligned data. *)

  type Data = FSeq Bit

  type BlockAlignedData = {d : Data | length d rem blockSize = 0}

  (* Besides the block size, block cipher modes are parameterized over the
  details of the block encryption/decryption process. Encryption/decryption
  can be viewed as a function from blocks to blocks (there are generally
  different functions for different blocks). Functions from blocks to blocks
  are used as additional arguments to ops defined below. *)

  type CryptoFunction = Block -> Block

  (* The simplest mode is ECB (= Electronic CodeBook). This mode only works on
  block-aligned data (non-block-aligned data must be suitably padded). The
  data is split into blocks and each block is encrypted/decrypted separately;
  the results are concatenated in the same order as the original blocks. Note
  that this works fine for empty data, as a boundary case. *)

  op encryptECB (cryptoFun:CryptoFunction) (data:BlockAlignedData)
                : BlockAlignedData =
    % split data into blocks:
    let dataBlocks : FSeq Block = the(dataBlocks)
        flatten dataBlocks = data in
    % encrypt each block separately:
    let encryptedDataBlocks = map cryptoFun dataBlocks in
    % join blocks:
    flatten encryptedDataBlocks

  op decryptECB (cryptoFun:CryptoFunction) (data:BlockAlignedData)
                : BlockAlignedData =
    % split data into blocks:
    let dataBlocks : FSeq Block = the(dataBlocks)
        flatten dataBlocks = data in
    % decrypt each block separately:
    let decryptedDataBlocks = map cryptoFun dataBlocks in
    % join blocks:
    flatten decryptedDataBlocks

  (* ECB encryption and decryption are inverses of each other, provided that
  the block encryption and decryption functions are inverses of each other. *)

  conjecture encryptECB_and_decryptECB_are_inverses is
    fa (encFun:CryptoFunction, decFun:CryptoFunction)
      decFun o encFun = id &&
      encFun o decFun = id =>
      (decryptECB decFun) o (encryptECB encFun) = id &&
      (encryptECB decFun) o (decryptECB encFun) = id

  (* Another popular mode is CBC (= Cipher-Block Chaining). This mode only
  works on block-aligned data (non-block-aligned data must be suitably
  padded). In the descriptions in the following two paragraphs, "plaintext"
  indicates (block-aligned) data to be encrypted while "ciphertext" indicates
  (also block-aligned) encrypted plaintext to be decrypted.

  For encryption, the plaintext data is split into blocks. Each block is first
  xor'd with the ciphertext block resulting from the encryption of the
  previous plaintext block, and then encrypted as a block according to the
  specific block cipher. Since the first (i.e. leftmost) block has no
  preceding block, it is necessary to supply an "initialization vector" ("IV"
  for short), consisting of nBlock bits (i.e. a block well). The last
  ciphertext block can be used to continue the chaining with additional block,
  so op encryptCBC below returns an IV as additional result, besides the
  ordered concatenation of the ciphertext blocks.

  Decryption works similarly, except that each ciphertext block is first
  decrypted as a block according to the specific block cipher, then xor'd with
  the previous ciphertext block (not the plaintext block). For the first
  block, we use IV, which must be supplied as additional input to op
  decryptCBC below. *)

  type InitVector = Block

  op encryptCBC (cryptoFun: CryptoFunction)
                (IV0      : InitVector)
                (plaintext: BlockAlignedData)
                : BlockAlignedData * InitVector = the(output)
    ex (P  : FSeq Block,       % plaintext blocks
        C  : FSeq Block,       % ciphertext blocks
        IV : FSeq InitVector,  % IVs for each block
        n  : Nat)              % number of plaintext and ciphertext blocks
      length P  = n &&
      length C  = n &&
      length IV = n + 1 &&  % includes output IV
      % split plaintext into blocks:
      flatten P = plaintext &&
      % first IV is given as argument:
      IV@0 = IV0 &&
      (fa(i:Nat) i < n =>
         % i-th ciphertext block computed from i-th plaintext block and i-th IV:
         C@i = cryptoFun (IV@i xor P@i) &&
         % i-th ciphertext block is next (i.e. (i+1)-th) IV:
         IV@(i+1) = C@i) &&
      % final result consists of all ciphertext blocks plus last IV:
      output = (flatten C, IV@n)

  op decryptCBC (cryptoFun : CryptoFunction)
                (IV0       : InitVector)
                (ciphertext: BlockAlignedData)
                : BlockAlignedData * InitVector = the(output)
    ex (C  : FSeq Block,       % ciphertext blocks
        P  : FSeq Block,       % plaintext blocks
        IV : FSeq InitVector,  % IVs for each block
        n  : Nat)              % number of ciphertext and plaintext blocks
      length C  = n &&
      length P  = n &&
      length IV = n + 1 &&  % includes output IV
      % split ciphertext into blocks:
      flatten C = ciphertext &&
      % first IV is given as argument:
      IV@0 = IV0 &&
      (fa(i:Nat) i < n =>
         % i-th plaintext block computed from i-th ciphertext block and i-th IV:
         P@i = IV@i xor (cryptoFun (C@i)) &&
         % the i-th ciphertext block is the next (i.e. (i+1)-th) IV:
         IV@(i+1) = C@i) &&
      % final result consists of all plaintext blocks plus last IV:
      output = (flatten P, IV@n)

  (* CBC encryption and decryption are inverses of each other, provided that
  the block encryption and decryption functions are inverses of each other. *)

  conjecture encryptCBC_and_decryptCBC_are_inverses is
    fa (encFun : CryptoFunction,
        decFun : CryptoFunction,
        inIV   : InitVector,
        outIV  : InitVector,
        P      : BlockAlignedData,
        C      : BlockAlignedData)
      decFun o encFun = id &&
      encFun o decFun = id =>
      (encryptCBC encFun inIV P = (C, outIV)
       <=>
       decryptCBC decFun inIV C = (P, outIV))

  (* This spec should be extended with CFB (= Cipher FeedBack) and OFB (=
  Output FeedBack) mode, and also with padding methods to turn
  possibly-non-block-aligned data into block-aligned data. *)

endspec
