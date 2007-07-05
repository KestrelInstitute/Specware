(*
2007:07:05
AC
A spec for DES (basic computation; DES modes are specified elsewhere).

*)


DES qualifying spec

  (* This spec formally specifies the basics of the Data Encryption Standard
  (DES), as officially specified in NIST's FIPS PUB 46-3. By "basics" we mean
  the encryption and decryption process for a single block. DES modes of
  operations like ECB and CBC are specified elsewhere.

  For better understanding of this formal spec, it is recommended to refer to
  the graphical representations of the DES computations that are present in
  FIPS PUB 46-3. In regard to such graphical representations, in the future it
  would be interesting to try to formalize directly those graphical
  representations and use them to specify DES in this spec. *)

  import BitSequences, NatExt

  (* A DES key consists of 64 bits. Only 56 bits of the key are actually used
  for encrypting/decrypting. The other 8 bits are parity bits used for error
  detection. The parity bits are the 8th, 16th, ..., 64th bit, starting from 1
  from left to right. Anyhow, in this spec we consider any sequence of 64 bits
  to be a DES key, regardless of the values of the parity bits. DES
  encryption/decryption does not rely on the fact that the parity bits are
  correct, it simply ignores those bits. Thus, there is no need to use a
  subtype of Word64 for DES keys. *)

  type Key = Word64

  (* We provide a predicate that checks whether the parity bits are correct,
  i.e. each byte comprising the key has an odd number of 1's (i.e. the
  exclusive OR of all the bytes comprising each byte is 1). However, this
  predicate is not used in the rest of this spec. *)

  op parityOK? (k:Key) : Boolean =
    fa(b:Byte) b in? bitsToBytes k => foldl (xor) 0 b = 1

  (* DES is a block cipher, i.e. an encryption/decryption method that operates
  on blocks of fixed size. The block size for DES is 64 bits. *)

  type Block = Word64

  (* Various transformations used in DES consist in scrambling a bit sequence
  to form another bit sequence: a new bit sequence by copying bits from
  various positions of the original bit sequence. In some cases the scrambling
  is a permutation, i.e. each bit in the original sequence is copied to
  exactly one position of the new sequence. In other cases the scrambling is
  an permuted expansion, i.e. each bit in the original sequence is copied to
  at least one position of the new sequence, but some bits are copied to
  multiple positions. In the remaining cases the scrambling is a permuted
  choice, i.e.  only some bits (not all) of the original sequence are copied
  to exactly one position of the new sequence.

  In all the three cases, the scrambling can be specified via a sequence of
  positive natural numbers n1 n2 ... nN that describe how the new sequence is
  constructed from the old one: the i-th bit of the new sequence (counting
  from 1 from left to right) is the ni-th bit of the original sequence (also
  counting from 1 from left to right). So, each ni must be not greater than
  the length of the original sequence (otherwise it would not identify any bit
  in the original sequence). The length N of the sequence of numbers is also
  the length of the new sequence.

  Since these sequences n1...nN may be relatively long, it is customary to
  split them across various lines and call them "tables". However, the
  row-and-column structure has little significance; they are just sequences of
  numbers. We actually use lists (i.e. constants of type List) instead of
  finite sequences (i.e. constants of type FSeq) so that we can use
  Metaslang's built-in syntax for list displays, which is slightly terser than
  an equivalent expression involving sequences.

  The following op scrambles a bit sequence according to a table (i.e. list).
  The subtype requires each number in the list to not exceed the bit sequence
  length, as explained above. Note that op @ on finite sequences counts
  indices starting from 0, so we need to subtract 1 from the number found in
  the list. When constructing the new bit sequence, we count from 0, so we can
  directly use i (without adding or subtracting 1) to retrieve the i-th number
  in the list via op nth. *)

  op scramble (table: List PosNat, input: FSeq Bit |
               fa(i:Nat) i < length table =>
                         nth(table,i) <= length input) : FSeq Bit =
    seq (fn(i:Nat) ->
      if i < length table then Some (input @ (nth(table,i) - 1)) else None)

  (* The very first operation in DES encryption/decryption is to apply an
  Initial Permutation (IP) to a block. This permutation is specified by the
  following table. *)

  op IP : List (Nat | in? (1, 64)) = [58, 50, 42, 34, 26, 18, 10,  2,
                                      60, 52, 44, 36, 28, 20, 12,  4,
                                      62, 54, 46, 38, 30, 22, 14,  6,
                                      64, 56, 48, 40, 32, 24, 16,  8,
                                      57, 49, 41, 33, 25, 17,  9,  1,
                                      59, 51, 43, 35, 27, 19, 11,  3,
                                      61, 53, 45, 37, 29, 21, 13,  5,
                                      63, 55, 47, 39, 31, 23, 15,  7]

  (* The very last operation in DES encryption/decryption is to apply the
  inverse of the Initial Permutation to a block, which is specified by the
  following table. *)

  op IPinv : List (Nat | in? (1, 64)) = [40,  8, 48, 16, 56, 24, 64, 32,
                                         39,  7, 47, 15, 55, 23, 63, 31,
                                         38,  6, 46, 14, 54, 22, 62, 30,
                                         37,  5, 45, 13, 53, 21, 61, 29,
                                         36,  4, 44, 12, 52, 20, 60, 28,
                                         35,  3, 43, 11, 51, 19, 59, 27,
                                         34,  2, 42, 10, 50, 18, 58, 26,
                                         33,  1, 41,  9, 49, 17, 57, 25]

  conjecture IP_and_IPinv_are_inverses is
    fa(block:Block) scramble (IPinv, scramble (IP,    block)) = block
                 && scramble (IP,    scramble (IPinv, block)) = block

  (* The computation of function f (formalized later) involves a permuted
  expansion of a sequence of 32 bits into a sequence of 48 bits (denoted "E")
  at the beginning and a permutation of a sequence of 32 bits (denoted "P") at
  the end. *)

  op E : List (Nat | in? (1, 32)) = [32,  1,  2,  3,  4,  5,
                                      4,  5,  6,  7,  8,  9,
                                      8,  9, 10, 11, 12, 13,
                                     12, 13, 14, 15, 16, 17,
                                     16, 17, 18, 19, 20, 21,
                                     20, 21, 22, 23, 24, 25,
                                     24, 25, 26, 27, 28, 29,
                                     28, 29, 30, 31, 32,  1]

  op P : List (Nat | in? (1, 32)) = [16,  7, 20, 21,
                                     29, 12, 28, 17,
                                      1, 15, 23, 26,
                                      5, 18, 31, 10,
                                      2,  8, 24, 14,
                                     32, 27,  3,  9,
                                     19, 13, 30,  6,
                                     22, 11,  4, 25]

  (* The computation of the key schedule (formalized later) involves two
  permuted choices. The first, denoted "PC-1", transforms a sequence of 64
  bits into a sequence of 56 bits and it is used at the beginning of the key
  schedule computation. The second, denoted "PC-2", transforms a sequence of
  56 bits into a sequence of 48 bits and it is used at the end of the
  computation, for each key bit sequence computed by the schedule. *)

  op PC1 : List (Nat | in? (1, 64)) = [57, 49, 41, 33, 25, 17,  9,
                                        1, 58, 50, 42, 34, 26, 18,
                                       10,  2, 59, 51, 43, 35, 27,
                                       19, 11,  3, 60, 52, 44, 36,
                                       63, 55, 47, 39, 31, 23, 15,
                                        7, 62, 54, 46, 38, 30, 22,
                                       14,  6, 61, 53, 45, 37, 29,
                                       21, 13,  5, 28, 20, 12,  4]

  op PC2 : List (Nat | in? (1, 56)) = [14, 17, 11, 24,  1,  5,
                                        3, 28, 15,  6, 21, 10,
                                       23, 19, 12,  4, 26,  8,
                                       16,  7, 27, 20, 13,  2,
                                       41, 52, 31, 37, 47, 55,
                                       30, 40, 51, 45, 33, 48,
                                       44, 49, 39, 56, 34, 53,
                                       46, 42, 50, 36, 29, 32]

  (* The computation of function f makes use of 8 "S" boxes, each of which
  maps a sequence of 6 bits into a sequence of 4 bits. Each S box is a table
  of 4 rows by 16 columns (so it is a "real" table, unlike the scrambling
  tables above that are really just lists). The first and last bit of the
  6-bit sequence are used to construct a row index. The middle 4 bits of the
  6-bit sequence are used to construct a column index. The entry at the
  designated row and column is a natural number less than 16, which represents
  the 4 output bits of the S box.

  We represent each S box via a list of length 4 of lists of length 16. In
  other words, each of the four inner lists constitutes a row, and the outer
  list puts the rows together. We use lists so that we can take advantage of
  Metaslang's built-in syntax for list displays, for increased terseness with
  respect to a formulation involving finite sequences.

  Since we have eight S boxes, numbered from 1 to 8, it is convenient to
  define S as a (finite) function from {1,...,8} to tables as described in the
  previous paragraph. So, the i-th S box (i.e. Si) can be denoted as (S i). *)

  op S : (Nat | in? (1, 8)) -> List (List (Nat | in? (0, 15))) = fn
    | 1 -> [[14,  4, 13,  1,  2, 15, 11,  8,  3, 10,  6, 12,  5,  9,  0,  7],
            [ 0, 15,  7,  4, 14,  2, 13,  1, 10,  6, 12, 11,  9,  5,  3,  8],
            [ 4,  1, 14,  8, 13,  6,  2, 11, 15, 12,  9,  7,  3, 10,  5,  0],
            [15, 12,  8,  2,  4,  9,  1,  7,  5, 11,  3, 14, 10,  0,  6, 13]]
    | 2 -> [[15,  1,  8, 14,  6, 11,  3,  4,  9,  7,  2, 13, 12,  0,  5, 10],
            [ 3, 13,  4,  7, 15,  2,  8, 14, 12,  0,  1, 10,  6,  9, 11,  5],
            [ 0, 14,  7, 11, 10,  4, 13,  1,  5,  8, 12,  6,  9,  3,  2, 15],
            [13,  8, 10,  1,  3, 15,  4,  2, 11,  6,  7, 12,  0,  5, 14,  9]]
    | 3 -> [[10,  0,  9, 14,  6,  3, 15,  5,  1, 13, 12,  7, 11,  4,  2,  8],
            [13,  7,  0,  9,  3,  4,  6, 10,  2,  8,  5, 14, 12, 11, 15,  1],
            [13,  6,  4,  9,  8, 15,  3,  0, 11,  1,  2, 12,  5, 10, 14,  7],
            [ 1, 10, 13,  0,  6,  9,  8,  7,  4, 15, 14,  3, 11,  5,  2, 12]]
    | 4 -> [[ 7, 13, 14,  3,  0,  6,  9, 10,  1,  2,  8,  5, 11, 12,  4, 15],
            [13,  8, 11,  5,  6, 15,  0,  3,  4,  7,  2, 12,  1, 10, 14,  9],
            [10,  6,  9,  0, 12, 11,  7, 13, 15,  1,  3, 14,  5,  2,  8,  4],
            [ 3, 15,  0,  6, 10,  1, 13,  8,  9,  4,  5, 11, 12,  7,  2, 14]]
    | 5 -> [[ 2, 12,  4,  1,  7, 10, 11,  6,  8,  5,  3, 15, 13,  0, 14,  9],
            [14, 11,  2, 12,  4,  7, 13,  1,  5,  0, 15, 10,  3,  9,  8,  6],
            [ 4,  2,  1, 11, 10, 13,  7,  8, 15,  9, 12,  5,  6,  3,  0, 14],
            [11,  8, 12,  7,  1, 14,  2, 13,  6, 15,  0,  9, 10,  4,  5,  3]]
    | 6 -> [[12,  1, 10, 15,  9,  2,  6,  8,  0, 13,  3,  4, 14,  7,  5, 11],
            [10, 15,  4,  2,  7, 12,  9,  5,  6,  1, 13, 14,  0, 11,  3,  8],
            [ 9, 14, 15,  5,  2,  8, 12,  3,  7,  0,  4, 10,  1, 13, 11,  6],
            [ 4,  3,  2, 12,  9,  5, 15, 10, 11, 14,  1,  7,  6,  0,  8, 13]]
    | 7 -> [[ 4, 11,  2, 14, 15,  0,  8, 13,  3, 12,  9,  7,  5, 10,  6,  1],
            [13,  0, 11,  7,  4,  9,  1, 10, 14,  3,  5, 12,  2, 15,  8,  6],
            [ 1,  4, 11, 13, 12,  3,  7, 14, 10, 15,  6,  8,  0,  5,  9,  2],
            [ 6, 11, 13,  8,  1,  4, 10,  7,  9,  5,  0, 15, 14,  2,  3, 12]]
    | 8 -> [[13,  2,  8,  4,  6, 15, 11,  1, 10,  9,  3, 14,  5,  0, 12,  7],
            [ 1, 15, 13,  8, 10,  3,  7,  4, 12,  5,  6, 11,  0, 14,  9,  2],
            [ 7, 11,  4,  1,  9, 12, 14,  2,  0,  6, 10, 13, 15,  3,  5,  8],
            [ 2,  1, 14,  7,  4, 10,  8, 13, 15, 12,  9,  0,  3,  5,  6, 11]]

  (* The following op applies the i-th S box to a 6-bit sequence, yielding a
  4-bit sequence (a.k.a. a nibble). The first bit of the 6-bit sequence is the
  most significant bit of the 2-bit row index. The 4 middle bits of the 6-bit
  sequence determine a column index by being interpreted as a big endian
  representation of the index (i.e. the second bit of the 6-bit sequence is
  the most significant bit). The numbers in the S tables are a big endian
  representation of the nibbles. *)

  op applyS (i: (Nat | in? (1, 8))) (x: (FSeq Bit | ofLength? 6)) : Nibble =
    let row    = toNat (first x |> last x |> empty) in
    let column = toNat (subFromLong (x, 1, 4)) in
    let val    = nth (nth (S i, row), column) in
    toNibble val

  (* The computation of function f uses the 8 S boxes to compute a 32-bit
  sequence from a 48-bit sequence. The 48-bit sequence is broken into 8
  subsequences of 6 bits each, each subsequence is run through an S box (1 to
  8, in left-to-right order), and the 8 resulting nibbles are concatenated
  into a 32-bit sequence. This process is captured by the following op, named
  after tha fact that it applies "all" the S boxes. *)

  op applySall (x: (FSeq Bit | ofLength? 48)) : Word32 =
       applyS 1 (subFromLong (x, 0 * 6, 6))  % leftmost subsequence
    ++ applyS 2 (subFromLong (x, 1 * 6, 6))
    ++ applyS 3 (subFromLong (x, 2 * 6, 6))
    ++ applyS 4 (subFromLong (x, 3 * 6, 6))
    ++ applyS 5 (subFromLong (x, 4 * 6, 6))
    ++ applyS 6 (subFromLong (x, 5 * 6, 6))
    ++ applyS 7 (subFromLong (x, 6 * 6, 6))
    ++ applyS 8 (subFromLong (x, 7 * 6, 6))  % rightmost subsequence

  (* The function f takes two inputs: a 32-bit sequence R and a 48-bit
  sequence K. It first uses E to expand R into 48 bits, which are xor'd with
  K, yielding a 48-bit sequence that is fed through the S boxes, and the
  resulting 32-bit sequence is permuted according to P. *)

  op f (R:Word32, K: (FSeq Bit | ofLength? 48)) : Word32 =
    scramble (P, applySall (scramble(E,R) xor K))

  (* The key schedule consists of 16 sequences of 48 bits from the key. Each
  48-bit sequence is used in one "round" of the DES encryption/decryption
  process, as second argument to function f defined above. An ingredient of
  the key schedule computation is a left shift of 28-bit sequences. There are
  16 such left shifts, one for each element of the key schedule. The distance
  for each such shift is given by the following function. (Note that all
  distances are 1 or 2.) *)

  op leftShiftSchedule : (Nat | in? (1, 16)) -> (Nat | in? (1, 2)) = fn
    |  1 -> 1
    |  2 -> 1
    |  3 -> 2
    |  4 -> 2
    |  5 -> 2
    |  6 -> 2
    |  7 -> 2
    |  8 -> 2
    |  9 -> 1
    | 10 -> 2
    | 11 -> 2
    | 12 -> 2
    | 13 -> 2
    | 14 -> 2
    | 15 -> 2
    | 16 -> 1

  (* The following op applies the n-th shift to a 28-bit sequence, yielding
  another 28-bit sequence. The (1 or 2) bits shifted out through the left end
  of the sequence are re-inserted into the right end. In processor instruction
  set jargon, this kind of operation would be called a "rotation" rather than
  a "shift" (a shift would discard the bits shifted out). *)

  op leftShift (n: (Nat | in? (1, 16))) (bits: (FSeq Bit | ofLength? 28))
               : (FSeq Bit | ofLength? 28) =
    removePrefix (bits, leftShiftSchedule n) ++ prefix (bits, leftShiftSchedule n)

  (* It is convenient to introduce a type for key schedules as finite
  functions from {1,...,8} to 48-bit sequences. *)

  type KeySchedule = (Nat | in? (1, 16)) -> (FSeq Bit | ofLength? 48)

  (* The key schedule for a given key is computed as follows. We first apply
  the permuted choice PC-1 to the key, obtaining a 56-bit sequence that is
  split into two subsequences, C0 and D0. Then, for each n in {1,...,16}, we
  compute Cn as the n-th left shift of Cn-1 and Dn as the n-th left shift of
  Dn-1. Each Kn is the result of applying the permuted choice PC-2 to the
  concatenation of Cn and Dn.

  This process is captured by the following op. We existentially quantify C
  and D as functions from {1,...,16} to 28-bit sequences, so that we can write
  C n and D n to denote Cn and Dn as described in the previous paragraph.
  Also, since K has type KeySchedule, we can write K n to denote Kn.

  This op is a curried form of function KS as usually defined in the
  literature. In the literature, KS is usually defined as a binary function
  KS(n,key), which in this spec is KS key n instead. *)

  op KS (key:Key) : KeySchedule = the(K:KeySchedule)
    ex (C : (Nat | in? (0, 16)) -> (FSeq Bit | ofLength? 28),
        D : (Nat | in? (0, 16)) -> (FSeq Bit | ofLength? 28))
      C 0 ++ D 0 = scramble (PC1, key) &&
      (fa (n : (Nat | in? (1, 16)))
         C n = leftShift n (C (n-1)) &&
         D n = leftShift n (D (n-1)) &&
         K n = scramble (PC2, C n ++ D n))

  (* The following is the reverse key schedule, i.e. K16 ... K1 (instead of
  K1...K16). As specified below, encryption and decryption are the same
  computation, except that for decryption we reverse the key schedule. *)

  op KSrev (key:Key) : KeySchedule =
    fn (n : (Nat | in? (1, 16))) -> KS key (17 - n)

  (* Encryption and decryption are the same operation, but with a different
  key schedule. So, we define an op (where "XX" stands for "en" or "de") that
  takes a key schedule and an input block as argument, returning an output
  block. The output is computed as follows. First, the input is permuted
  according to IP. The result is split into two equal subsequences, L0 and
  R0. 16 rounds follow. Each round n copies Rn-1 into Ln and computes Rn as
  the exclusive OR of Ln-1 and f applied to Rn-1 and Kn. The pre-output is the
  concatenation of R16 and L16, which is permuted according to IPinv to yield
  the final output. Similarly to the specification of op KS above, we
  existentially quantify L and R as functions from {1,...,16} to 32-bit
  sequences. *)

  op XXcryptBlock (K:KeySchedule) (input:Block) : Block = the(output)
    ex (L : (Nat | in? (0, 16)) -> (FSeq Bit | ofLength? 32),
        R : (Nat | in? (0, 16)) -> (FSeq Bit | ofLength? 32))
      L 0 ++ R 0 = scramble (IP, input) &&
      (fa (n : (Nat | in? (1, 16)))
         L n = R (n-1) &&
         R n = (L (n-1)) xor (f (R (n-1), K n))) &&
      output = scramble (IPinv, R 16 ++ L 16)

  (* We now simply define encryption and decryption as follows. *)

  op encryptBlock (key:Key) : Block -> Block = XXcryptBlock (KS key)

  op decryptBlock (key:Key) : Block -> Block = XXcryptBlock (KSrev key)

  (* It is not hard to see that encryption and decryption are inverses. The
  initial permutation IP is the inverse of the final permutation IPinv. For
  each round, we have (see definition of op XXcryptBlock above):
    L n = R (n-1)
    R n = (L (n-1)) xor (f (R (n-1), K n)))
  That is, using elementary properties of xor:
    R (n-1) = L n
    L (n-1) = (R n) xor (f (L n, K n))
  In other words, the same computation that yields L n and R n from L (n-1)
  and R (n-1), also yields R (n-1) and L (n-1) from R n and L n. So, we can
  compute R 0 and L 0 from R 16 and L 16 in the same way that we compute L 16
  and R 16 from L 0 and R 0, but the key schedule must be reversed, as it is
  indeed in the definition of encryption and decryption. *)

  conjecture encrypt_and_decrypt_are_inverses is
    fa(key:Key) (decryptBlock key) o (encryptBlock key) = id
             && (encryptBlock key) o (decryptBlock key) = id

endspec
