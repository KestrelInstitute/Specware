(* $Id$ *)

(*
2007:07:13
AC
A spec for AES (basic computation; AES modes are specified elsewhere).

ISSUE:
This spec should import a (currently non-existent) generic spec for polynomials
and operations over polynomials, and use it to define polynomial multiplication
in a higher-level way. See comments in this spec below.

ISSUE:
Perhaps decryption should be defined as in the FIPS standard, and then proved to
be the inverse of encryption, as opposed to directly defining it as the inverse
of encryption. See comment at the end of this spec.

*)


AES qualifying spec

  (* This spec formalizes the basics of the Advanced Encryption Standard (AES),
  as officially specified in NIST's FIPS PUB 197. By "basic" we mean the
  encryption and decryption process for a single block. AES modes of operations
  like ECB and CBC are specified elsewhere.

  In the comments in this spec, we refer to NIST's FIPS PUB 197 as "[FIPS]",
  possibly extended with references to (sub)sections (e.g. "[FIPS 3.1]"),
  figures (e.g. "[FIPS Fig 4]"), and equations (e.g. "FIPS (3.3)"). *)

  import BitSequences

  (* A key consists of 128, 192, or 256 bits [FIPS 3.1], leading to the AES-128,
  AES-192, and AES-256 variants of the algorithm [FIPS Fig 4]. *)

  type Key = (FSeq Bit | ofLength? 128 \/ ofLength? 192 \/ ofLength? 256)

  (* AES is a block cipher, i.e. an encryption/decryption method that operates
  on blocks of fixed size. The block size for AES is 128 bits. *)

  type Block = (FSeq Bit | ofLength? 128)

  (* Block length in 32-bit words. Even though it is constant, [FIPS] introduces
  a symbolic name ("Nb") and uses that symbolic name (perhaps for easier future
  extension). We do the same here. *)

  op Nb : Nat = 4  % = 128 div 32

  (* The internal state of the algorithm is a two-dimensional (4 x Nb) array of
  bytes [FIPS 3.4], which we capture as a function from pairs of row and column
  indices to bytes. *)

  type RC = {(r,c) : Nat * Nat | r < 4 && c < Nb}

  type State = RC -> Byte

  (* The input block of the algorithm becomes the initial state, while the final
  state becomes the output block [FIPS Fig 3]. The following two ops capture
  conversions between blocks and states. *)

  op blockToState (bl:Block) : State =
    % group into bytes first:
    let input = bitsToBytes bl in
    % [FIPS (3.3)]:
    fn (r,c):RC -> input @ (r + 4 * c)

  op stateToBlock : State -> Block = inverse blockToState

  (* The state is sometimes manipulated as an array of Nb columns, where a
  column is a 32-bit word [FIPS 3.5]. The following op captures this view of the
  state. *)

  op column (st:State, c:Nat | c < Nb) : Word32 =  % c-th column
    st(0,c) ++ st(1,c) ++ st(2,c) ++ st(3,c)

  (* The following op captures the operation xtime() defined in [FIPS 4.2.1].
  This is an implementation-level operation, used to define multiplication of
  polynomials represented as bytes. It would be more elegant to define
  polynomial multiplication at a higher level, in a generic spec for
  polynomials, and then use that definition in this spec. This will be done in
  the future. *)

  op xtime (poly:Byte) : Byte =
    (* If poly includes x^7 (i.e. if the leftmost/first bit is 1),
    multiplication by x (i.e. left shift by 1, inserting 0 into the
    rightmost/last bit) yields a polynomial that includes x^8, and therefore we
    need to subtract the irreducible polynomial m(x), which amounts to xor'ing
    by 0x1b. *)
    if first poly = 1 then shiftLeft(poly,0,1) xor toByte 0x1b
    (* If instead poly does not include x^7, multiplication by x yields a
    polynomial that does not include x^8, which is therefore already reduced
    modulo m(x). *)   else shiftLeft(poly,0,1)

  (* Multiplication by x as defined by op xtime can be iterated to multiply by
  an arbitrary x^n. In order to define polynomial multiplication, we only need
  to multiply by x^2, ..., x^7, besides x. For uniformity, the following op
  captures multiplication by x^0, x^1, x^2, ..., x^7. *)

  op xntime (n:Nat, poly:Byte | n < 8) : Byte =
    if n = 0 then poly             % multiplication by 1, i.e. identity
    else xtime (xntime(n-1,poly))  % x^n = x * x^(n-1)

  (* To multiply two polynomials, we multiply one of them (it does not matter
  which) for each of the monomials that comprises the other polynomial, and then
  we add the results. The "b" in "MULb" disambiguates this op, which operates on
  (polynomials represented as) bytes, from op MULw (below), which operates on
  another kind of polynomials. *)

  op MULb (poly:Byte, poly':Byte) infixl 27 : Byte =
    (* We construct 8 summands (each summand is a polynomial), one for each
    degree n of the monomials x^n that comprise poly. If the coefficient of x^n
    in poly is 1 (i.e. if poly includes x^n), the summand is the product of
    poly' by x^n. If instead the coefficient of x^n in poly is 0 (if poly does
    not include x^n), the summand is 0. Note that, when we view a byte as a
    polynomial, the first bit is the coefficient of x^7 and the last bit is the
    coefficient of x^0 [FIPS 3.2]; on the other hand, op @ over finite sequences
    indexes elements in the other way, so we use (7-n) to flip the indexing. *)
    let summands = seq (fn n:Nat ->
        if n < 8 then
          Some (if poly @ (7-n) = 1 then xntime (n, poly') else toByte 0)
        else None) in
    % add (i.e. xor) up all the summands (starting of course from 0):
    foldl (xor) (toByte 0) summands

  (* The following op defines multiplication of polynomials with coefficients in
  GF(2^8) [FIPS 4.3]. The "w" in "MULw" disambiguates this op, which operates on
  (polynomials represented as) 32-bit words, from op MULb above. As also
  remarked for op MULb, it would be more elegant to have a generic spec for
  polynomials and operations over them, and use that spec in this spec for AES;
  this will be done in the future. *)

  op MULw (a:Word32, b:Word32) infixl 27 : Word32 =
    % decompose each polynomial into constituent bytes:
    let (a3,a2,a1,a0) = word32ToBytes a in
    let (b3,b2,b1,b0) = word32ToBytes b in
    % [FIPS (4.12)]:
    let d0 = (a0 MULb b0) xor (a3 MULb b1) xor (a2 MULb b2) xor (a1 MULb b3) in
    let d1 = (a1 MULb b0) xor (a0 MULb b1) xor (a3 MULb b2) xor (a2 MULb b3) in
    let d2 = (a2 MULb b0) xor (a1 MULb b1) xor (a0 MULb b2) xor (a3 MULb b3) in
    let d3 = (a3 MULb b0) xor (a2 MULb b1) xor (a1 MULb b2) xor (a0 MULb b3) in
    % compose byte coefficients into polynomial:
    d3 ++ d2 ++ d1 ++ d0

  (* The SubBytes operation [FIPS 5.1.1] transforms each byte of the state. The
  transformation of each byte consists of two steps. The first is to take the
  multiplicative inverse (in GF(2^8)) of the byte, mapping 0 to 0. *)

  op SubByte1 (b:Byte) : Byte =
    if b = toByte 0 then toByte 0        % 0 to 0
    else (the(b') b' MULb b = toByte 1)  % multiplicative inverse

  (* The second step of the SubBytes operation is the affine transformation
  defined by [FIPS (5.1)]. As also mentioned above, when viewing a byte as a
  polynomial, its bits are indexed from right to left (i.e. b7...b0) [FIPS
  3.2]. However, op @ on finite sequences indexes bits the other way
  (i.e. b0...b7). In order to index bits as in the polynomial view, all we need
  to do is reverse the bytes, as done in the op below. *)

  op SubByte2 (b:Byte) : Byte =
    let b = reverse b in
    let c = reverse (toByte 0x63) in
    the(b') (let b' = reverse b' in
             fa(i:Nat) i < 8 =>
               b' @ i = (b @ i)
                    xor (b @ ((i+4) rem 8))
                    xor (b @ ((i+5) rem 8))
                    xor (b @ ((i+6) rem 8))
                    xor (b @ ((i+7) rem 8))
                    xor (c @ i))

  % the transformation of each byte consists of the two steps just defined:

  op SubByte : Byte -> Byte = SubByte2 o SubByte1

  (* The state is transformed by transforming its bytes. Since the state is a
  function from row-column indices to bytes, we use function composition. *)

  op SubBytes (s:State) : State = SubByte o s

  % [FIPS 5.1.2] (note that shift(r,Nb) = r always):

  op ShiftRows (s:State) : State =
    fn (r,c):RC -> s (r, (c + r) rem Nb)

  % [FIPS (5.5)]:

  op ax : Word32 = toByte 3 ++ toByte 1 ++ toByte 1 ++ toByte 2

  % [FIPS 5.1.3]:

  op MixColumns (s:State) : State =
    the(s') fa(c:Nat) c < Nb =>
       column(s',c) = ax MULw column(s,c)

  % [FIPS 5.2]:

  op SubWord (w:Word32) : Word32 =
    let (a,b,c,d) = word32ToBytes w in
    SubByte a ++ SubByte b ++ SubByte c ++ SubByte d

  % [FIPS 5.2]:

  op RotWord (w:Word32) : Word32 = rotateLeft (w, 8)

  % number of 32-bit words that comprise the key [FIPS Fig 4]:

  op Nk (k:Key) : Nat = length k div 32  % 4, 6, 8

  % number of rounds [FIPS Fig 4]:

  op Nr (k:Key) : Nat = Nk k + 6  % 10, 12, 14

  (* Key expansion [FIPS Fig 11] makes use of the round constants Rcon[i/Nk],
  for Nk <= i < Nb * (Nr+1), when i is a multiple of Nk. Therefore: when Nk = 4
  and Nr = 10, i/Nk goes from 1 to 10 because the max value of i is 43; when Nk
  = 6 and Nr = 12, i/Nk goes from 1 to 8 because the max value of i is 51; when
  Nk = 8 and Nr = 14, i/Nk goes from 1 to 7 because the max value of i is 59.
  Thus, op Rcon only needs to be defined on {1,...,10}.

  As defined in [FIPS 5.2], Rcon[i] is a 32-bit word whose first byte represents
  the polynomial x^(i-1). If i <= 8, x^(i-1) is already in reduced form
  w.r.t. m(x). If instead i = 9 or i = 10, we must reduce it. More precisely, if
  i = 9, x^8 reduced by m(x) is just m(x), represented by 0x1b. If i = 10, x^9
  reduced by m(x) is p(x) = x^5 + x^4 + x^2 + x (because x^9 = x * m(x) + p(x)),
  which is represented by 0x36. These calculations are not explicit in [FIPS
  5.2]. *)

  op Rcon (i:PosNat | i <= 10) : Word32 =
    let xi_1 =
        if i <= 8     then update (toByte 0, 8-i, 1)
        else if i = 9 then toByte 0x1b
        else (* i = 10 *)  toByte 0x36 in
    xi_1 ++ repeat 0 24

  (* The key schedule consists of a finite sequence of Nb*(Nr+1) 32-bit words,
  defined by the following op, which returns the i-th word for the given key
  k. The definition of this op mirrors the procedural definition in [FIPS Fig
  11]. *)

  op w (k:Key, i:Nat | i < Nb * (Nr k + 1)) : Word32 =
    % the first Nk words are just copied from the key:
    if i < Nk k then subFromLong (k, 32*i, 32)
    % the other words are computed based on previous words:
    else let temp = w(k,i-1) in
         let temp = if (i rem Nk k) = 0 then
                      (SubWord (RotWord temp)) xor Rcon (i div Nk k)
                    else if (Nk k > 6 && i rem Nk k = 4) then
                      SubWord temp
                    else
                      temp in
         w (k, i - Nk k) xor temp

  % add round key to state, for given key and round number [FIPS 5.1.4]:

  op AddRoundKey (k:Key, round:Nat | round <= Nr k) (s:State) : State =
    let l = round * Nb in
    % [FIPS (5.7)]:
    the(s') fa(c:Nat) c < Nb =>
       column(s',c) = column(s,c) xor w(k,l+c)

  (* The following op returns the state just after the round given as argument,
  for the given input block and the given key. Its definition mirrors the
  procedural definition in [FIPS Fig 5]. Our definition seems slightly more
  readable than [FIPS Fig 5] because op AddRoundKey just takes a round number as
  argument in this spec, as opposed to an array of words as in [FIPS]. *)

  op stateAfterRound (input:Block, k:Key, round:Nat | round <= Nr k) : State =
    let initialState = blockToState input in  % [FIPS Fig 3.3]
    if round = 0 then
      AddRoundKey (k, 0) initialState  % first round operates on initial state
    else if round < Nr k then
      let s = stateAfterRound (input, k, round-1) in  % start from state from
      let s = SubBytes   s in                         % previous round
      let s = ShiftRows  s in
      let s = MixColumns s in
      AddRoundKey (k, round) s
    else (* round = Nr k *)
      let s = stateAfterRound (input, k, round-1) in  % start from state from
      let s = SubBytes   s in                         % previous round
      let s = ShiftRows  s in
      AddRoundKey (k, round) s

  (* Encryption is obtained by copying the final state (i.e. the state after the
  final round) into the output block [FIPS Fig 3.3]. *)

  op encryptBlock (k:Key) (input:Block) : Block =
    stateToBlock (stateAfterRound (input, k, Nr k))

  (* We simply define decryption as the inverse of encryption. Since this formal
  spec is meant to capture [FIPS], perhaps it should instead define decryption
  more directly, in terms of operations InvShiftRows etc. [FIPS 5.3], and then
  the fact that decryption is the inverse of encryption should be stated and
  proved as a theorem. However, that AES decryption and encryption are inverses
  is a well-known fact. Thus, at least for now, the rather concise definition of
  decryption below is fine. *)

  op decryptBlock (k:Key) : Block -> Block = inverse (encryptBlock k)

endspec
