(* $Id$ *)

(*
2007:07:09
AC
A spec for SHA.

*)


SHA qualifying spec

  import BitSequences, NatExt

  (* This spec formalizes the Secure Hash Algorithm(s) (SHA) described in NIST's
  FIPS PUB 180-2, "Secure Hash Standard". In the comments in this spec, we refer
  to that document as "[FIPS]", possibly extended with references to
  (sub)sections, e.g. "[FIPS 4.2.1]". This spec is meant to be read in
  conjunction with [FIPS]: the comments in this spec are not meant to provide a
  self-contained explanation of SHA.

  The "main" ops in this spec are sha1, sha224, sha256, sha384, and sha512; the
  "main" types in this spec are Message64 and Message128. All other types and
  ops are auxiliary, their only purpose is to enable the specification of the
  "main" types and ops. *)

  % [FIPS 4.1]:

  op Ch (x: FSeq Bit, y: FSeq Bit, z: FSeq Bit | x equiLong y && y equiLong z)
        : FSeq Bit =
    (x and y) xor (not x and y)
    % note that it operates on bit sequences of any length, not just 32 and 64

  op Maj (x: FSeq Bit, y: FSeq Bit, z: FSeq Bit | x equiLong y && y equiLong z)
         : FSeq Bit =
    (x and y) xor (x and z) xor (y and z)
    % note that it operates on bit sequences of any length, not just 32 and 64

  op Parity (x:Word32, y:Word32, z:Word32) : Word32 = x xor y xor z

  op f (t:Nat | t < 80) (x:Word32, y:Word32, z:Word32) : Word32 =
         if t < 20 then Ch     (x,y,z)
    else if t < 40 then Parity (x,y,z)
    else if t < 60 then Maj    (x,y,z)
    else (* t < 80 *)   Parity (x,y,z)

  op Sigma256_0 (x:Word32) : Word32 =
    rotateRight (x, 2)  xor rotateRight (x, 13) xor rotateRight (x, 22)

  op Sigma256_1 (x:Word32) : Word32 =
    rotateRight (x, 6) xor rotateRight (x, 11) xor rotateRight (x, 25)

  op sigma256_0 (x:Word32) : Word32 =
    rotateRight (x, 7) xor rotateRight (x, 18) xor rotateRight (x, 3)

  op sigma256_1 (x:Word32) : Word32 =
    rotateRight (x, 17) xor rotateRight (x, 19) xor rotateRight (x, 10)

  op Sigma512_0 (x:Word64) : Word64 =
    rotateRight (x, 28) xor rotateRight (x, 34) xor rotateRight (x, 39)

  op Sigma512_1 (x:Word64) : Word64 =
    rotateRight (x, 14) xor rotateRight (x, 18) xor rotateRight (x, 41)

  op sigma512_0 (x:Word64) : Word64 =
    rotateRight (x, 1) xor rotateRight (x, 8) xor rotateRight (x, 7)

  op sigma512_1 (x:Word64) : Word64 =
    rotateRight (x, 19) xor rotateRight (x, 61) xor rotateRight (x, 6)

  % [FIPS 4.2]:

  op K (t:Nat | t < 80) : Word32 =
         if t < 20 then toWord32 0x5a827999
    else if t < 40 then toWord32 0x6ed9eba1
    else if t < 60 then toWord32 0x8f1bbcdc
    else (* t < 80 *)   toWord32 0xca62c1d6

  op K256 (i:Nat | i < 64) : Word32 =
    nth (map toWord32 [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
                       0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
                       0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
                       0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
                       0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
                       0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
                       0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
                       0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
                       0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
                       0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
                       0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
                       0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
                       0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
                       0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
                       0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
                       0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2], i)

  op K512 (i:Nat | i < 80) : Word64 =
    nth (map toWord64 [0x428a2f98d728ae22, 0x7137449123ef65cd,
                       0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
                       0x3956c25bf348b538, 0x59f111f1b605d019,
                       0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
                       0xd807aa98a3030242, 0x12835b0145706fbe,
                       0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
                       0x72be5d74f27b896f, 0x80deb1fe3b1696b1,
                       0x9bdc06a725c71235, 0xc19bf174cf692694,
                       0xe49b69c19ef14ad2, 0xefbe4786384f25e3,
                       0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
                       0x2de92c6f592b0275, 0x4a7484aa6ea6e483,
                       0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
                       0x983e5152ee66dfab, 0xa831c66d2db43210,
                       0xb00327c898fb213f, 0xbf597fc7beef0ee4,
                       0xc6e00bf33da88fc2, 0xd5a79147930aa725,
                       0x06ca6351e003826f, 0x142929670a0e6e70,
                       0x27b70a8546d22ffc, 0x2e1b21385c26c926,
                       0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
                       0x650a73548baf63de, 0x766a0abb3c77b2a8,
                       0x81c2c92e47edaee6, 0x92722c851482353b,
                       0xa2bfe8a14cf10364, 0xa81a664bbc423001,
                       0xc24b8b70d0f89791, 0xc76c51a30654be30,
                       0xd192e819d6ef5218, 0xd69906245565a910,
                       0xf40e35855771202a, 0x106aa07032bbd1b8,
                       0x19a4c116b8d2d0c8, 0x1e376c085141ab53,
                       0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
                       0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb,
                       0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
                       0x748f82ee5defb2fc, 0x78a5636f43172f60,
                       0x84c87814a1f0ab72, 0x8cc702081a6439ec,
                       0x90befffa23631e28, 0xa4506cebde82bde9,
                       0xbef9a3f7b2c67915, 0xc67178f2e372532b,
                       0xca273eceea26619c, 0xd186b8c721c0c207,
                       0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
                       0x06f067aa72176fba, 0x0a637dc5a2c898a6,
                       0x113f9804bef90dae, 0x1b710b35131c471b,
                       0x28db77f523047d84, 0x32caab7b40c72493,
                       0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
                       0x4cc5d4becb3e42b6, 0x597f299cfc657e2a,
                       0x5fcb6fab3ad6faec, 0x6c44198c4a475817], i)

  % messages that SHA-1, SHA-224, and SHA-256 operate on:

  type Message64 = {M: FSeq Bit | length M < 2**64}

  % messages that SHA-384 and SHA-512 operate on:

  type Message128 = {M: FSeq Bit | length M < 2**128}

  % [FIPS 5.1.1]:

  op padded512 (M:Message64) : {M: FSeq Bit | length M rem 512 = 0} =
    let l = length M in
    let k = minIn (fn k:Integer ->
        k >= 0 && (l + 1 + k) rem 512 = 448) in
    M ++ single 1 ++ repeat 0 k ++ fromNat (l, 64)

  % [FIPS 5.1.2]:

  op padded1024 (M:Message128) : {M: FSeq Bit | length M rem 1024 = 0} =
    let l = length M in
    let k = minIn (fn k:Integer ->
        k >= 0 && (l + 1 + k) rem 1024 = 896) in
    M ++ single 1 ++ repeat 0 k ++ fromNat (l, 128)

  (* Since a 512/1024-bit block is "viewed" (and referenced) as sixteen
  32/64-bit words, we model such blocks as functions from indices (0 thru 15) to
  words. *)

  type Block512  = (Nat|in?(0,15)) -> Word32
  type Block1024 = (Nat|in?(0,15)) -> Word64

  % [FIPS 5.2.1]:

  op parsed512 (M:Message64) : FSeq Block512 =
    let M = padded512 M in
    let N = length M div 512 in
    % sequence of N blocks:
    seq (fn i:Nat ->
      if i < N then
        Some (fn j:(Nat|in?(0,15)) ->
                 % j-th word of i-th block:
                 subFromLong (M, i * 512 + j * 32, 32))
      else None)

  % [FIPS 5.2.2]:

  op parsed1024 (M:Message128) : FSeq Block1024 =
    let M = padded1024 M in
    let N = length M div 1024 in
    % sequence of N blocks:
    seq (fn i:Nat ->
      if i < N then
        Some (fn j:(Nat|in?(0,15)) ->
                 % j-th word of i-th block:
                 subFromLong (M, i * 1024 + j * 64, 64))
      else None)

  % number of blocks that a (padded) message is parsed into [FIPS 5.2]:

  op N512  (M:Message64)  : Nat = length (parsed512  M)
  op N1024 (M:Message128) : Nat = length (parsed1024 M)

  % hash values used by SHA-1 (160 bits total):

  type Hash160 = (Nat|in?(0,4)) -> Word32

  % hash values used by SHA-224 and SHA-256 (256 bits total):

  type Hash256 = (Nat|in?(0,7)) -> Word32

  % hash values used by SHA-384 and SHA-512 (512 bits total):

  type Hash512 = (Nat|in?(0,7)) -> Word64

  % initial hash value for SHA-1 [FIPS 5.3.1]:

  op sha1H0 : Hash160 = fn
    | 0 -> toWord32 0x67452301
    | 1 -> toWord32 0xefcdab89
    | 2 -> toWord32 0x98badcfe
    | 3 -> toWord32 0x10325476
    | 4 -> toWord32 0xc3d2e1f0

  % initial hash value for SHA-224 [FIPS Change Notice 1]:

  op sha224H0 : Hash256 = fn
    | 0 -> toWord32 0xc1059ed8
    | 1 -> toWord32 0x367cd507
    | 2 -> toWord32 0x3070dd17
    | 3 -> toWord32 0xf70e5939
    | 4 -> toWord32 0xffc00b31
    | 5 -> toWord32 0x68581511
    | 6 -> toWord32 0x64f98fa7
    | 7 -> toWord32 0xbefa4fa4

  % initial hash value for SHA-256 [FIPS 5.3.2]:

  op sha256H0 : Hash256 = fn
    | 0 -> toWord32 0x6a09e667
    | 1 -> toWord32 0xbb67ae85
    | 2 -> toWord32 0x3c6ef372
    | 3 -> toWord32 0xa54ff53a
    | 4 -> toWord32 0x510e527f
    | 5 -> toWord32 0x9b05688c
    | 6 -> toWord32 0x1f83d9ab
    | 7 -> toWord32 0x5be0cd19

  % initial hash value for SHA-384 [FIPS 5.3.3]:

  op sha384H0 : Hash512 = fn
    | 0 -> toWord64 0xcbbb9d5dc1059ed8
    | 1 -> toWord64 0x629a292a367cd507
    | 2 -> toWord64 0x9159015a3070dd17
    | 3 -> toWord64 0x152fecd8f70e5939
    | 4 -> toWord64 0x67332667ffc00b31
    | 5 -> toWord64 0x8eb44a8768581511
    | 6 -> toWord64 0xdb0c2e0d64f98fa7
    | 7 -> toWord64 0x47b5481dbefa4fa4

  % initial hash value for SHA-512 [FIPS 5.3.4]:

  op sha512H0 : Hash512 = fn
    | 0 -> toWord64 0x6a09e667f3bcc908
    | 1 -> toWord64 0xbb67ae8584caa73b
    | 2 -> toWord64 0x3c6ef372fe94f82b
    | 3 -> toWord64 0xa54ff53a5f1d36f1
    | 4 -> toWord64 0x510e527fade682d1
    | 5 -> toWord64 0x9b05688c2b3e6c1f
    | 6 -> toWord64 0x1f83d9abfb41bd6b
    | 7 -> toWord64 0x5be0cd19137e2179

  (* For each block i (1 <= i <= N) of message M, SHA-1 computes a message
  schedule W, which consists of 80 (32-bit) words, in step 1 of the main loop
  [FIPS 6.1.2]. *)

  type SHA1MessageSchedule = (Nat|in?(0,79)) -> Word32

  op sha1W (M:Message64, i:PosNat | i <= N512 M) : SHA1MessageSchedule =
    % block i of message M (we use i-1 because op @ indexes sequence elements
    % starting from 0, while op sha1W indexes blocks starting from 1):
    let Mi = (parsed512 M) @ (i-1) in
    % abbreviation for readability:
    let W = sha1W (M, i) in
    % message schedule:
    fn t:(Nat|in?(0,79)) ->
      if t < 16 then Mi t
      else rotateLeft (W(t-3) xor W(t-8) xor W(t-14) xor W(t-16), 1)

  (* For each block i (1 <= i <= N) of message M, SHA-1 initializes the five
  working variables (a,b,c,d,e) in step 2 of the main loop [FIPS 6.1.2] and then
  updates them 80 times in the loop in step 3 of the main loop [FIPS 6.1.2]. For
  0 <= t <= 79, sha1abcde(M,i,t) returns the values of (a,b,c,d,e) just before
  iteration t of the loop in step 3 (and in particular, sha1abcde(M,i,0) returns
  the values of (a,b,c,d,e) as initialized in step 2), while sha1abcde(M,i,80)
  returns the values of (a,b,c,d,e) at the end of step 3 (which are also the
  values of (a,b,c,d,e) at step 4).

  For each block i (1 <= i <= N) of message M, SHA-1 computes an intermediate
  hash value.

  Note that ops sha1abcde and sha1H are mutually recursive. *)


  op sha1abcde (M:Message64, i:PosNat, t:Nat | i <= N512 M && t <= 80)
               : Word32 * Word32 * Word32 * Word32 * Word32 =
    % hash value from previous iteration of the main loop,
    % or initial hash value if i = 1 (i.e. if i-1 = 0):
    let Hi_1 = sha1H (M, i-1) in
    % abbreviation for readability:
    let (a,b,c,d,e) = sha1abcde (M, i-1, t) in
    % values of (a,b,c,d,e) at the beginning of iteration 0 of the loop in
    % step 3, assigned in step 2:
    if t = 0 then (Hi_1 0, Hi_1 1, Hi_1 2, Hi_1 3, Hi_1 4)
    % updated values of (a,b,c,d,e):
    else let T:Word32 = rotateLeft (a, 5)
                   PLUS f t (b,c,d)
                   PLUS e
                   PLUS K t
                   PLUS sha1W(M,i) t in
         (T,                  % updated a
          a,                  % updated b
          rotateLeft (b, 30), % updated c
          c,                  % updated d
          d)                  % updated e

  op sha1H (M:Message64, i:PosNat | i <= N512 M) : Hash160 =
    if i = 0 then
      sha1H0  % initial hash value
    else
      % values of (a,b,c,d,e) at the end of step 3:
      let (a,b,c,d,e) = sha1abcde (M, i, 80) in
      % step 4:
      let Hi_1 = sha1H (M, i-1) in
      fn | 0 -> a PLUS Hi_1 0
         | 1 -> b PLUS Hi_1 1
         | 2 -> c PLUS Hi_1 2
         | 3 -> d PLUS Hi_1 3
         | 4 -> e PLUS Hi_1 4

  % result of SHA-1 [FIPS 6.1.2]:

  op sha1 (M:Message64) : (FSeq Bit | ofLength? 160) =
    let N = N512 M in
    let HN = sha1H (M, N) in
    HN 0 ++ HN 1 ++ HN 2 ++ HN 3 ++ HN 4

  (* For each block i (1 <= i <= N) of message M, SHA-224/256 computes a message
  schedule W, which consists of 64 (32-bit) words, in step 1 of the main loop
  [FIPS 6.2.2]. *)

  type SHA2MessageSchedule = (Nat|in?(0,63)) -> Word32

  op sha2W (M:Message64, i:PosNat | i <= N512 M) : SHA2MessageSchedule =
    % block i of message M (we use i-1 because op @ indexes sequence elements
    % starting from 0, while op sha1W indexes blocks starting from 1):
    let Mi = (parsed512 M) @ (i-1) in
    % abbreviation for readability:
    let W = sha2W (M, i) in
    % message schedule:
    fn t:(Nat|in?(0,63)) ->
      if t < 16 then Mi t
      else sigma256_1 (W (t-2))
      PLUS W (t-7)
      PLUS sigma256_0 (W (t-15))
      PLUS W (t-16)

  (* Since SHA-224 and SHA-256 use different initial hash values, the following
  three ops are parameterized over the initial hash value. *)

  (* For each block i (1 <= i <= N) of message M, SHA-224/256 initializes the
  eight working variables (a,b,c,d,e,f,g,h) in step 2 of the main loop [FIPS
  6.2.2] and then updates them 64 times in the loop in step 3 of the main loop
  [FIPS 6.2.2]. For 0 <= t <= 63, sha2abcdefgh(M,i,t,...) returns the values of
  (a,b,c,d,e,f,g,h) just before iteration t of the loop in step 3 (and in
  particular, sha2abcdefgh(M,i,0,...) returns the values of (a,b,c,d,e,f,g,h) as
  initialized in step 2), while sha2abcdefgh(M,i,64,...) returns the values of
  (a,b,c,d,e,f,g,h) at the end of step 3 (which are also the values of
  (a,b,c,d,e,f,g,h) at step 4).

  For each block i (1 <= i <= N) of message M, SHA-224/256 computes an
  intermediate hash value.

  Note that ops sha2abcdefgh and sha2H are mutually recursive. *)

  op sha2abcdefgh
     (M:Message64, i:PosNat, t:Nat, H0:Hash256 | i <= N512 M && t <= 64)
     : Word32 * Word32 * Word32 * Word32 * Word32 * Word32 * Word32 * Word32 =
    % hash value from previous iteration of the main loop,
    % or initial hash value if i = 1 (i.e. if i-1 = 0):
    let Hi_1 = sha2H (M, i-1, H0) in
    % abbreviation for readability:
    let (a,b,c,d,e,f,g,h) = sha2abcdefgh (M, i-1, t, H0) in
    % values of (a,b,c,d,e,f,g,h) at the beginning of iteration 0 of the loop in
    % step 3, assigned in step 2:
    if t = 0 then
      (Hi_1 0, Hi_1 1, Hi_1 2, Hi_1 3, Hi_1 4, Hi_1 5, Hi_1 6, Hi_1 7)
    % updated values of (a,b,c,d,e,f,g,h):
    else let T1:Word32 = h
                    PLUS Sigma256_1 e
                    PLUS Ch (e,f,g)
                    PLUS K256 t
                    PLUS sha2W(M,i) t in
         let T2:Word32 = Sigma256_0 a
                    PLUS Maj (a,b,c) in
         (T1 PLUS T2, % updated a
          a,          % updated b
          b,          % updated c
          c,          % updated d
          d PLUS T1,  % updated e
          e,          % updated f
          f,          % updated g
          g)          % updated h

  op sha2H (M:Message64, i:PosNat, H0:Hash256 | i <= N512 M) : Hash256 =
    if i = 0 then
      H0  % initial hash value
    else
      % values of (a,b,c,d,e,f,g,h) at the end of step 3:
      let (a,b,c,d,e,f,g,h) = sha2abcdefgh (M, i, 64, H0) in
      % step 4:
      let Hi_1 = sha2H (M, i-1, H0) in
      fn | 0 -> a PLUS Hi_1 0
         | 1 -> b PLUS Hi_1 1
         | 2 -> c PLUS Hi_1 2
         | 3 -> d PLUS Hi_1 3
         | 4 -> e PLUS Hi_1 4
         | 5 -> f PLUS Hi_1 5
         | 6 -> g PLUS Hi_1 6
         | 7 -> h PLUS Hi_1 7

  % flattened bits of final hash value [FIPS 6.2.2]:

  op sha2 (M:Message64, H0:Hash256) : (FSeq Bit | ofLength? 256) =
    let N = N512 M in
    let HN = sha2H (M, N, H0) in
    HN 0 ++ HN 1 ++ HN 2 ++ HN 3 ++ HN 4 ++ HN 5 ++ HN 6 ++ HN 7

  % all bits of final hash value for SHA-256:

  op sha256 (M:Message64) : (FSeq Bit | ofLength? 256) =
    sha2 (M, sha256H0)

  % truncate bits of final hash values for SHA-224:

  op sha224 (M:Message64) : (FSeq Bit | ofLength? 224) =
    prefix (sha2 (M, sha224H0), 224)

  (* For each block i (1 <= i <= N) of message M, SHA-384/512 computes a message
  schedule W, which consists of 80 (64-bit) words, in step 1 of the main loop
  [FIPS 6.3.2]. *)

  type SHA3MessageSchedule = (Nat|in?(0,79)) -> Word64

  op sha3W (M:Message128, i:PosNat | i <= N1024 M) : SHA3MessageSchedule =
    % block i of message M (we use i-1 because op @ indexes sequence elements
    % starting from 0, while op sha1W indexes blocks starting from 1):
    let Mi = (parsed1024 M) @ (i-1) in
    % abbreviation for readability:
    let W = sha3W (M, i) in
    % message schedule:
    fn t:(Nat|in?(0,79)) ->
      if t < 16 then Mi t
      else sigma512_1 (W (t-2))
      PLUS W (t-7)
      PLUS sigma512_0 (W (t-15))
      PLUS W (t-16)

  (* Since SHA-384 and SHA-512 use different initial hash values, the following
  three ops are parameterized over the initial hash value. *)

  (* For each block i (1 <= i <= N) of message M, SHA-384/512 initializes the
  eight working variables (a,b,c,d,e,f,g,h) in step 2 of the main loop [FIPS
  6.3.2] and then updates them 80 times in the loop in step 3 of the main loop
  [FIPS 6.3.2]. For 0 <= t <= 79, sha3abcdefgh(M,i,t,...) returns the values of
  (a,b,c,d,e,f,g,h) just before iteration t of the loop in step 3 (and in
  particular, sha3abcdefgh(M,i,0,...) returns the values of (a,b,c,d,e,f,g,h) as
  initialized in step 2), while sha3abcdefgh(M,i,80,...) returns the values of
  (a,b,c,d,e,f,g,h) at the end of step 3 (which are also the values of
  (a,b,c,d,e,f,g,h) at step 4).

  For each block i (1 <= i <= N) of message M, SHA-384/512 computes an
  intermediate hash value.

  Note that ops sha3abcdefgh and sha3H are mutually recursive. *)

  op sha3abcdefgh
     (M:Message128, i:PosNat, t:Nat, H0:Hash512 | i <= N1024 M && t <= 80)
     : Word64 * Word64 * Word64 * Word64 * Word64 * Word64 * Word64 * Word64 =
    % hash value from previous iteration of the main loop,
    % or initial hash value if i = 1 (i.e. if i-1 = 0):
    let Hi_1 = sha3H (M, i-1, H0) in
    % abbreviation for readability:
    let (a,b,c,d,e,f,g,h) = sha3abcdefgh (M, i-1, t, H0) in
    % values of (a,b,c,d,e,f,g,h) at the beginning of iteration 0 of the loop in
    % step 3, assigned in step 2:
    if t = 0 then
      (Hi_1 0, Hi_1 1, Hi_1 2, Hi_1 3, Hi_1 4, Hi_1 5, Hi_1 6, Hi_1 7)
    % updated values of (a,b,c,d,e,f,g,h):
    else let T1:Word64 = h
                    PLUS Sigma512_1 e
                    PLUS Ch (e,f,g)
                    PLUS K512 t
                    PLUS sha3W(M,i) t in
         let T2:Word64 = Sigma512_0 a
                    PLUS Maj (a,b,c) in
         (T1 PLUS T2, % updated a
          a,          % updated b
          b,          % updated c
          c,          % updated d
          d PLUS T1,  % updated e
          e,          % updated f
          f,          % updated g
          g)          % updated h

  op sha3H (M:Message128, i:PosNat, H0:Hash512 | i <= N1024 M) : Hash512 =
    if i = 0 then
      H0  % initial hash value
    else
      % values of (a,b,c,d,e,f,g,h) at the end of step 3:
      let (a,b,c,d,e,f,g,h) = sha3abcdefgh (M, i, 80, H0) in
      % step 4:
      let Hi_1 = sha3H (M, i-1, H0) in
      fn | 0 -> a PLUS Hi_1 0
         | 1 -> b PLUS Hi_1 1
         | 2 -> c PLUS Hi_1 2
         | 3 -> d PLUS Hi_1 3
         | 4 -> e PLUS Hi_1 4
         | 5 -> f PLUS Hi_1 5
         | 6 -> g PLUS Hi_1 6
         | 7 -> h PLUS Hi_1 7

  % flattened bits of final hash value [FIPS 6.3.2]:

  op sha3 (M:Message128, H0:Hash512) : (FSeq Bit | ofLength? 512) =
    let N = N1024 M in
    let HN = sha3H (M, N, H0) in
    HN 0 ++ HN 1 ++ HN 2 ++ HN 3 ++ HN 4 ++ HN 5 ++ HN 6 ++ HN 7

  % all bits of final hash value for SHA-512:

  op sha512 (M:Message64) : (FSeq Bit | ofLength? 512) =
    sha3 (M, sha512H0)

  % truncate bits of final hash values for SHA-224:

  op sha384 (M:Message64) : (FSeq Bit | ofLength? 384) =
    prefix (sha3 (M, sha384H0), 384)

endspec
