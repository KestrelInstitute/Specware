(*
2007:07:19
AC
A spec for ECC.

2007:07:31
AC
Added MQV with cofactor multiplication.

ISSUE:
This spec should be suitably factored, extended, and generalized (see comments
below).

*)


ECCP qualifying spec

  import /Library/General/FiniteSets, /Library/General/Assert, NatExt

  (* This spec defines (part of) Elliptic Curve Cryptography (ECC) over prime
  fields, as specified in the "IEEE Standard Specifications for Public-Key
  Cryptography 1363-2000".

  In the comments in this spec, we refer to that IEEE standard as "[IEEE]",
  possibly extended with references to (sub)sections (e.g. "[IEEE 7.1.2]").

  This spec should be eventually factored, extended, and generalized. For
  example: the notion of prime field should be factored into a separate spec,
  imported by this spec; the notion of elliptic curve should be generalized to
  arbitrary fields and factored into a separate spec, instantiated and imported
  by this spec; additional signature and verification primitives should be
  added; signature primitives should be generalized to arbitrary cyclic groups
  and factored into a separate spec for discrete logarithm cryptography; ECC
  over binary fields should be added; and so on. *)

  (* We start with the notion of prime field, i.e. the finite field consisting
  of the natural numbers {0,1,...,p-1} less than a prime number p [IEEE A.1.2].
  Since the field is completely determined by the prime number p, we identify
  (in the context of this spec) a field with a prime number. More information on
  (prime) fields can be readily found, e.g. on Wikipedia or in textbooks. *)

  type Field = PrimeNat

  % field operations defined in terms of modular arithmetic (note that 0 and 1
  % are always the field's "zero" and "one", for any p):

  op addF (p:Field, x:Nat, y:Nat | x < p && y < p) : Nat =  % addition
    (x + y) rem p

  op negF (p:Field, x:Nat | x < p) : Nat =  % additive inverse
    the(y:Nat) addF(p,x,y) = 0

  op subF (p:Field, x:Nat, y:Nat | x < p && y < p) : Nat =  % subtraction
    addF (p, x, negF (p, y))

  op mulF (p:Field, x:Nat, y:Nat | x < p && y < p) : Nat =  % multiplication
    (x * y) rem p

  op invF (p:Field, x:PosNat | x < p) : Nat =  % multiplicative inverse
    the(y) mulF (p, x, y) = 1

  op divF (p:Field, x:Nat, y:PosNat | x < p && y < p) : Nat =  % division
    mulF (p, x, invF (p, y))

  op powF (p:Field, x:Nat, e:Integer | x < p && (e < 0 => x ~= 0)) : Nat =
    % raise to power (negative exponent requires non-zero base)
    if e = 0 then 1
    else if e > 0 then mulF (p, x, powF (p, x, e-1))
    else (* e < 0 *) powF (p, invF (p, x), -e)

  % coerce any natural number to a field element (see its use later):
  op toField (p:Field) (x:Nat) : Nat = x rem p

  (* An elliptic curve over an odd prime field [IEEE A.9.1] is described by the
  equation (y^2 = x^3 + ax + b), with a and b such that (4a^3 + 27b^2 ~= 0).
  Therefore, the curve is completely described by a field (i.e. prime number) p
  and the two field coefficients a and b; we identify the curve with their
  triple. Only odd prime fields are used in ECC; this only excludes 2
  theoretically, but in practice p's much larger than 3 are used. However, since
  our notion of elliptic curve below allows p to be 3, 5, 7, etc., we use op
  toField to coerce 4 and 27 into field elements (in practice p is much larger
  than 27 and so op toField leaves 4 and 27 unchanged). *)

  type Curve = {(p,a,b) : Field * Nat * Nat |
                odd? p && a < p && b < p &&
                addF (p, mulF (p, toField p  4, powF (p, a, 3)),
                         mulF (p, toField p 27, powF (p, b, 2))) ~= 0}

  (* The points of a curve are all the pairs (x,y) that satisfy the curve
  equation, plus a point at infinity denoted "O". Points that are pairs (x,y)
  are called "finite points". We model points via a Metaslang sum type, where
  the constructor "F" stands for "finite (point)". Another acceptable modeling
  strategy (typically used in implementations) is to represent O as a particular
  pair (x,y) that does not satisfy the curve equation, namely (0,0) if b ~= 0
  and (0,1) if b = 0 [IEEE A.9.3]. All in all, it seems that using a sum type is
  more readable. *)

  type Point = | F Nat * Nat
               | O

  op in? (P:Point, E:Curve) infixl 20 : Boolean =
    case P of
    % point at infinity always belongs to curve by definition:
    | O -> true
    % finite point belongs to curve iff it satisfies equation:
    | F(x,y) ->
      let (p,a,b) = E in
      mulF (p, y, 2) = addF (p,
                       addF (p, powF (p, x, 3),
                                mulF (p, a, x)),
                                b)

  % order of curve = number of points that belong to the curve:

  op orderC (E:Curve) : Nat = size (fn P:Point -> P in? E)

  % additive inverse of a point on the curve [IEEE A.9.2]:

  op negP (E:Curve, P:Point | P in? E) : Point =
    let (p,_,_) = E in
    case P of
    | O -> O
    | F(x,y) -> F (x, negF(p,y))

  % addition of points on the curve (paraphrased from [IEEE A.10.1], which
  % provides a procedural description):

  op addP (E:Curve, P0:Point, P1:Point | P0 in? E && P1 in? E) : Point =
    let (p, a, b) = E in
    case (P0,P1) of
    % point at infinity is additive identity (so return other point):
    | (O,P1) -> P1
    | (P0,O) -> P0
    % if we have two finite points:
    | (F(x0,y0), F(x1,y1)) ->
      (* The curve is symmetric w.r.t. to the x axis. So, if two points have
      identical x and different y, they are distinct points that are opposites
      (i.e. inverses), and so their sum is the additive identity, i.e. the point
      at infinity O. If two points have identical x and one has null y, the
      other one must have null y too, and so the two points coincide but they
      are also opposites (they both lie on the x axis) and their sum is O. *)
      if x0 = x1 && (y0 ~= y1 || y1 = 0) then
        (assert (P0 = negP (E, P1));
        O)
      (* Otherwise, the two points are not inverses and their sum yields a
      finite point, computed as follows. *)
      else
        (* The computation differs depending on whether the two points are
        distinct or coincide. This difference can be factored into the
        computation of lambda (which differs in the two cases) but then the rest
        of the computation is the same. We apply op toField to 3 in case that p
        is 3; this would never happen in practice, since much larger values of p
        are used, but mathematically it is allowed in our definition of elliptic
        curve. *)
        let lambda = if x0 ~= x1 then
                       (assert (P0 ~= P1);
                       divF (p, subF (p, y0, y1), subF (p, x0, x1)))
                     else
                       (assert (P0 = P1);
                       divF (p, addF (p, mulF (p, toField p 3, powF (p, x1, 2)),
                                         a),
                                mulF (p, 2, y1))) in
        % once we have lambda, the remaining computation is the same:
        let x2 = subF (p, subF (p, powF (p, lambda, 2), x0), x1) in
        let y2 = subF (p, mulF (p, subF (p, x1, x2), lambda), y1) in
        F (x2, y2)

  % scalar multiplication [IEEE A.9.2] (i.e. iterated sum):

  op mulP (E:Curve, n:Integer, P:Point) : Point =
    if n = 0 then O
    else if n > 0 then addP (E, P, mulP (E, n-1, P))
    else (* n < 0 *)   mulP (E, -n, negP (E, P))

  % order of point in curve (group) [IEEE A.9.3]:

  op orderP (E:Curve, P:Point | P in? E) : Nat =
    minIn (fn r:Integer -> r > 0 &&
      mulP (E, r, P) = O)

  (* The domain parameters of ECC [IEEE 7.1.2] are a prime field p, two elliptic
  curve coefficients a and b defining a curve E, a prime divisor r of the number
  of points of E, and a point G of E of order r (the generator of the cyclic
  subgroup of order r). In our model, E consists of p, a, and b, so the domain
  parameters are E plus r and G. *)

  type DomainParams = {(E,r,G) : Curve * PrimeNat * Point |
                       r divides orderC E && G in? E && orderP(E,G) = r}

  (* The cofactor is another domain parameter that is specified implicitly,
  because it can be derived from the other parameters. *)

  op cofactor ((E,r,G):DomainParams) : Nat = (orderC E) div r

  (* For certain cryptographic operations, the cofactor and the order r of G
  must be coprime, which is formalized by the following predicate and
  subtype. *)

  op coprimeKR? ((E,r,G):DomainParams) : Boolean = coprime? (cofactor(E,r,G), r)

  type DomainParamsCoprimeKR = (DomainParams | coprimeKR?)

  (* A private key for given domain parameters is a natural number in the range
  [1,r-1] [IEEE 7.1.3]. *)

  type PrivateKey = Nat

  op privateKeyFor? (s:PrivateKey, (E,r,G):DomainParams) infixl 20 : Boolean =
    1 <= s && s < r

  (* A public key is a point of the cyclic subgroup, which is derivable from the
  private key by simple scalar multiplication [IEEE 7.1.3]. *)

  type PublicKey = Point

  op publicKeyOf ((E,r,G):DomainParams, s:PrivateKey | s privateKeyFor? (E,r,G))
                 : PublicKey =
    mulP (E, s, G)

  op keyPairFor? ((s,W): PrivateKey * PublicKey, dp:DomainParams)
                 infixl 20 : Boolean =
    s privateKeyFor? dp && W = publicKeyOf (dp, s)

  op publicKeyFor? (W:PublicKey, dp:DomainParams) infixl 20 : Boolean =
    ex(s:PrivateKey) (s,W) keyPairFor? dp

  (* For now we only formalize the DSA version of elliptic curve signature [IEEE
  7.2.7, 7.2.8]. The Nyberg-Rueppel version [IEEE 7.2.5, 7.2.6] will be
  formalized in the future. *)

  % a message (representative) f is simply a natural number:

  type Message = Nat

  % a signature is a pair of natural numbers (in certain ranges, see below):

  type Signature = Nat * Nat

  (* Given domain parameters dp, a private key s, and a message f, signing
  involves the generation of a (one-time) key pair (u,V). So, the following op
  takes such a pair as an additional parameter. *)

  op dsaSign
     (dp:DomainParams, s:PrivateKey, f:Message, u:PrivateKey, V:PublicKey |
      s privateKeyFor? dp && (u,V) keyPairFor? dp) : Signature =
    let (E,r,_) = dp in
    let (p,_,_) = E in
    let F(x,_) = V in
    let c = x rem r in
    let u_1 = invF(r,u) in
    let d = mulF (r, u_1, addF (r, toField r f, mulF (r, s, c))) in
    (c, d)

  (* The following op returns all possible signatures of a message f with a
  private key s w.r.t. domain parameters dp. There is a signature for each
  possible key pair (u,V) generated during the signing procedure. However, if
  either component of the signature (c,d) are 0, the signing procedure generates
  another key pair and tries the computation again. Correspondingly, signatures
  (c,d) with a null component are excluded from the set returned by the
  following op. The set is finite because everything (the field, the curve,
  etc.) is finite. *)

  op dsaSignatures
     (dp:DomainParams, s:PrivateKey, f:Message | s privateKeyFor? dp)
     : FSet Signature =
    toFSet (fn (c,d):Signature ->
      ex (u:PrivateKey, V:PublicKey)
        (u,V) keyPairFor? dp &&
        dsaSign (dp, s, f, u, V) = (c, d) &&
        c ~= 0 && d ~= 0)

  % the components of the signature are always in the range [1,r-1]:

  conjecture signature_components_range is
    fa (dp:DomainParams, s:PrivateKey, f:Message, sig:Signature)
      s privateKeyFor? dp &&
      sig in? dsaSignatures (dp, s, f) =>
      (let (c,d) = sig in
       let (_,r,_) = dp in
       1 <= c && c < r &&
       1 <= d && d < r)

  (* The following op captures the process of verifying a signature (c,d) for a
  message f, signed by the entity whose public key is W, w.r.t. domain
  parameters dp. *)

  op dsaVerify? (dp:DomainParams, W:PublicKey, f:Message, (c,d):Signature |
                 W publicKeyFor? dp) : Boolean =
    let (E,r,G) = dp in
    1 <= c && c < r &&
    1 <= d && d < r &&
    (let h = invF(r,d) in
     let h1 = mulF (r, toField r f, h) in
     let h2 = mulF (r, c, h) in
     let P = addP (E, mulP (E, h1, G), mulP (E, h2, W)) in
     case P of
     | O -> false
     | F(x,y) ->
       let c' = x rem r in
       c' = c)

  % valid signatures pass verification:

  conjecture valid_signatures_are_verified is
    fa (dp:DomainParams, s:PrivateKey, W:PublicKey, f:Message, sig:Signature)
      (s,W) keyPairFor? dp &&
      sig in? dsaSignatures (dp, s, f) =>
      dsaVerify? (dp, W, f, sig)

  (* For now we only formalize the MQV with cofactor multiplication version of
  elliptic curve key secret value derivation [IEEE 7.2.4]. MQV without cofactor
  multiplication [IEEE 7.2.3], as well as Diffie-Hellman with and without
  cofactor multiplication [IEEE 7.2.1, 7.2.2], will be formalized in the
  future. Also, in formalizing MQV with cofactor multiplication, for now we do
  not cover compatibility with MQV without cofactor multiplication. *)

  (* The following op computes a secret natural number from the party's own
  first private key s, the party's own second key pair (u,V), the other party's
  first public key W', and the other party's second public key V'. The keys must
  be all valid w.r.t. to the domain parameters, which must be such that the
  cofactor and the order of the generator are coprime. The op returns an
  optional value to cover the case that the computed point P is O, which
  according to [IEEE 7.2.4] should output "invalid public key".

  [IEEE 7.2.4] defines h = ceil ((log_2 r) / 2), where ceil is the ceiling
  function. In the following definition, instead, we (effectively) define h =
  ceil (ceil (log_2 r) / 2). It is not hard to prove that the two definitions
  are equivalent. (Indeed, NIST Special Publication 800-56A defines h as we do
  in this spec.) *)

  op mqvcSecret (dp:DomainParamsCoprimeKR,
                 s:PrivateKey, u:PrivateKey, V:PublicKey,
                 W':PublicKey, V':PublicKey |
                 s privateKeyFor? dp &&
                 (u,V) keyPairFor? dp &&
                 W' publicKeyFor? dp &&
                 V' publicKeyFor? dp) : Option Nat =
    let F(x,_) = V in
    let F(x',_) = V' in
    let (E,r,_) = dp in
    let k = cofactor dp in
    let log2r = minIn (fn log2r:Integer -> log2r > 0 && 2**log2r >= r) in
    let h = if even? log2r then log2r div 2 else (log2r + 1) div 2 in
    let i = x in
    let t = i rem 2**h + 2**h in
    let i' = x' in
    let t' = i' rem 2**h + 2**h in
    let e = addF (r, mulF (r, t, s), u) in
    let P = mulP (E, k, mulP (E, e, addP (E, V', mulP (E, t', W')))) in
    case P of
    | O -> None
    | F(x,_) -> Some x

  (* Given two key pairs for each party A and B, with shared public keys, the
  two parties share the computed secret. *)

  conjecture secret_is_shared is
    fa (dp:DomainParamsCoprimeKR,
        s :PrivateKey, W :PublicKey,  % party A's first  key pair
        u :PrivateKey, V :PublicKey,  % party A's second key pair
        s':PrivateKey, W':PublicKey,  % party B's first  key pair
        u':PrivateKey, V':PublicKey)  % party B's second key pair
      (s, W)  keyPairFor? dp &&
      (u, V)  keyPairFor? dp &&
      (s',W') keyPairFor? dp &&
      (u',V') keyPairFor? dp =>
      mqvcSecret (dp, s, u, V, W', V')   % computed by party A
      =
      mqvcSecret (dp, s', u', V', W, V)  % computed by party B

  (* Sometimes the party's own second key pair is the same as the party's own
  first key pair. This is the case, for example, in the One-Pass MQV key
  agreement scheme specified in NIST Special Publication 800-56A. The following
  op captures this special case. *)

  op mqvcSecretSameKeys (dp:DomainParamsCoprimeKR,
                         s:PrivateKey, W':PublicKey, V':PublicKey |
                         s privateKeyFor? dp &&
                         W' publicKeyFor? dp &&
                         V' publicKeyFor? dp) : Option Nat =
    let W = publicKeyOf (dp, s) in
    mqvcSecret (dp, s, s, W, W', V')

  (* When the party's own second key pair differs from the party's own first
  keys, the second key pair is typically generated on the fly as part of the key
  agreement scheme. The public key of the second pair is typically sent to the
  other party. This happens, for example, in the Full MQV key agreement scheme
  specified in NIST Special Publication 800-56A. So, the operation performed by
  the party yields not only a secret (a natural number) but also a key pair.
  The following op returns the set of all possible results of that operation,
  where a result consists of (1) a secret and (2) a key pair. The set is finite
  because everything (the field, the curve, etc.) is finite. *)

  op mqvcSecretsAndKeys (dp:DomainParamsCoprimeKR,
                         s:PrivateKey, W':PublicKey, V':PublicKey |
                         s privateKeyFor? dp &&
                         W' publicKeyFor? dp &&
                         V' publicKeyFor? dp)
                        : FSet (Nat * PrivateKey * PublicKey) =
    toFSet (fn (secret,u,V): Nat * PrivateKey * PublicKey ->
        (u,V) keyPairFor? dp &&
        mqvcSecret (dp, s, u, V, W', V') = Some secret)

endspec
