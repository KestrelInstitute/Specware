(*
2007:07:05
AC
A spec for RSA.

ISSUE:
Private keys in Chinese Remainer Theorems should be added.

ISSUE:
Multi-prime moduli should be added.

*)


RSA qualifying spec

  (* This spec formalizes RSA cryptography as officially specified in the
  document "PKCS #1 v2.1: RSA Cryptography Standard" by RSA Labs. In the
  comments in this spec, We refer to that document as [PKCS1]. *)

  import NatExt, /Library/General/FiniteSets

  (* A (public or private) key consists of a modulus and an exponent, both
  natural numbers. For now, we do not formalize private keys in Chinese
  Remainder Theorem form.

  [PKCS1] provides constraints that keys must satisfy in order to be
  valid. This includes easy-to-check conditions such as the fact that modulus
  and exponent must be positive, but also the hard-to-check condition that the
  modulus must be the product of two or more distinct odd primes. The latter
  condition is hard to check computationally, and in fact the security of RSA
  cryptography rests on the assumption that factoring large numbers is hard.
  Therefore, an implemented system that makes use of RSA keys cannot generally
  establish for sure the validity of the keys. Accordingly, the type just
  below allows any pair of natural numbers, even if they violate the
  easy-to-check conditions. *)

  type Key =
   {modulus  : Nat,
    exponent : Nat}

  (* The potential non-validity of a key as just defined does not constitute a
  practical problem as far as encryption/decryption goes. Modular
  exponentiation works (i.e. it yields a well-defined result) regardless of
  the validity of the key used to perform the operation. The only
  (easy-to-check) requirement is that the modulus is not 0, because it is used
  as a divisor.

  Of course, if we encrypt/decrypt with invalid keys some expected properties
  (such as the recovery of an encrypted message) do not hold. However, the
  operations are still well-defined.

  We define the application of an RSA key to a natural number (meant to
  represent the data to encrypt/decrypt) as modular exponentiation. This
  corresponds to the encryption and decryption primitives specified in
  [PKCS1]. The operation is the same, regardless of whether the key is public
  or private.

  Even though [PKCS1] requires the natural number to be encrypted/decrypted to
  be less than the modulus, this is not required for modular exponentiation to
  work. Accordingly, we allow any natural number.

  The op is only defined on keys with a non-zero modulus, because otherwise it
  would not be possible to use the modulus as a divisor to compute the
  remainder. We resist the temptation to totalize the op by returning 0 if the
  modulus is 0, because that would be a somewhat arbitrary choice.

  It is convenient to introduce an auxiliary op to perform modular
  exponentiation. This op can be refined for efficiency and can be used in
  other contexts than RSA encryption/decryption (e.g. it can be used as part
  of RSA key generation). *)

  op nonZeroModulus? (k:Key) : Boolean = (k.modulus ~= 0)

  op powerMod (base:Nat) (exp:Nat) (mod:PosNat) : Nat = (base ** exp) rem mod

  op apply (k:Key | nonZeroModulus? k) (x:Nat) : Nat =
    powerMod x k.exponent k.modulus

  (* A key has a valid modulus if the modulus is the product of two or more
  distinct odd primes. The first predicate below includes the set of primes as
  an explicit argument, while the second predicate existentially quantifies
  over the set of primes. The third op returns the (unique) set of primes
  whose product is the (valid) modulus. *)

  op validModulusWithPrimes? (k:Key) (primes: FSet PrimeNat) : Boolean =
    size primes >= 2    &&
    forall? odd? primes &&
    k.modulus = fold (1, ( * ), primes)

  op validModulus? (k:Key) : Boolean =
    ex (primes: FSet PrimeNat) validModulusWithPrimes? k primes

  op modulusPrimes (k:Key | validModulus? k) : FSet PrimeNat =
    the(primes) validModulusWithPrimes? k primes

  (* The public exponent must be between 3 (inclusive) and the modulus
  (exclusive). In addition, it must be coprime with the result of the "lambda"
  function applied to the modulus, where the lambda function is defined in
  [PKCS1] to be the least common multiple of the set {r1 - 1, ..., ru - 1},
  where r1...ru are the u >= 2 primes whose product is the modulus. For
  convenience, we define op lambda below to operate on keys vs. numbers. *)

  op lambda (k:Key | validModulus? k) : PosNat =
    let primes = modulusPrimes k in
    let primes_1 = map (fn(p:PrimeNat) -> p - 1) primes in
    lcm (fromFSet primes_1)

  op validPublicExponent? (k:Key | validModulus? k) : Boolean =
    3 <= k.exponent && k.exponent <= k.modulus - 1 &&
    gcd2 (k.exponent, lambda k) = 1

  (* [PKCS1] describes the validity of the private exponent in relation to a
  public key. The following predicate only covers the validity conditions that
  are only expressed on the exponent in isolation. The validity conditions
  that depend on a public key are expressed by the predicate that specifies
  the validity of a key pair, below. *)

  op validPrivateExponent? (k:Key | validModulus? k) : Boolean =
    0 < k.exponent && k.exponent <= k.modulus - 1

  (* A pair of keys are valid if they have the same valid modulus, the
  exponents are valid in isolation, and the exponent are also valid together,
  i.e. they are inverses. *)

  op validPair? (public:Key) (private:Key) : Boolean =
    % same and valid modulus:
    validModulus? public             &&
    public.modulus = private.modulus &&  % => validModulus? private.modulus
    % valid exponents:
    validPublicExponent?  public     &&
    validPrivateExponent? private    &&
    % exponents are inverses:
    (public.exponent * private.exponent) rem (lambda public) = 1
                                         % = (lambda private)

  (* Valid key pairs yield inverse transformations, when applied to numbers
  less than the (common) modulus. *)

  conjecture valid_public_and_private_keys_are_inverses is
    fa (public:Key, private:Key, x:Nat)
      validPair? public private &&
      x < public.modulus (* = private.modulus *) =>
      apply public  (apply private x) = x &&
      apply private (apply public  x) = x

endspec
