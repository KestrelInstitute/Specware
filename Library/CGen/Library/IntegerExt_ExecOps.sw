(* We refine the ops in spec IntegerExt to be executable. We refine all the ops
that can be made executable. Of course, we cannot refine the others (e.g. minIn,
which operates on a potentially infinite set). *)

spec

  import IntegerExt

  refine def ** (base:Int, exp:Nat) : Int =
  % exponentiation by squaring (well-known algorithm):
    if exp = 0 then
      1
    else if exp = 1 then
      base
    else if even? exp then
      (base * base) ** (exp / 2)
    else
      base * ((base * base) ** ((exp - 1) / 2))

  refine def isqrt (n:Nat) : Nat =
  % naive generate-and-test loop (OK for not-too-large numbers):
    let def loop (i:PosNat) : Nat =
        if i * i > n then i - 1 else loop (i + 1) in
    loop 1

  refine def primesLessThan (limit:Nat) : InjList PrimeNat =
  % sieve of Erathostenes:
    if limit <= 2 then [] else  % no primes less than 2
    let initialList =  % [2, 3, 4, ..., limit-1]
        tabulate (limit - 2, fn i:Nat -> i + 2) in
    % if a number less than limit is not prime, it must have at least a factor
    % not exceeding the integer square root of limit; so, we can stop the
    % sieving when we reach isqrt(limit), see loop below:
    let stoppingValue = isqrt limit in
    % tail-recursive function to do one pass of the sieve:
    let def loop (stillToProcess : List PosNat,
                  primesSoFar    : List PosNat)  % accumulated in reverse order
                 : List PosNat =
        case stillToProcess of
        | [] ->  % finished
          reverse primesSoFar
        | hd::tl ->
          if hd > stoppingValue then  % finished
            reverse primesSoFar ++ stillToProcess
              % we also return the numbers that are still to process because
              % if they have no factor not exceeding isqrt(limit), then, since
              % they are all less than limit, they must be all prime
          else
            loop (filter (fn x:Nat -> ~ (hd divides x)) tl,
                    % only keep numbers that are not multiple of first number
                  hd :: primesSoFar)
                    % add hd to list of primes
    in loop (initialList, [])

  refine def prime? (n:Nat) : Bool =
    % compute primes less than n+1 and check if n is in the list:
    n in? primesLessThan (n+1)

  refine def coprime? (n1:Nat, n2:Nat) : Bool =
    (n1 = 0 && n2 = 1) ||
    (n2 = 0 && n1 = 1) ||
    (n1 ~= 0 && n2 ~= 0 && gcd (n1, n2) = 1)

  refine def primeFactorsOf (n:PosNat) : List PrimeNat =
  % naive algorithm:
    % these are all the primes that might be factors of n (they are <= n):
    let potentialFactors: InjList PrimeNat = primesLessThan (n + 1) in
    % tail-recursive function to accumulate and return the list of factors:
    let def loop (potentialFactors: InjList PrimeNat,
                  n:PosNat, actualFactors: List PrimeNat |
                  n ~= 1 => nonEmpty? potentialFactors) : List PrimeNat =
        if n = 1 then  % finished
          reverse actualFactors
        else
          let f = head potentialFactors in
          % if smallest potential factor f divides n, divide n by f, add f to
          % actual factors, and continue (leaving f among potential factors, as
          % f may divide n again):
          if f divides n then
            loop (potentialFactors, n div f, f::actualFactors)
          else
            loop (tail potentialFactors, n, actualFactors)
    in loop (potentialFactors, n, [])

  refine def totient (n:PosNat) : Nat =
    length (filter (fn m:PosNat -> m <= n && coprime? (m,n))
                   (tabulate (n, fn i:Nat -> i+1)))  % = [1,...,n]

  refine def littleEndian? (digits: List Nat, base:Nat, x:Nat) : Bool =
    forall? (fn d:Nat -> d < base) digits &&
    (let weights: List Nat = tabulate (length digits, fn i:Nat -> base**i) in
    x = foldl (+) 0 (map2 ( * ) (digits, weights)))

  refine def fromBigEndian
     (digits: List Nat, base:Nat |
      base >= 2 && (fa(d:Nat) d in? digits => d < base)) : Nat =
    let def loop (digits: List Nat, result:Nat) : Nat =
        case digits of
        | [] -> result
        | d::moreDigits -> loop (moreDigits, d + result * base)
    in
    loop (digits, 0)

  refine def fromLittleEndian
     (digits: List Nat, base:Nat |
      base >= 2 && (fa(d:Nat) d in? digits => d < base)) : Nat =
    fromBigEndian (reverse digits, base)

  refine def toMinBigEndian (x:Nat, base:Nat | base >= 2) : List1 Nat =
    let def loop (x:Nat, result: List Nat) : List Nat =
        if x = 0 then result
        else loop (x div base, (x mod base) :: result)
    in
    let digits = loop (x, []) in
    if digits = [] then [0] else digits

  refine def toMinLittleEndian (x:Nat, base:Nat | base >= 2) : List1 Nat =
    reverse (toMinBigEndian (x, base))

  refine def toBigEndian
     (x:Nat, base:Nat, len:Nat | base >= 2 && x < base**len) : List Nat =
    if len = 0 then []
    else extendLeft (toMinBigEndian (x, base), 0, len)

  refine def toLittleEndian
     (x:Nat, base:Nat, len:Nat | base >= 2 && x < base**len) : List Nat =
    if len = 0 then []
    else extendRight (toMinLittleEndian (x, base), 0, len)

endspec
