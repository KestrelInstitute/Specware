(*
2005:03:18
AC
A definition of two's complement numbers as bit sequences and various
operations on them.
*)


TwosComplement qualifying spec

  (* A two's complement number is a finite sequence of bits (interpreted as an
  integer). We consider the bit sequence in big endian format, i.e. the sign
  bit is the first one and the least significant bit is the last one. *)

  import BitSequences

  type TCNumber = NonEmptyFSeq Bit

  op sign : TCNumber -> Bit = first

  op zero? (x:TCNumber) : Boolean = forall? (fn b -> b = 0) x

  op nonZero? : TCNumber -> Boolean = ~~ zero?

  type NonZeroTCNumber = (TCNumber | nonZero?)

  op negative? (x:TCNumber) : Boolean = (sign x = 1)

  op nonNegative? : TCNumber -> Boolean = ~~ negative?

  theorem nonNegative?_alt_def is
    fa(x:TCNumber) nonNegative? x <=> sign x = 0

  op positive? : TCNumber -> Boolean = nonNegative? /\ (~~ zero?)

  op nonPositive? : TCNumber -> Boolean = ~~ positive?

  % interpretation as integer:
  op toInteger (x:TCNumber) : Integer = if nonNegative? x then toNat x
                                        else toNat x - 2 ** (length x)

  theorem twos_complement_of_negative is
    fa(x:TCNumber) negative? x =>  % given negative TC number
      toNat (not x) + 1 =  % two's complement operation
        - (toInteger x)  % yields absolute value of represented integer

  % minimum integer representable as TC number of length `len':
  op minForLength (len:PosNat) : Integer = - (2 ** (len - 1))

  % maximum integer representable as TC number of length `len':
  op maxForLength (len:PosNat) : Integer = 2 ** (len - 1) - 1

  % range of integers representable as TC numbers of length `len':
  op rangeForLength (len:PosNat) : Set Integer =
    fn i -> minForLength len <= i && i <= maxForLength len

  theorem integer_range is
    fa(x:TCNumber) toInteger x in? rangeForLength (length x)

  % construct zero TC number of given length (i.e. number of bits):
  op zero (len:PosNat) : TCNumber = repeat 0 len

  theorem zero_is_zero is
    fa(len:PosNat) zero? (zero len)

  % extend sign bit to given length (>= current length):
  op signExtend (x:TCNumber, newLen:PosNat | newLen >= length x) : TCNumber =
    extendLeft (x, sign x, newLen)

  theorem sign_extension_does_not_change_value is
    fa (x:TCNumber, newLen:PosNat)
      newLen >= length x =>
      toInteger (signExtend (x, newLen)) = toInteger x

  % sign-extend shorter TC number to length of longer TC number:
  op equiSignExtend (x:TCNumber, y:TCNumber) : TCNumber * TCNumber =
    equiExtendLeft (x, y, sign x, sign y)

  % change length of TC number by either sign-extending or discarding higher
  % bits (depending on whether new length is > or <= current length)
  op changeLength (x:TCNumber, newLen:PosNat) : TCNumber =
    if newLen > length x then signExtend(x,newLen)
    else (* newLen <= length x *) suffix (x, newLen)

  % convert integer to TC number of shortest length:
  op fromInteger (i:Integer) : TCNumber =
    minimizer (length, fn(x:TCNumber) -> toInteger x = i)

  theorem length_of_fromInteger is
    fa (i:Integer, len:PosNat) i in? rangeForLength len =>
                               length (fromInteger i) <= len

  % unary minus:
  op TCNumber.- (x:TCNumber) : TCNumber =
     % qualifier needed to avoid confusion with binary -;
     % ending "_" to avoid conflicts with user-defined qualifiers
    % first calculate exact result as TC number:
    let y = fromInteger (- (toInteger x)) in
    % then truncate to operand length:
    changeLength (y, length x)

  % addition:
  op + (x:TCNumber, y:TCNumber | x equiLong y) infixl 25 : TCNumber =
    % first calculate exact result as TC number:
    let z = fromInteger (toInteger x + toInteger y) in
    % then truncate to operand length if overflow:
    changeLength (z, length x)

  % subtraction:
  op - (x:TCNumber, y:TCNumber | x equiLong y) infixl 25 : TCNumber = x + (- y)

  % multiplication:
  op * (x:TCNumber, y:TCNumber | x equiLong y) infixl 27 : TCNumber =
    % first calculate exact result as TC number:
    let z = fromInteger (toInteger x * toInteger y) in
    % then truncate to operand length if overflow:
    changeLength (z, length x)

  % division:
  op div (x:TCNumber, y:TCNumber | x equiLong y) infixl 26 : TCNumber =
    % first calculate exact result as TC number:
    let z = fromInteger (toInteger x div toInteger y) in
    % then truncate to operand length if overflow:
    changeLength (z, length x)

  % remainder:
  op rem (x:TCNumber, y:TCNumber | x equiLong y) infixl 26 : TCNumber =
    fromInteger (toInteger x rem toInteger y)  % no overflow is possible

  theorem rem is
    fa (x:TCNumber, y:TCNumber)
      (x div y) * y + (x rem y) = x

  op < (x:TCNumber, y:TCNumber | x equiLong y) infixl 20 : Boolean =
    toInteger x < toInteger y

  op <= (x:TCNumber, y:TCNumber | x equiLong y) infixl 20 : Boolean =
    toInteger x <= toInteger y

  op > (x:TCNumber, y:TCNumber | x equiLong y) infixl 20 : Boolean =
    toInteger x > toInteger y

  op >= (x:TCNumber, y:TCNumber | x equiLong y) infixl 20 : Boolean =
    toInteger x >= toInteger y

  % TC numbers represent the same integer:
  op EQ (x:TCNumber, y:TCNumber) infixl 20 : Boolean = (toInteger x = toInteger y)

  op shiftLeft (x:TCNumber, n:Nat | n <= length x) : TCNumber =
    shiftLeft (x, 0, n)

  op shiftRightSigned (x:TCNumber, n:Nat | n <= length x) : TCNumber =
    shiftRight (x, sign x, n)

  op shiftRightUnsigned (x:TCNumber, n:Nat | n <= length x) : TCNumber =
    shiftRight (x, 0, n)

endspec
