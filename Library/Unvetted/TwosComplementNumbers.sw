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

  op sign : TCNumber -> Bit
  def sign = first

  op zero? : TCNumber -> Boolean
  def zero? x = forall? (fn b -> b = 0) x

  op nonZero? : TCNumber -> Boolean
  def nonZero? = ~~ zero?

  type NonZeroTCNumber = (TCNumber | nonZero?)

  op negative? : TCNumber -> Boolean
  def negative? x = (sign x = 1)

  op nonNegative? : TCNumber -> Boolean
  def nonNegative? = ~~ negative?

  conjecture nonNegative?_alt_def is
    fa(x:TCNumber) nonNegative? x <=> sign x = 0

  op positive? : TCNumber -> Boolean
  def positive? = nonNegative? /\ (~~ zero?)

  op nonPositive? : TCNumber -> Boolean
  def nonPositive? = ~~ positive?

  % interpretation as integer:
  op toInteger : TCNumber -> Integer
  def toInteger x = if nonNegative? x then toNat x
                    else toNat x - 2 ** (length x)

  conjecture twos_complement_of_negative is
    fa(x:TCNumber) negative? x =>  % given negative TC number
      toNat (not x) + 1 =  % two's complement operation
        - (toInteger x)  % yields absolute value of represented integer

  % minimum integer representable as TC number of length `len':
  op minForLength : PosNat -> Integer
  def minForLength len = - (2 ** (len - 1))

  % maximum integer representable as TC number of length `len':
  op maxForLength : PosNat -> Integer
  def maxForLength len = 2 ** (len - 1) - 1

  % range of integers representable as TC numbers of length `len':
  op rangeForLength : PosNat -> Set Integer
  def rangeForLength len = fn i -> minForLength len <= i && i <= maxForLength len

  conjecture integerRange is
    fa(x:TCNumber) toInteger x in? rangeForLength (length x)

  % construct zero TC number of given length (i.e. number of bits):
  op zero : PosNat -> TCNumber
  def zero len = repeat 0 len

  conjecture zeroIsZero is
    fa(len:PosNat) zero? (zero len)

  % extend sign bit to given length (>= current length):
  op signExtend :
     {(x,newLen) : TCNumber * PosNat | newLen >= length x} -> TCNumber
  def signExtend(x,newLen) = extendLeft (x, sign x, newLen)

  conjecture sign_extension_does_not_change_value is
    fa (x:TCNumber, newLen:PosNat)
      newLen >= length x =>
      toInteger (signExtend (x, newLen)) = toInteger x

  % sign-extend shorter TC number to length of longer TC number:
  op equiSignExtend : TCNumber * TCNumber -> TCNumber * TCNumber
  def equiSignExtend(x,y) =
    equiExtendLeft (x, y, sign x, sign y)

  % change length of TC number by either sign-extending or discarding higher
  % bits (depending on whether new length is > or <= current length)
  op changeLength : TCNumber * PosNat -> TCNumber
  def changeLength(x,newLen) = if newLen > length x then signExtend(x,newLen)
                               else (* newLen <= length x *) suffix (x, newLen)

  % convert integer to TC number of shortest length:
  op fromInteger : Integer -> TCNumber
  def fromInteger i = minimizer (length, fn(x:TCNumber) -> toInteger x = i)

  % unary minus:
  op TCNumber_.- : TCNumber -> TCNumber
     % qualifier needed to avoid confusion with binary -;
     % ending "_" to avoid conflicts with user-defined qualifiers
  def TCNumber_.- x =
    % first calculate exact result as TC number:
    let y = fromInteger (- (toInteger x)) in
    % then truncate to operand length:
    changeLength (y, length x)

  % addition:
  op + infixl 25 : ((TCNumber * TCNumber) | equiLong) -> TCNumber
  def + (x,y) =
    % first calculate exact result as TC number:
    let z = fromInteger (toInteger x + toInteger y) in
    % then truncate to operand length if overflow:
    changeLength (z, length x)

  % subtraction:
  op - infixl 25 : ((TCNumber * TCNumber) | equiLong) -> TCNumber
  def - (x,y) = x + (- y)

  % multiplication:
  op * infixl 27 : ((TCNumber * TCNumber) | equiLong) -> TCNumber
  def * (x,y) =
    % first calculate exact result as TC number:
    let z = fromInteger (toInteger x * toInteger y) in
    % then truncate to operand length if overflow:
    changeLength (z, length x)

  % division:
  op div infixl 26 : ((TCNumber * NonZeroTCNumber) | equiLong) -> TCNumber
  def div (x,y) =
    % first calculate exact result as TC number:
    let z = fromInteger (toInteger x div toInteger y) in
    % then truncate to operand length if overflow:
    changeLength (z, length x)

  % remainder:
  op rem infixl 26 : ((TCNumber * NonZeroTCNumber) | equiLong) -> TCNumber
  def rem (x,y) = fromInteger (toInteger x rem toInteger y)
                        % no overflow is possible

  conjecture rem is
    fa (x:TCNumber, y:TCNumber)
      (x div y) * y + (x rem y) = x

  op < infixl 20 : ((TCNumber * TCNumber) | equiLong) -> Boolean
  def < (x,y) = (toInteger x < toInteger y)

  op <= infixl 20 : ((TCNumber * TCNumber) | equiLong) -> Boolean
  def <= (x,y) = (toInteger x <= toInteger y)

  op > infixl 20 : ((TCNumber * TCNumber) | equiLong) -> Boolean
  def > (x,y) = (toInteger x > toInteger y)

  op >= infixl 20 : ((TCNumber * TCNumber) | equiLong) -> Boolean
  def >= (x,y) = (toInteger x >= toInteger y)

  % TC numbers represent the same integer:
  op EQ infixl 20 : TCNumber * TCNumber -> Boolean
  def EQ (x,y) = (toInteger x = toInteger y)

  op shiftLeft : {(x,n) : TCNumber * Nat | n <= length x} -> TCNumber
  def shiftLeft(x,n) = shiftLeft (x, 0, n)

  op shiftRightSigned : {(x,n) : TCNumber * Nat | n <= length x} -> TCNumber
  def shiftRightSigned(x,n) = shiftRight (x, sign x, n)

  op shiftRightUnsigned : {(x,n) : TCNumber * Nat | n <= length x} -> TCNumber
  def shiftRightUnsigned(x,n) = shiftRight (x, 0, n)

endspec
