Nat qualifying spec 
  import PrimitiveSorts
  import Integer
  import Compare
  import Boolean

  sort Nat.Nat  = {n : Integer | n >= 0}

  op succ : Nat -> Nat
  op zero : Nat 
  op one  : Nat
  op two  : Nat

  op pred : Nat -> Integer
  op posNat? : Nat -> Boolean

  sort PosNat = {n : Nat | posNat? n}
  op rem infixl 26 : Nat * PosNat -> Nat
  op div infixl 26 : Nat * PosNat -> Nat

  %% toString is the same as natToString.
  %% show is the same as natToString
  %% toString and natToString to be deprecated

  op toString    : Nat -> String
  op natToString : Nat -> String
  op show        : Nat -> String
  op stringToNat : String -> Nat

  def zero = 0
  def one  = 1
  def two  = 2

  def pred n = n - 1

  def div (n,m) =
    if n < m then 0 else 1 + ((n - m) div m)

  def succ n = n + 1

  def posNat? n = n > 0

  def show n = natToString n
endspec
