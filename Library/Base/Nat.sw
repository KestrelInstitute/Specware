Nat qualifying spec

  % refinement of base spec Nat

  import Integer

  % sorts:

 %sort Nat = {n : Integer | n >= 0}
  sort PosNat = {n : Nat | posNat? n}

  % ops whose Lisp code is generated:

  op succ    : Nat -> Nat
  op pred    : Nat -> Integer
  op zero    : Nat 
  op one     : Nat
  op two     : Nat
  op posNat? : Nat -> Boolean

  def zero = 0

  def one  = 1

  def two  = 2

  def pred x = x-1

  def succ x = x+1

  def posNat? x = x > 0

  % ops conceptually belonging to this spec but introduced elsewhere:

  % op toString    : Nat -> String  % deprecated
  % op show        : Nat -> String
  % op natToString : Nat -> String
  % op stringToNat : (String | ...) -> Nat

endspec
