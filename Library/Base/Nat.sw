\section{Nat}

\begin{spec}
Nat qualifying spec
  import PrimitiveSorts
  import Integer
  import Compare
  import Boolean

  sort Nat.Nat = {n : Integer | n Integer.>= 0}
  op Nat.+ infixl 25 : Nat * Nat -> Nat
  op Nat.* infixl 27 : Nat * Nat -> Nat
  op Nat.- infixl 25 : Nat * Nat -> Integer

  op succ : Nat -> Nat
  op zero : Nat 
  op one  : Nat
  op two  : Nat

  op pred : Nat -> Integer
  op Nat.<  infixl 20 : Nat * Nat -> Boolean
  op Nat.<= infixl 20 : Nat * Nat -> Boolean
  op Nat.>  infixl 20 : Nat * Nat -> Boolean
  op Nat.>= infixl 20 : Nat * Nat -> Boolean
  op min : Nat * Nat -> Nat
  op max : Nat * Nat -> Nat
  op posNat? : Nat -> Boolean

  sort PosNat = {n : Nat | posNat? n}
  op rem infixl 26 : Nat * PosNat -> Nat
  op div infixl 26 : Nat * PosNat -> Nat

  %% toString is the same as natToString.

  op toString    : Nat -> String
  op natToString : Nat -> String
  op stringToNat : String -> Nat

  def zero = 0
  def one  = 1
  def two  = 2

  def pred n = n Nat.- 1

  def div (n,m) =
    if n Nat.< m then 0 else 1 Nat.+ ((n Nat.- m) div m)

  def succ n = n Nat.+ 1

  def posNat? n = n Nat.> 0

  axiom < zero is fa(x) (~(x Nat.< 0))
  axiom < succ is fa(x,y) (x Nat.< succ y) <=> (x Nat.< y) or (x = y)
  axiom less or equal is fa(x,y) (x Nat.<= y)  <=>  (x Nat.< y) or (x = y)

  def min (x,y) = if x Nat.<= y then x else y
  def max (x,y) = if x Nat.<= y then y else x

  def Nat.>  (x,y) = y Nat.<  x
  def Nat.>= (x,y) = y Nat.<= x

 % def toString(n) = 
 %     if 0 <= n & n <= 9
 %     then [54+n]
 %     else (toString(n div 10)) ++ [54+(n rem 10)]

  op compare : Nat * Nat -> Comparison
  def compare (n,m) =
    if n Nat.< m then LESS else if n = m then EQUAL else GREATER        
end
\end{spec}
