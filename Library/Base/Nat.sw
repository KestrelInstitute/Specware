\section{Nat}

\begin{spec}
Nat qualifying spec 
  import PrimitiveSorts
  import Integer
  import Compare
  import Boolean

  sort Nat.Nat  = {n : Integer | n >= 0}
%  op Nat.+ infixl 25 : Nat * Nat -> Nat
%  op Nat.* infixl 27 : Nat * Nat -> Nat
%  op Nat.- infixl 25 : Nat * Nat -> Integer

  op succ : Nat -> Nat
  op zero : Nat 
  op one  : Nat
  op two  : Nat

  op pred : Nat -> Integer
%  op Nat.<  infixl 20 : Nat * Nat -> Boolean
%  op Nat.<= infixl 20 : Nat * Nat -> Boolean
%  op Nat.>  infixl 20 : Nat * Nat -> Boolean
%  op Nat.>= infixl 20 : Nat * Nat -> Boolean
%  op min : Nat * Nat -> Nat
%  op max : Nat * Nat -> Nat
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

  % coercion functions.
%  op fromNat : Nat -> Nat
%  op Integer.fromNat : Nat -> Integer

%  op toNat : Integer -> Nat

  def zero = 0
  def one  = 1
  def two  = 2

  def pred n = n - 1

  def div (n,m) =
    if n < m then 0 else 1 + ((n - m) div m)

  def succ n = n + 1

  def posNat? n = n > 0

%  axiom < zero is fa(x) (~(x < 0))
%  axiom < succ is fa(x,y) (x < succ y) <=> (x < y) or (x = y)
%  axiom less or equal is fa(x,y) (x <= y)  <=>  (x < y) or (x = y)

%  def min (x,y) = if x <= y then x else y
%  def max (x,y) = if x <= y then y else x

 % def >  (x,y) = y <  x
%  def >= (x,y) = y <= x

 % def toString(n) = 
 %     if 0 <= n & n <= 9
 %     then [54+n]
 %     else (toString(n div 10)) ++ [54+(n rem 10)]

%  op compare : Nat * Nat -> Comparison
%  def compare (n,m) =
%    if n < m then Less else if n = m then Equal else Greater        

  def show n = natToString n
endspec
\end{spec}
