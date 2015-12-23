(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec
  type Nat.Nat

  def f = fn 
    | 0 -> 1
    | 1 -> 2

  % op x : Nat
  % def x = 1


  type Choose (a,b,c) =
    | A a
    | B b
    | C c

  op plus : [a] a * a -> a
  def plus(x,y) = x

  type List.List a = | Nil | Cons (a * List a)

  % op hd : [a] List a -> a
  % op tl : [a] List a -> List a

  op length : [a] List a -> Nat
  def length = fn
    | [] -> 0
    % | a::x -> plus (1, length x)
    | a::x -> plus (1, 2)

  % def length l = if l = Nil then 0 else plus (1, length (tl l))
  % def f x = if x = 0 then 1 else 2
  % axiom f is if x = 0 then true else false

   % op zero : MyNat

   % op succ : MyNat -> MyNat

   % axiom zero_not_succ is
     % ~(ex(n:Nat) zero = succ n)

   % axiom succ_injective is
     % fa (n1:Nat, n2:Nat) succ n1 = succ n2 => n1 = n2

%   axiom induction is
%     fa (p : Nat -> Bool)
%       p zero &&
%       (fa(n:Nat) p n => p (succ n)) =>
%       (fa(n:Nat) p n)
% 
%   % positive natural numbers:
% 
%   op posNat? : Nat -> Bool
%   def posNat? n = (n ~= zero)
% 
%   type PosNat = {n : Nat | posNat? n}
% 
%   % other ops:
% 
%   op one : Nat
%   def one = succ zero
% 
%   op two : Nat
%   def two = succ(succ zero)
% 
%   op plus : Nat * Nat -> Nat
%   axiom plus_def1 is
%     fa(n:Nat) plus(n,zero) = n
%   axiom plus_def2 is
%     fa(n:Nat, n0:Nat) plus(n,succ n0) = succ(plus(n,n0))
% 
%   op lte : Nat * Nat -> Bool
%   axiom lte_def1 is
%     fa(n:Nat) lte(zero,n)
%   axiom lte_def2 is
%     fa(n:Nat) ~(lte(succ n, zero))
%   axiom lte_def3 is
%     fa(n1:Nat, n2:Nat) lte(succ n1,succ n2) <=> lte(n1,n2)
% 
%   op minus : {(n1,n2) : Nat * Nat | lte(n2,n1)} -> Nat
%   axiom minus_def1 is
%     fa(n:Nat) minus(n,zero) = n
%   axiom minus_def2 is
%     fa(n1:Nat, n2:Nat) lte(n2,n1) => minus(succ n1,succ n2) = minus(n1,n2)
% 
endspec
