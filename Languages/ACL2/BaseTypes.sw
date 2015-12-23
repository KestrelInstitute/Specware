(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec
  import /Library/Base/Empty

  type Int
  type Bool = Boolean

  % primitives
  op <  infixl 20 : Int * Int -> Bool
  op zero : Int
  op one : Int
  
  % 
  op >= (x:Int,y:Int) infixl 20 : Bool = ~(x < y)
  op > (x:Int, y:Int) infixl 20 : Bool = y < x

  type Nat = {x : Int | x >= zero}

  op int_+ infixl 20 : Int * Int -> Int
  op nat_+ infixl 20 : Nat * Nat -> Nat

%  type Positive = {x : Int | x > zero}

(*
(defsubtype positivep integerp (> x 0))

(defun-typed (booleanp Positivep) (x)
  (and (integerp x) (> x 0)))
*)

end-spec