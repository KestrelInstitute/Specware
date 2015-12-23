(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
     Spec for 3-valued Propositional Logic

 The Kleene partial order (cf. Marek05) 

    False    True
       \     /
       Unknown 

Note that since this is not a lattice, And3 and Or3 are not monotone
as they are in Bool.

*)

spec
  type Logic3 = |Unknown |False |True 

  def KleeneLe (p1:Logic3, p2:Logic3): Bool =
    case p1 of
      | Unknown -> true
      | False -> (case p2 of
                    | False -> true
                    | _     -> false)
      | True -> (case p2 of
                    | True -> true
                    | _     -> false)

  def Not3(p:Logic3):Logic3 = 
    case p of
      | False -> True
      | True -> False
      | Unknown -> Unknown

  def Or3(p:Logic3, q:Logic3):Logic3 = 
    case p of
      | True -> True
      | False -> q
      | Unknown -> (if q=True then True else Unknown)

  def And3(p:Logic3, q:Logic3):Logic3 = 
    case p of
      | False -> False
      | True -> q
      | Unknown -> (if q=False then False else Unknown)

  def logic3toBoolean(l3v: Logic3): Bool =
    case l3v of
      | True -> true
      | False -> false
      | Unknown -> false  % could make this polarity-sensitive

  def BooleantoLogic3(b: Bool): Logic3 =
    case b of
      | true -> True
      | false -> False

end-spec
