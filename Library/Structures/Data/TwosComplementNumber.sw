(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


(* A copy of the parts of /Library/General/TwosComplementNumber needed for C
generation (in /Library/CGen/Monadic) that removes any dependencies on
/Library/General/Set, so that it is compatible with libraries in
/Library/DataStructures/ . *)

TwosComplementNumber qualifying spec
  import /Library/General/Bit % Does not use /Library/General/Set
  import ISet

  type TCNumber = List1 Bit

  op sign : TCNumber -> Bit = head
  op negative? (x:TCNumber) : Bool = (sign x = B1)


  op minForLength (len:PosNat) : Int = - (2 ** (len - 1))
  op maxForLength (len:PosNat) : Int = 2 ** (len - 1) - 1

  op rangeForLength (len:PosNat) : ISet Int =
    fn i -> minForLength len <= i && i <= maxForLength len

  op toNat (bs:List Bit) : Nat =
    case bs of
      | [] -> 0
      | B0 :: bs' -> toNat bs'
      | B1 :: bs' -> (2 ** length bs') + toNat bs'

  op toInt (x:TCNumber) : Int = if ~(negative? x) then toNat x
                                else toNat x - 2 ** (length x)

  (* Convert an integer to a twos complement number *)
  (* FIXME: remove the  definite description operator *)
  op tcNumber (i:Int, len:PosNat | i memb? rangeForLength len) : TCNumber =
    the(x:TCNumber) length x = len && toInt x = i

end-spec
