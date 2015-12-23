(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Compare qualifying spec

  import ../Base/Compare
(*
  type Comparison =
    | Less
    | Equal
    | Greater

  op compare : Comparison * Comparison -> Comparison

  def compare(cmp1,cmp2) = if  cmp1 = cmp2     then Equal
                      else if (cmp1 = Less ||
                               cmp2 = Greater) then Less
                      else (*  cmp1 = Greater ||
                               cmp2 = Less *)       Greater

  op Bool.compare : Bool * Bool -> Compare.Comparison

  def Bool.compare(x,y) = if (x = y)    then Equal
                     else if (x = true) then Greater
                     else  (* x = false *)   Less
*)

endspec
