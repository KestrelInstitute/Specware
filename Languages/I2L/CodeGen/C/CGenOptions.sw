(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(**
 * options for the C generator
 *)

CG qualifying 
spec

  (**
   * flag for the special treatment of BitString type and ops. 
   * If set to true the type BitString will be translated to unsigned int and the operators
   * One, Zero, leftShift, rightShift, complement, andBits, notZero, orBits, xorBits
   * are treated specially and directly translated into the corresponding C bit operation/constant
   *)

  op bitStringSpecial? : Bool
  def bitStringSpecial? = true



endspec
