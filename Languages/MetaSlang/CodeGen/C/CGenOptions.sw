(**
 * options for the C generator
 *)

CG qualifying spec

  (**
   * flag for the special treatment of BitString sort and ops. If set to true
   * the sort BitString will be translated to unsigned int and the operators
   * One, Zero, leftShift, rightShift, complement, andBits, notZero, orBits, xorBits
   * are treated specially and directly translated into the corresponding C bit operation/constant
   *)

  op bitStringSpecial: Boolean
  def bitStringSpecial = true



endspec
