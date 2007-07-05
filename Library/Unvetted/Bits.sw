(*
2005:03:18
AC
This spec defines bits and logical operations over them.
*)


Bit qualifying spec

  % bit = binary digit:

  type Bit = {b : Nat | b = 0 or b = 1}

  % isomorphism with booleans:

  op toBoolean : Bit -> Boolean = fn 0 -> false
                                   | 1 -> true

  op fromBoolean : Boolean -> Bit = fn false -> 0
                                     | true  -> 1

  conjecture isomorphicToBooleans is
    fromBoolean = inverse toBoolean

  % logical operations:

  op not (b:Bit) : Bit = (if b = 0 then 1 else 0)

  conjecture booleanNot is
    fa(b:Bit) toBoolean (not b) = ~ (toBoolean b)

  op and (b1:Bit, b2:Bit) infixl 25 : Bit = (if b1 = 1 && b2 = 1 then 1 else 0)

  conjecture booleanAnd is
    fa(b1:Bit,b2:Bit) toBoolean (b1 and b2) = (toBoolean b1) && (toBoolean b2)

  op ior (b1:Bit, b2:Bit) infixl 24 : Bit = (if b1 = 0 && b2 = 0 then 0 else 1)

  conjecture booleanOr is
    fa(b1:Bit,b2:Bit) toBoolean (b1 ior b2) = (toBoolean b1) || (toBoolean b2)

  op xor (b1:Bit, b2:Bit) infixl 24 : Bit = (if b1 = b2 then 0 else 1)

  conjecture booleanXor is
    fa(b1:Bit,b2:Bit) toBoolean (b1 xor b2) = ((toBoolean b1) ~= (toBoolean b2))

  op nand (b1:Bit, b2:Bit) infixl 25 : Bit = not (b1 and b2)

  conjecture booleanNand is
    fa(b1:Bit,b2:Bit) toBoolean (b1 nand b2) = ~((toBoolean b1) && (toBoolean b2))

  op nor (b1:Bit, b2:Bit) infixl 24 : Bit = not (b1 ior b2)

  conjecture booleanNor is
    fa(b1:Bit,b2:Bit) toBoolean (b1 nor b2) = ~((toBoolean b1) || (toBoolean b2))

endspec
