(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec
  import Structs

  type Name = String

  (* Only "simple" typedefs as needed for a CFG *)

  type Typedef = {typename : Name, rhs : Type}

  type Type =
    | Typename Name
    | Option Type
    | Seq Type
    | ProperSeq Type
    | Sum Seq Summand
    | Record Seq Field

  type Summand = {cname : Name, tipo? : Option Type}

  type Field = {fname : Name, tipo : Type}

endspec
