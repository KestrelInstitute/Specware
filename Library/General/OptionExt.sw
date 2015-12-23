(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Option qualifying spec

(* This is an extension of the base library spec Option.

The following op removes the wrapping constructor Some from an optional value
(i.e. it "unwraps" the value). *)

op [a] unwrap (ox:Option a | ox ~= None) : a =
  let Some x = ox in x

(* The Option type has the structure of an exception monad, whose bind operator
is defined as follows. The use of the name "monadBind" enables the use of
Metaslang's monadic syntax. *)

op [a,b] monadBind (m:Option a, f: a -> Option b) : Option b =
  case m of
  | None -> None
  | Some x -> f x

endspec
