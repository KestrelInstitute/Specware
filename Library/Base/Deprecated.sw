spec

(* This spec collects deprecated types and ops of the Specware base library. It
will be eventually eliminated. *)

import String

op Option.some : [a] a -> Option a = embed Some
op Option.none : [a]      Option a = embed None

endspec
