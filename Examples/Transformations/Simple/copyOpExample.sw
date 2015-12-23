(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

A = spec
  import /Library/Base/Empty
  type foo
  op bar : foo -> foo
end-spec

B = transform A by {copyOp bar}
  