(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

AbstractSyntax qualifying spec

  type SExp = 
    | Atom String
    | Cons SExp * SExp

end-spec