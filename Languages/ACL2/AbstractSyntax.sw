AbstractSyntax qualifying spec

  type SExp = 
    | Atom String
    | Cons SExp * SExp

end-spec