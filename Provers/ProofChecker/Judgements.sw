spec

  (* In LD, judgements are not syntactic entities, but just meta-statements
  that certain syntactic entities (contexts, types, etc.) belong to a certain
  relation (e.g. the binary relation (_ |- _ : TYPE) for well-formed types in
  context. Here, instead, we model judgements explicitly as syntactic
  entities. *)

  import Specs

  type Judgement =
    | wellFormedContext Context
    | wellFormedSpec    Spec
    | wellFormedType    Context * Type
    | typeEquivalence   Context * Type * Type
    | wellTypedExpr     Context * Expression * Type
    | wellTypedPatt     Context * Pattern    * Type
    | theore(*m*)       Context * Expression

endspec
