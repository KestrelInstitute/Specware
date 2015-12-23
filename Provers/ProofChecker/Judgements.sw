(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MetaslangProofChecker qualifying
spec

  % API public all

  import Contexts

  (* In LD, judgements are not syntactic entities, but just meta-statements
  that certain syntactic entities (contexts, types, etc.) belong to a certain
  relation (e.g. the binary relation (_ |- _ : TYPE) for well-formed types in
  context. Here, instead, we model judgements explicitly as syntactic
  entities. *)

  type Judgement =
    | wellFormedContext Context
    | wellFormedSpec    Context  % no type for specs (see spec Contexts)
    | wellFormedType    Context * Type
    | subType           Context * Type * Expression * Type
    | wellTypedExpr     Context * Expression * Type
    | theoreM           Context * Expression

endspec
