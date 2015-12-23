(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MetaslangProofChecker qualifying
spec

  % API public default

  import TypesAndExpressions

  (* Unlike LD, we do not require the type variables appearing in an op
  declaration axiom, or lemma to be distinct. This requirement is captured in
  the inference rules for well-formed contexts, thus keeping the syntax
  simpler and avoiding subtypes (as explained in README.txt). *)

  type ContextElement =
    | typeDeclaration    TypeName * Int
    | opDeclaration      Operation * TypeVariables * Type
    | axioM              AxiomName * TypeVariables * Expression
    | lemma              LemmaName * TypeVariables * Expression
    | typeVarDeclaration TypeVariable
    | varDeclaration     Variable * Type

  type Context = List ContextElement

  % API private
  type Contexts = List Context

  (* Unlike LD, we do not introduce a type for specs as contexts without
  (type) variable declarations. Rather, we incorporate the requirement into
  the inference rule used to prove that a context is a well-formed spec. The
  reason is that we avoid subtypes, as explained in README.txt. *)

  % contexts consisting of multiple type variable declarations:

  % API private
  op multiTypeVarDecls : TypeVariables -> Context
  def multiTypeVarDecls tvS = map typeVarDeclaration tvS

endspec
