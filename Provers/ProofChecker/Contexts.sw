spec

  % API public default

  import TypesAndExpressions

  (* Unlike LD, we do not require the type variables appearing in an op
  declaration, type definition, op definition, or axiom to be distinct. This
  requirement is captured in the inference rules for well-formed contexts,
  thus keeping the syntax simpler. *)

  type ContextElement =
    | typeDeclaration    TypeName * Nat
    | opDeclaration      Operation * TypeVariables * Type
    | typeDefinition     TypeName  * TypeVariables * Type
    | opDefinition       Operation * TypeVariables * Expression
    | axioM              AxiomName * TypeVariables * Expression
    | typeVarDeclaration TypeVariable
    | varDeclaration     Variable * Type

  type Context = FSeq ContextElement

  (* Unlike LD, we do not introduce a type for specs as contexts without
  (type) variable declarations. Rather, we incorporate the requirement into
  the inference rule used to prove that a context is a well-formed spec. The
  reason is that we avoid subtypes, as explained in README.txt. *)

  % contexts consisting of multiple type variable declarations:

  % API private
  op multiTypeVarDecls : TypeVariables -> Context
  def multiTypeVarDecls tvS = map (embed typeVarDeclaration) tvS

endspec
