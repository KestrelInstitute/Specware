spec

  import ../ProofChecker/Spec

  op typeDeclaration?: ContextElement -> Boolean
  def typeDeclaration?(ce) =
    case ce of
      | typeDeclaration _ -> true
      | _ -> false

  op opDeclaration?: ContextElement -> Boolean
  def opDeclaration?(ce) =
    case ce of
      | opDeclaration _ -> true
      | _ -> false

  op typeDefinition?: ContextElement -> Boolean
  def typeDefinition?(ce) =
    case ce of
      | typeDefinition _ -> true
      | _ -> false

  op opDefinition?: ContextElement -> Boolean
  def opDefinition?(ce) =
    case ce of
      | opDefinition _ -> true
      | _ -> false

  op axioM?: ContextElement -> Boolean
  def axioM?(ce) =
    case ce of
      | axioM _ -> true
      | _ -> false

  op typeVarDeclaration?: ContextElement -> Boolean
  def typeVarDeclaration?(ce) =
    case ce of
      | typeVarDeclaration _ -> true
      | _ -> false

  op varDeclaration?: ContextElement -> Boolean
  def varDeclaration?(ce) =
    case ce of
      | varDeclaration _ -> true
      | _ -> false


  type TypeDeclarationContextElement = (ContextElement | typeDeclaration?)
  type OpDeclarationContextElement = (ContextElement | opDeclaration?)
  type TypeDefinitionContextElement = (ContextElement | typeDefinition?)
  type OpDefinitionContextElement = (ContextElement | opDefinition?)
  type AxioMContextElement = (ContextElement | axioM?)
  type TypeVarDeclarationContextElement = (ContextElement | typeVarDeclaration?)
  type VarDeclarationContextElement = (ContextElement | varDeclaration?)
  
  op typeDefinitionTypeName: TypeDefinitionContextElement -> TypeName
  def typeDefinitionTypeName(ce) =
    let typeDefinition(tn, _, _) = ce in
    tn

  op typeDefinitionTypeVariables: TypeDefinitionContextElement -> TypeVariables
  def typeDefinitionTypeVariables(ce) =
    let typeDefinition(_, tvs, _) = ce in
    tvs

  op typeDefinitionType: TypeDefinitionContextElement -> Type
  def typeDefinitionType(ce) =
    let typeDefinition(_, _, t) = ce in
    t

endspec
