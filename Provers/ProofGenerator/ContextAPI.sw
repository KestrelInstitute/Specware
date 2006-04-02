spec

  import ../ProofChecker/Spec

  op mkTypeSubstitution: TypeVariables * Types -> TypeSubstitution
  def mkTypeSubstitution(tvs, ts) = fromSeqs(tvs, ts)

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

  op axioM?: ContextElement -> Boolean
  def axioM?(ce) =
    case ce of
      | axioM _ -> true
      | _ -> false

  op lemma?: ContextElement -> Boolean
  def lemma?(ce) =
    case ce of
      | lemma _ -> true
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
  type AxioMContextElement = (ContextElement | axioM?)
  type LemmaContextElement = (ContextElement | lemma?)
  type TypeVarDeclarationContextElement = (ContextElement | typeVarDeclaration?)
  type VarDeclarationContextElement = (ContextElement | varDeclaration?)
  
endspec
