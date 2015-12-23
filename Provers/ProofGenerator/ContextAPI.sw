(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ProofGenerator qualifying
spec

  import ../ProofChecker/Spec

  op mkTypeSubstitution: TypeVariables * Types -> TypeSubstitution
  def mkTypeSubstitution(tvs, ts) = fromLists(tvs, ts)

  op typeDeclaration?: ContextElement -> Bool
  def typeDeclaration?(ce) =
    case ce of
      | typeDeclaration _ -> true
      | _ -> false

  op opDeclaration?: ContextElement -> Bool
  def opDeclaration?(ce) =
    case ce of
      | opDeclaration _ -> true
      | _ -> false

  op axioM?: ContextElement -> Bool
  def axioM?(ce) =
    case ce of
      | axioM _ -> true
      | _ -> false

  op lemma?: ContextElement -> Bool
  def lemma?(ce) =
    case ce of
      | lemma _ -> true
      | _ -> false

  op typeVarDeclaration?: ContextElement -> Bool
  def typeVarDeclaration?(ce) =
    case ce of
      | typeVarDeclaration _ -> true
      | _ -> false

  op varDeclaration?: ContextElement -> Bool
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
