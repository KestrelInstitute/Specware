\section{Abstraction of MetaSlang Properties}

\begin{spec}
Property qualifying spec {
  import Op

  sort Property
  sort PropertyType

  op name : Property -> Id.Set
  op names : Property -> Id.Set
  op propType : Property -> PropertyType
  op typeVars : Property -> TypeVars
  op term : Property -> AbstTerm

  op withName infixl 18 : Property * QualifiedId -> Property
  op withNames infixl 18 : Property * Id.Set -> Property
  op withPropType infixl 18 : Property * PropertyType -> Property
  op withTypeVars infixl 18 : Property * TypeVars -> Property
  op withTerm infixl 18 : Property * AbstTerm -> Property

  op make : QualifiedId -> PropertyType -> TypeVars -> AbstTerm -> Property
  op PropNoTypeVars.make : QualifiedId -> PropertyType -> AbstTerm -> Property
  op pp : Property -> Doc
}
\end{spec}

Why do we need the type variables here? 
