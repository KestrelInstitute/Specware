\section{Abstraction of MetaSlang Properties}

\begin{spec}
Property qualifying spec {
  import Op

  sort Property
  sort PropertyType

  op name : Property -> IdSet.Set
  op names : Property -> IdSet.Set
  op propType : Property -> PropertyType
  op typeVars : Property -> TypeVars
  op term : Property -> MS.Term

  op withName infixl 18 : Property * Id -> Property
  op withNames infixl 18 : Property * IdSet.Set -> Property
  op withPropType infixl 18 : Property * PropertyType -> Property
  op withTypeVars infixl 18 : Property * TypeVars -> Property
  op withTerm infixl 18 : Property * MS.Term -> Property

  op make : Id -> PropertyType -> TypeVars -> MS.Term -> Property
  op PropNoTypeVars.make : Id -> PropertyType -> MS.Term -> Property

  op pp : Property -> Doc
  op show : Property -> String
}
\end{spec}

Why do we need the type variables here? 
