\section{Abstraction of MetaSlang Properties}

Right now when one omits the type vars, the list is assumed empty. It
would be better to accumulate them.

\begin{spec}
Property qualifying spec
  import Op

  sort Property
  sort PropertyType

  op idOf : Property -> IdSet.Set
  op ids : Property -> IdSet.Set
  op propType : Property -> PropertyType
  op typeVars : Property -> TypeVars
  op term : Property -> MSlang.Term

  op withId infixl 18 : Property * Id -> Property
  op withIds infixl 18 : Property * IdSet.Set -> Property
  op withPropType infixl 18 : Property * PropertyType -> Property
  op withTypeVars infixl 18 : Property * TypeVars -> Property
  op withTerm infixl 18 : Property * MSlang.Term -> Property

  % op make : Id -> PropertyType -> TypeVars -> MSlang.Term -> Property
  % op PropNoTypeVars.make : Id -> PropertyType -> MSlang.Term -> Property

  op makeAxiom : Id -> TypeVars -> MSlang.Term -> Property

  op PropertyEnv.makeAxiom : Id -> TypeVars -> MSlang.Term -> Env Property
  def PropertyEnv.makeAxiom id tyVars term = return (makeAxiom id tyVars term)

  op PropertyNoTypeVarsEnv.makeAxiom : Id -> MSlang.Term -> Env Property
  def PropertyNoTypeVarsEnv.makeAxiom id term = return (makeAxiom id noTypeVars term)

  op makeTheorem : Id -> TypeVars -> MSlang.Term -> Property

  op PropertyEnv.makeTheorem : Id -> TypeVars -> MSlang.Term -> Env Property
  def PropertyEnv.makeTheorem id tyVars term = return (makeTheorem id tyVars term)

  op PropertyNoTypeVarsEnv.makeTheorem : Id -> MSlang.Term -> Env Property
  def PropertyNoTypeVarsEnv.makeTheorem id term = return (makeTheorem id noTypeVars term)

  op makeConjecture : Id -> TypeVars -> MSlang.Term -> Property

  op PropertyEnv.makeConjecture : Id -> TypeVars -> MSlang.Term -> Env Property
  def PropertyEnv.makeConjecture id tyVars term = return (makeConjecture id tyVars term)

  op PropertyNoTypeVarsEnv.makeConjecture : Id -> MSlang.Term -> Env Property
  def PropertyNoTypeVarsEnv.makeConjecture id term = return (makeConjecture id noTypeVars term)

  op pp : Property -> Doc
  op show : Property -> String
endspec
\end{spec}

Why do we need the type variables here? 
