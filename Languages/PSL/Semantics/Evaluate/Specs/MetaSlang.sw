\section{Abstraction of MetaSlang Terms}

Not clear that this is useful at this stage. Would
prefer the qualifier to be MetaSlang but this is taken.

It is expected that \Sort{Term} refines to \Sort{ATerm Position}
Similary, we expect that \Sort{Type} refines to \Sort{ASortScheme Position}

The name of the qualifier is unfortunate. Would prefer \Qualifier{MetaSlang}
or \Qualifier{MS} but both are taken.

\begin{spec}
MSlang qualifying spec
  import /Library/Structures/Data/Pretty
  import Id
  import Env

  sort Position.Position
  sort Term
  sort Type
  sort Fun
  sort TypeVars

  op Term.pp : Term -> Doc
  op Term.show : Term -> String

  op Type.pp : Type -> Doc
  op Type.show : Type -> String

  op noTypeVars : TypeVars

  op boolType : Position -> Type

  op mkApplyN : Term -> Term -> Position -> Term
  op mkTuple : List Term -> Position -> Term
  op mkRecord : List (Id.Id * Term) -> Position -> Term

  % op mkProduct : List Type -> Type
  % op Env.mkProduct : List Type -> Env Type
  % def Env.mkProduct types = return (mkProduct types)

  op MSPos.mkProduct : List Type -> Position -> Type
  op MSlangEnv.mkProduct : List Type -> Position -> Env Type
  def MSlangEnv.mkProduct types position = return (mkProduct types position)

  op mkBase : Id -> List Type -> Position -> Type
  op MSlangEnv.mkBase : Id -> List Type -> Position -> Env Type
  def MSlangEnv.mkBase id types position = return (mkBase id types position)

  op mkEquals : Type -> Position -> Term

  op mkEquality : Term -> Term -> Position -> Term
  op MSlangEnv.mkEquality : Term -> Term -> Position -> Env Term
  def MSlangEnv.mkEquality term1 term2 position =
    return (mkEquality term1 term2 position)

  op mkTrue : Position -> Term
  op MSPosEnv.mkTrue : Position -> Env Term
  
  op mkNot : Term -> Position -> Term
  op mkFun : Fun -> Type -> Position -> Term
  op mkOp : Id -> Type -> Position -> Term
  op mkOr : Term -> Term -> Position -> Term
  op disjList : List Term -> Position -> Term

  op mkNat : Nat -> Term

  op freshMetaTyVar : Position -> Type
endspec
\end{spec}
