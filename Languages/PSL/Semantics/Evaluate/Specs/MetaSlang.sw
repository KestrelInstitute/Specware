\section{Abstraction of MetaSlang Terms}

Not clear that this is useful at this stage. Would
prefer the qualifier to be MetaSlang but this is taken.

It is expected that \Sort{Term} refines to \Sort{ATerm Position}
Similary, we expect that \Sort{Type} refines to \Sort{ASortScheme Position}

### Should we just get rid of the "At" suffix of the make functions and have four of
each: monadic / non-monadic. position / no position

Something like:

         mkNot : Term -> Term
     Env.mkNot : Term -> Env Term
     Pos.mkNot : Term -> Position -> Term
 Env.Pos.mkNot : Term -> Position -> Env Term

\begin{spec}
MS qualifying spec
  import Pretty
  import Id
  import Env

  sort Position
  sort Term
  sort Type
  sort Fun  % Don't like this one.
  sort TypeVars

  op Term.pp : Term -> Doc
  op Term.show : Term -> String

  op Type.pp : Type -> Doc
  op Type.show : Type -> String

  op mkApplyNAt : Term -> Term -> Position -> Term
  op mkTupleAt : List Term -> Position -> Term
  op mkRecordAt : List (Id * Term) -> Position -> Term

  op mkProduct : List Type -> Type
  op Env.mkProduct : List Type -> Env Type
  def Env.mkProduct types = return (mkProduct types)

  op MSPos.mkProduct : List Type -> Position -> Type
  op MSPosEnv.mkProduct : List Type -> Position -> Env Type
  def MSPosEnv.mkProduct types position = return (mkProduct types position)

  op mkBase : Id -> List Type -> Position -> Type
  op MSPos.mkBase : Id -> List Type -> Position -> Type
  op Env.mkBase : Id -> List Type -> Env Type
  op MSPosEnv.mkBase : Id -> List Type -> Position -> Env Type
  
  op mkArrowAt : Type -> Type -> Position -> Type
  op mkNotAt : Term -> Position -> Term
  op mkTrueAt : Position -> Term
  op mkFunAt : Fun -> Type -> Position -> Type
  op mkEqualsAt : Type -> Position -> Term
  op mkEqualityAt : Term -> Term -> Position -> Term
  op mkOpAt : Id -> Type -> Position -> Term
  op mkOrAt : Term -> Term -> Position -> Term
  op disjList : List Term -> Position -> Term

  op mkNat : Nat -> Term
endspec
\end{spec}
