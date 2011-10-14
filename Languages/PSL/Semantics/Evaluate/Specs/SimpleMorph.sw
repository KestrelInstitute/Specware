\section{Simple Mode Spec morphisms}
This needs to be factored into abstract spec and concrete refinement. Perhaps
also reconciled with the other definition in \UnitId{Morphism}.

\begin{spec}
SpecMorph qualifying spec 
  import ModeSpec

  type Morphism
  op changedOps : Morphism -> OpRefSet.Set

  type Morphism = {
    changedVars : OpRefSet.Set
  }

  def changedVars morph = morph.changedVars

  op makeMorphism : ModeSpec -> ModeSpec -> OpRefSet.Set -> Morphism
  def makeMorphism _ _ (* dom cod *) changedVars = {
      changedVars = changedVars
    }

  op pp : Morphism -> Doc
  def pp morph = pp (changedVars morph)
endspec
\end{spec}
