\section{Substitution (Prototype)}

\begin{spec}
SpecCalc qualifying spec {
  import Signature
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
\end{spec}

\begin{spec}
  def SpecCalc.evaluateSubstitute specTerm morphTerm = {
    (specValue,specTimeStamp,specDepURIs) <- evaluateTermInfo specTerm;
    (morphValue,morphTimeStamp,morphDepURIs) <- evaluateTermInfo morphTerm;
    case (specValue,morphValue) of
      | (Spec spc, Morph morph) -> {
            newSpec <- applySubstitution spc morph;
            return (Spec newSpec,max(specTimeStamp,morphTimeStamp),listUnion(specDepURIs,morphDepURIs))
          }
      | (_, Morph _) -> raise
          (TypeCheck (positionOf specTerm, "substitution not applied to a spec"))
      | (Spec _, _) -> raise
          (TypeCheck (positionOf morphTerm, "substitution is not a morphism"))
    }

  op applySubstitution : Spec -> Morphism -> Env Spec
  % def applySubstitution spc morph =
}
\end{spec}
