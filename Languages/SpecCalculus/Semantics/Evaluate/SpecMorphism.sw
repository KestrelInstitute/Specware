\subsection{Evalution of Spec Morphisms}

Synchronized with r1.4 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalSpecMorphism.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
\end{spec}

For morphisms, evaluate the domain and codomain terms, and check
coherence conditions of the morphism elements. 

\begin{spec}
  def SpecCalc.evaluateSpecMorph (domTerm,codTerm,morphElems) = {
    (domValue,domTimeStamp,domDepURIs) <- evaluateTermInfo domTerm;
    (codValue,codTimeStamp,codDepURIs) <- evaluateTermInfo codTerm;
    case (domValue,codValue) of
      | (Spec spc1, Spec spc2) ->
          raise (Unsupported (positionOf domTerm,
                              "spec morphisms not available yet"))
      | (Spec _, _) -> raise
          (TypeCheck (positionOf domTerm,
                      "domain of spec morphism is not a spec"))
      | (_, Spec _) -> raise
          (TypeCheck (positionOf codTerm,
                      "codomain of spec morphism is not a spec"))
      | (_,_) -> raise
          (TypeCheck (positionOf domTerm,
                      "domain and codomain of spec morphism are not specs"))
    }
}
\end{spec}
