\subsection{Evalution of a diagram term in the Spec Calculus}

Derived from r1.3 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalDiagram.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature
\end{spec}

When constructing the semantic representation of a diagram, what are
the coherence conditions that come up? Commutativity of sketches.
Lots of proof obligations. Needs thought.

\begin{spec}
  def SpecCalc.evaluateDiag elems =
    raise (Unsupported (pos0,"No diagrams right now"))

  def SpecCalc.evaluateDiagMorph (domTerm,codTerm,morphElems) = {
      domValue <- SpecCalc.evaluateTermInfo domTerm;
      codValue <- SpecCalc.evaluateTermInfo codTerm;
      raise (Unsupported ((positionOf domTerm),
                          "diagram morphisms not available yet"))
    }
}
\end{spec}
