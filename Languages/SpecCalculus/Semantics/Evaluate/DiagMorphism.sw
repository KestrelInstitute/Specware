\subsection{Evalution of a diagram term in the Spec Calculus}

Synchronized with r1.3 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalDiagram.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature
\end{spec}

\begin{spec}
  def SpecCalc.evaluateDiagMorph (domTerm,codTerm,morphRules) = {
      domValue <- SpecCalc.evaluateTermInfo domTerm;
      codValue <- SpecCalc.evaluateTermInfo codTerm;
      raise (Unsupported ((positionOf domTerm),
                          "diagram morphisms not available yet\n" 
			  ^ "Dom   = " ^ showValue domValue ^"\"
			  ^ "Cod   = " ^ showValue codValue ^"\"
			  ^ toString (List.length morphRules) " rules"))
    }
}
\end{spec}
