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
			  ^ "Dom diagram  = \n" 
			  ^ showValue domValue 
			  ^ "\n"
			  ^ "Cod diagram  = \n" 
			  ^ showValue codValue 
			  ^ "\n"
			  ^ (toString (List.length morphRules)) 
			  ^ " diagram-morphism rules \n"))
    }
}
\end{spec}
