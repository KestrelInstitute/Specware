\subsection{Evalution of a diagram term in the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import Signature
\end{spec}

\begin{spec}
  def SpecCalc.evaluateDiagMorph (domTerm,codTerm,morphRules) = {
      domValueInfo <- SpecCalc.evaluateTermInfo domTerm;
      codValueInfo <- SpecCalc.evaluateTermInfo codTerm;
      let (domValue,_,_) = domValueInfo in
      let (codValue,_,_) = codValueInfo in
      raise (Unsupported ((positionOf domTerm),
                          "diagram morphisms not available yet\n" 
			  ^ "Dom diagram  = \n" 
			  ^ showValue domValue 
			  ^ "\n"
			  ^ "Cod diagram  = \n" 
			  ^ showValue codValue 
			  ^ "\n"
			  ^ (Nat.toString (List.length morphRules)) 
			  ^ " diagram-morphism rules \n"))
    }
}
\end{spec}
