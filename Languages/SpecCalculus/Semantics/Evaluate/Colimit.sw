\subsection{Evaluation of Colimits}

\begin{spec}
SpecCalc qualifying spec {
  import Signature
  import ../../../MetaSlang/Specs/Categories/AsRecord
\end{spec}

\begin{spec}
  def SpecCalc.evaluateColimit term = {
      (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
      case value of
        | Diag dgm -> 
            let univCocone = (colimit (cod (functor (dgm)))) dgm in
            return (Spec (apex (cocone univCocone)),timeStamp,depURIs)
        | _ -> raise (TypeCheck (positionOf term, "argument of colimit is not a diagram"))
    }
}
\end{spec}
