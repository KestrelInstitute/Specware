\subsection{Evaluation of Colimits}

\begin{spec}
SpecCalc qualifying spec {
  import Signature
  import UnitId/Utilities  % for uidToString, if used...
  import Colimit/Utilities
\end{spec}

\begin{spec}
  def SpecCalc.evaluateColimit term = {
    unitId <- getCurrentUID;
    print (";;; Elaborating diagram-colimit at " ^ (uidToString unitId) ^ "\n");
    (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo term;
    case value of
      | Diag dgm -> 
        let initial_cocone = (colimit (cod (functor (dgm)))) dgm in
        % return (Spec (apex (cocone univCocone)),timeStamp,depUIDs)
        return (Colimit initial_cocone, timeStamp, depUIDs)
      | _ -> raise (TypeCheck (positionOf term, "argument of colimit is not a diagram"))
    }
}
\end{spec}
