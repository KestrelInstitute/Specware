\subsection{Evaluation of Colimits}

\begin{spec}
SpecCalc qualifying spec {
  import Signature
  import URI/Utilities  % for uriToString, if used...
\end{spec}

\begin{spec}
  def SpecCalc.evaluateColimit term = {
    %% -------------------------------------------
    %% next two lines are optional:
    uri <- getCurrentURI;
    print (";;; Processing colimit at "^(uriToString uri)^"\n");
    %% -------------------------------------------
    (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
    case value of
      | Diag dgm -> 
        let initial_cocone = (colimit (cod (functor (dgm)))) dgm in
        % return (Spec (apex (cocone univCocone)),timeStamp,depURIs)
        return (Colimit initial_cocone, timeStamp, depURIs)
      | _ -> raise (TypeCheck (positionOf term, "argument of colimit is not a diagram"))
    }
}
\end{spec}
