\subsection{Evaluation of Colimits}

\begin{spec}

SpecCalc qualifying spec 
{
 import Signature
 import UnitId/Utilities  % for uidToString, if used...
 import SpecColimit

 def SpecCalc.evaluateColimit term = 
   {
    unitId <- getCurrentUID;
    print (";;; Elaborating diagram-colimit at " ^ (uidToString unitId) ^ "\n");
    (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo term;
    case value of
      | Diag dgm -> 
        let cod_cat = cod (functor (dgm)) in 
	% cod_cat is presumably the category of specs
	let colimit_fn = colimit cod_cat in  
	% colimit fn is presumably specColimit.
        let initial_cocone = colimit_fn dgm in
        return (Colimit initial_cocone, timeStamp, depUIDs)
      | _ -> 
	raise (TypeCheck (positionOf term, "argument of colimit is not a spec diagram"))
	 }
  }

\end{spec}
