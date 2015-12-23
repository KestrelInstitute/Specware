(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\subsection{Evaluation of Colimits}

\begin{spec}

SpecCalc qualifying spec 
{
 import Signature
 import UnitId/Utilities  % for uidToString, if used...
 import SpecColimit

 def SpecCalc.evaluateColimit term pos = 
   {
    unitId <- getCurrentUID;
    print (";;; Elaborating diagram-colimit at " ^ (uidToString unitId) ^ "\n");
    (value, ts, uids) <- SpecCalc.evaluateTermInfo term;
    case value of
      | Diag dgm -> 
        (let cod_cat    = cod (functor (dgm)) in  % cod_cat is presumably the category of specs
	 let colimit_fn = colimit cod_cat     in  % colimit fn is presumably specColimit. 
	 case colimit_fn dgm of
	   | (Some initial_cocone, _) ->
	     {
	      raise_any_pending_exceptions;       % e.g. if two defs are given to same op
	      return (Colimit initial_cocone, ts, uids)
	     }
	   | (_, Some error_msg) ->
	     raise (ColimitError (positionOf term, error_msg)))
      | _ -> 
	raise (ColimitError (positionOf term, "argument of colimit is not a spec diagram"))
    }
  }

\end{spec}
