\subsection{Evaluation of Colimits}

\begin{spec}
SpecCalc qualifying spec 
  import Signature

  def SpecCalc.evaluateColimit term = {
      (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
       saveSpecwareState; % HACK: communication with run_monad in /Languages/MetaSlang/Specs/Categories/Colimit.sw      
       %% This saves the global context in the global *specware-global-context*
       %% run_monad uses restoreSavedSpecwareState to restore that global state
       case value of 
	 | Diag dgm -> 
            let colimit_fn     = colimit (cod (functor (dgm))) in
            let initial_cocone = colimit_fn dgm in
	    return (Colimit initial_cocone, timeStamp, depURIs)
	 | _ -> raise (TypeCheck (positionOf term, "argument of colimit is not a diagram"))
    }
endspec
\end{spec}
