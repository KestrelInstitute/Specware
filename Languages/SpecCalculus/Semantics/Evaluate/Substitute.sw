\section{Substitution (Prototype)}

Dialog about adding this feature is in Substitute/Utilities

\begin{spec}
SpecCalc qualifying spec {
  import Signature
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
  import Substitute/Utilities
\end{spec}

\begin{spec}
  def SpecCalc.evaluateSubstitute (spec_tm, sm_tm) term_pos = {
    (spec_value, spec_timestamp, spec_dep_URIs) <- evaluateTermInfo spec_tm;
    (  sm_value,   sm_timestamp,   sm_dep_URIs) <- evaluateTermInfo   sm_tm;
    case (spec_value, sm_value) of
      | (Spec spc, Morph sm) ->
           let timeStamp = max (spec_timestamp, sm_timestamp) in
           let dep_URIs  = listUnion (spec_dep_URIs, sm_dep_URIs) in {
             new_spec <- attemptSubstitution spc sm term_pos;
             return (Spec new_spec, timeStamp, dep_URIs)
           }
      | (_,        Morph _)  ->
           raise (TypeCheck (positionOf spec_tm, "substitution attempted on a non-spec"))
      | (Spec _,   _) ->
           raise (TypeCheck (positionOf sm_tm, "substitution is not a morphism"))
      | (_,        _) ->
           raise (TypeCheck (term_pos, "substitution is not a morphism, and is attempted on a non-spec"))
    }
}
\end{spec}
