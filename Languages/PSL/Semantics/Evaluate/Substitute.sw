\section{Substitution (Prototype)}

Dialog about adding this feature is at end of file

\begin{spec}
SpecCalc qualifying spec {
  import Signature
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
  import Substitute/Utilities
  import ../Utilities

  def SpecCalc.evaluateSubstitute (specTerm, morphTerm) term_pos = {
    (spec_value, spec_timestamp, spec_dep_URIs) <- evaluateTermInfo specTerm;
    (  morph_value,   morph_timestamp,   morph_dep_URIs) <- evaluateTermInfo   morphTerm;
    case (coerceToSpec spec_value, morph_value) of % TODO: coerceToMorphism morph_value ??
      | (Spec spc, Morph sm) ->
           let timeStamp = max (spec_timestamp, morph_timestamp) in
           let dep_URIs  = listUnion (spec_dep_URIs, morph_dep_URIs) in {
             new_spec <- attemptSubstitution spc sm morphTerm term_pos;
             return (Spec new_spec, timeStamp, dep_URIs)
           }
      | (PSpec pSpec, Morph morph) ->
           let def appSub x y = unEnv (fn (x,y) -> applySubstitution x y morphTerm term_pos) (x,y) in
           let timeStamp = max (spec_timestamp, morph_timestamp) in
           let dep_URIs  = listUnion (spec_dep_URIs, morph_dep_URIs) in {
             dyCtxt <- dynamicSpec pSpec;
             print "\nApplying morphism to dynamic spec\n";
             newDyCtxt <- attemptSubstitution dyCtxt morph morphTerm term_pos;
             pSpec <- setDynamicSpec pSpec newDyCtxt;
             procs <- procedures pSpec;
             print "\nApplying morphism to procedures\n";
             procs <- return (mapMap (fn proc -> {
                           parameters= proc.parameters,
                           return = proc.return,
                           staticSpec = proc.staticSpec,
                           dynamicSpec = appSub morph proc.dynamicSpec,
                           code = mapBSpec proc.code (fn spc -> appSub morph spc) (fn x -> x)
                           }) procs);
             pSpec <- setProcedures pSpec procs;
             return (PSpec pSpec, timeStamp, dep_URIs)
           }
      | (_,        Morph _)  ->
           raise (TypeCheck (positionOf specTerm, "substitution attempted on a non-spec"))
      | (Spec _,   _) ->
           raise (TypeCheck (positionOf morphTerm, "substitution is not a morphism"))
      | (_,        _) ->
           raise (TypeCheck (term_pos, "substitution is not a morphism, and is attempted on a non-spec"))
    }

  op unEnv : fa (a,b) (a -> Env b) -> (a -> b)
  def unEnv f x =
    case (f x initialSpecwareState) of
      | (Ok y, newState) -> y
      | (Exception except, newState) -> fail (System.toString except)
}
\end{spec}
