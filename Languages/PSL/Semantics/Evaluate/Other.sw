\section{PSL Extension of the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import ../../AbstractSyntax/Types
  import PSpec
  import /Languages/SpecCalculus/Semantics/Evaluate/SpecMorphism
  import /Languages/SpecCalculus/Semantics/Evaluate/Substitute

  sort SpecCalc.OtherTerm a = List (PSpecElem a)
  % sort SpecCalc.OtherValue = SpecCalc.PSpec

  def SpecCalc.evaluateOther pSpec pos = evaluatePSpec pSpec

  op SpecCalc.formatPSpec : PSpec -> SpecCalc.Env Doc
  def SpecCalc.formatPSpec pSpec = {
      pslBaseURI <- pathToRelativeURI "/Library/PSL/Base";
      (Spec pslBase,_,_) <- SpecCalc.evaluateURI (Internal "PSpec base") pslBaseURI;
      fixPSpec <- return {
           staticSpec = convertPosSpecToSpec pSpec.staticSpec,
           dynamicSpec = convertPosSpecToSpec pSpec.dynamicSpec,
           procedures = pSpec.procedures
         };
      return (ppPSpecLess fixPSpec pslBase)
    }

  def SpecCalc.evaluateOtherSpecMorph
         (domValue,domTimeStamp,domDepUnitIds)
         (codValue,codTimeStamp,codDepUnitIds)
         morphRules pos =
    case (domValue,codValue) of
      | (Other pSpec, Spec spc) -> {
            morph <- makeSpecMorphism pSpec.dynamicSpec spc morphRules pos;
            return (Morph morph,max (domTimeStamp,codTimeStamp),
              listUnion (domDepUnitIds,codDepUnitIds))
          }
      | (Other pSpec1, Other pSpec2) -> {
            morph <- makeSpecMorphism pSpec1.dynamicSpec pSpec2.dynamicSpec morphRules pos;
            return (Morph morph,max (domTimeStamp,codTimeStamp),
              listUnion (domDepUnitIds,codDepUnitIds))
          }
      | (_,_) -> raise
          (TypeCheck (pos,
                      "(Other) domain and codomain of spec morphism are not specs"))

  def SpecCalc.evaluateOtherSubstitute (domValue,domTimeStamp,domDepUnitIds)
            (morphValue,morphTimeStamp,morphDepUnitIds) morphTerm pos =
    case (domValue,morphValue) of
      | (Other pSpec, Morph morph) ->
           let def appSub x = unEnv (fn x -> applySubstitution morph x morphTerm pos) x in
           let timeStamp = max (domTimeStamp, morphTimeStamp) in
           let dep_URIs  = listUnion (domDepUnitIds, morphDepUnitIds) in {
             dyCtxt <- dynamicSpec pSpec;
             print "\nApplying morphism to dynamic spec\n";
             newDyCtxt <- attemptSubstitution dyCtxt morph morphTerm pos;
             pSpec <- setDynamicSpec pSpec newDyCtxt;
             procs <- procedures pSpec;
             print "\nApplying morphism to procedures\n";
             procs <- return (mapMap (fn proc -> {
                           parameters= proc.parameters,
                           return = proc.return,
                           staticSpec = proc.staticSpec,
                           dynamicSpec = appSub proc.dynamicSpec,
                           code = mapBSpec proc.code (fn spc -> appSub spc) (fn x -> x)
                           }) procs);
             pSpec <- setProcedures pSpec procs;
             return (Other pSpec, timeStamp, dep_URIs)
           }
      | (_,        _) ->
           raise (TypeCheck (pos, "(Other) substitution is not a morphism, and is attempted on a non-spec"))

  op unEnv : fa (a,b) (a -> SpecCalc.Env b) -> (a -> b)
  def unEnv f x =
    case (f x initialSpecwareState) of
      | (Ok y, newState) -> y
      | (Exception except, newState) -> fail (System.toString except)

}
\end{spec}
