SpecCalc qualifying spec {
  import /Languages/MetaSlang/Specs/Categories/AsRecord
  import /Languages/MetaSlang/Specs/Printer
  import /Languages/SpecCalculus/AbstractSyntax/Printer
  import /Provers/Proof

  sort OtherValue                % Used for extensions to Specware

  sort SCTerm			 % Defined in Evaluate/Signature.sw

  sort Value =
    | Spec     Spec
    | Morph    Morphism
    | Diag     SpecDiagram       
    | Colimit  SpecInitialCocone 
    | Proof    Proof
    | InProcess			  % Used for catching circular definitions
    | UnEvaluated SCTerm	  % To allow evaluation by need of multiple terms within a file
    % | DiagMorph
    | Other    OtherValue         % Used for extensions to Specware

  op showValue : Value -> String
  def showValue value = ppFormat (ppValue value)

  op ppValue : Value -> Doc
  def ppValue value =
    case value of
      | Spec    spc           -> ppString (printSpec spc)
      | Morph   spec_morphism -> ppMorphism spec_morphism
      | Diag    spec_diagram  -> ppDiagram  spec_diagram
      | Colimit spec_colimit  -> ppColimit  spec_colimit
      | InProcess             -> ppString "InProcess"
      | Other   other_value   -> ppOtherValue other_value

  op ppOtherValue : OtherValue -> Doc % Used for extensions to Specware
}
