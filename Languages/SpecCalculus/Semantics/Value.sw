spec {
  import /Languages/MetaSlang/Specs/Categories/AsRecord
  import ../AbstractSyntax/Printer

  sort Value =
    | Spec     Spec
    | Morph    Morphism
    | Diag     SpecDiagram       
    | Colimit  SpecInitialCocone 
    | InProcess			  % Used for catching circular definitions
    % | DiagMorph

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
}
