spec {
  import Context
  import /Languages/MetaSlang/Specs/Categories/AsRecord 
  import ../AbstractSyntax/SimplePrinter

  sort Value =
    | Spec  Spec
    | Morph Morphism
    | Diag  (Diagram (Spec,Morphism))
    | PSpec (PSpec Position)
    | InProcess			  % Used for catching circular definitions
    % | DiagMorph

  op showValue : Value -> String
  def showValue value = ppFormat (ppValue value)

  op ppValue : Value -> Doc
  def ppValue value =
    case value of
      | Spec spc -> ppString (printSpec spc)
      | Morph morph -> ppMorphism morph
      | Diag dgm -> ppDiagram dgm
      | InProcess -> ppString "InProcess"
}
