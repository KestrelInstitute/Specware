SpecCalc qualifying spec {
  import /Languages/MetaSlang/Specs/Categories/AsRecord
  import /Languages/MetaSlang/Specs/Printer
  import /Languages/SpecCalculus/AbstractSyntax/Printer
  import /Provers/Proof

  sort OtherValue                % Used for extensions to Specware

  sort SCTerm			 % Defined in Evaluate/Signature.sw

  sort Value =
    | Spec        Spec
    | Morph       Morphism
    | SpecPrism   SpecPrism       % tentative
    | SpecInterp  SpecInterp      % tentative
    | Diag        SpecDiagram       
    | Colimit     SpecInitialCocone 
    | Proof       Proof
    | InProcess			  % Used for catching circular definitions
    | UnEvaluated SCTerm	  % To allow evaluation by need of multiple terms within a file
   %| DiagMorph
    | Other       OtherValue      % Used for extensions to Specware

  (* tentative *)
  type SpecInterp = {dom : Spec,
		     med : Spec,
		     cod : Spec,
		     d2m : Morphism,
		     c2m : Morphism}

  (* tentative *)
  type SpecPrism = {dom         : Spec,  
		    sms         : List Morphism,
		    conversions : List SpecInterp,
		    tm          : SCTerm}

  op  showValue : Value -> String
  def showValue value = ppFormat (ppValue value)

 %op  ppValue : Value -> Doc
  def ppValue value =
    case value of
      | Spec       spc           -> ppString (printSpec spc)
      | Morph      spec_morphism -> ppMorphism   spec_morphism
      | SpecPrism  spec_prism    -> ppPrism      spec_prism     % tentative
      | SpecInterp spec_interp   -> ppInterp     spec_interp    % tentative
      | Diag       spec_diagram  -> ppDiagram    spec_diagram
      | Colimit    spec_colimit  -> ppColimit    spec_colimit
      | Other      other_value   -> ppOtherValue other_value
      | InProcess                -> ppString "InProcess"

  op ppOtherValue : OtherValue -> Doc % Used for extensions to Specware

  (* tentative *)
  def ppPrism {dom, sms, conversions, tm} =
    ppString "<some prism>"

  (* tentative *)
  def ppInterp {dom, med, cod, d2m, c2m} =
    ppString "<some interp>"
}
