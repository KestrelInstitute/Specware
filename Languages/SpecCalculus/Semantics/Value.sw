SpecCalc qualifying spec
  import /Languages/MetaSlang/Specs/Categories/AsRecord
  import /Languages/MetaSlang/Specs/Printer
  import /Languages/SpecCalculus/AbstractSyntax/Printer
  import /Provers/Proof

  sort OtherValue                % Used for extensions to Specware

  sort SCTerm			 % Defined in ../AbstractSyntax/Types

  sort Value =
    | Spec        Spec
    | Morph       Morphism
    | Renaming    TranslationMaps
    | SpecPrism   SpecPrism       % tentative
    | SpecInterp  SpecInterp      % tentative
    | Diag        SpecDiagram       
    | Colimit     SpecInitialCocone 
    | Proof       Proof
    | InProcess			  % Used for catching circular definitions
    | UnEvaluated SCTerm	  % To allow evaluation by need of multiple terms within a file
   %| DiagMorph
    | Other       OtherValue      % Used for extensions to Specware

  type TranslationMaps = {op_id_map   : TranslationMap,
			  sort_id_map : TranslationMap,
			  other_maps  : OtherTranslationMaps}

  type TranslationMap  = AQualifierMap (QualifiedId * Aliases) 

  type OtherTranslationMaps 
  op noOtherTranslationMaps : OtherTranslationMaps % various defs in app-specific files such as NoOther.sw

  (* tentative *)
  type SpecInterp = {dom : Spec,
		     med : Spec,
		     cod : Spec,
		     d2m : Morphism,
		     c2m : Morphism}

  (* tentative *)
  type SpecPrism = {dom         : Spec,  
		    sms         : List Morphism,
		    pmode       : PrismMode,
		    tm          : SCTerm}

  type PrismMode = | Uniform      PrismSelection
                   | PerInstance  List SpecInterp

  op  showValue : Value -> String
  def showValue value = ppFormat (ppValue value)

 %op  ppValue : Value -> Doc
  def ppValue value =
    case value of
      | Spec        spc           -> ppString (printSpec spc)
      | Morph       spec_morphism -> ppMorphism   spec_morphism
      | Renaming    spec_renaming -> ppRenaming   spec_renaming
      | SpecPrism   spec_prism    -> ppPrism      spec_prism     % tentative
      | SpecInterp  spec_interp   -> ppInterp     spec_interp    % tentative
      | Diag        spec_diagram  -> ppDiagram    spec_diagram
      | Colimit     spec_colimit  -> ppColimit    spec_colimit
      | Other       other_value   -> ppOtherValue other_value
      | InProcess                 -> ppString "InProcess"
      | UnEvaluated _             -> ppString "some unevaluated term"
      | _                         -> ppString "<unrecognized value>"

  def ppRenaming translation_maps =
    ppString "<some spec renaming>"

  op ppOtherValue : OtherValue -> Doc % Used for extensions to Specware

  (* tentative *)
  def ppPrism {dom=_, sms=_, pmode=_, tm=_} =
    ppString "<some prism>"

  (* tentative *)
  def ppInterp {dom=_, med=_, cod=_, d2m=_, c2m=_} =
    ppString "<some interp>"

endspec
