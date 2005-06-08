\subsection{Evalution of extension-specific terms in the Spec Calculus}

This is the default version, to be used in Specware itself and in any
extensions of Specware that don't use OtherTerm, OtherValue, etc.

\begin{spec}
SpecCalc qualifying spec 

  import Signature
  import UnitId/Utilities

  type OtherRenamingRule a = ()  
  type OtherRenamings = ()
  def  noOtherRenamings = ()

  def SpecCalc.evaluateOther _ (* args *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Unexpected OtherTerm at " ^ (uidToString unitId) ^ "\n"))
  }

  def SpecCalc.evaluateOtherSubstitute _(* spec_tm *) _(* spec_value *) _(* morph_tm *) _(* morph_value *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Substitute: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherSpecMorph _(* dom *) _(* cod *) _(* rules *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "SpecMorph: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherPrint _ (* value *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Print: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherGenerate _ _ (* args valueInfo *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Generate: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherQualify _ _ _ (* term valueinfo qualifier *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Qualify: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherProve _ (* claimName, value, valueName, proverName, assertions, possibleOptions, baseOptions, answerVariable *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Prove: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherProofGen _ (* value, term, optFileName, fromObligations? *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "ProofGen: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherProofGenLocal _ (* value, term, optFileName, fromObligations? *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "ProofGenLocal: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherObligations _ (* value *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Obligations: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.ppOtherValue _ (* value *) = ppString "<some OtherValue>"

  def SpecCalc.ppOtherTerm  _ (* term *)  = ppString "<some OtherTerm>"

endspec
\end{spec}
 
%%
%% $Id$
%%
%% $Log$
%% Revision 1.16  2005/06/07 20:18:49  mcdonald
%% move TranslateRules from SpecColimit.sw to Types.sw
%% redefine TranslateExpr via TranslateRules
%%
%% add Renaming case to SpecCalc.Term_
%% add Other case to TranslateRule_
%% add OtherTranslateRule as hook for extensions
%% add printer for Renaming case of Term_
%% add constructor for renaming case  [to be called from parser]
%%
%% add Renaming case to SpecCalc.Value
%% move TranslationMaps from Translate.sw to Value.sw
%% add other_maps field to TranslationMaps
%% add OtherTranslationMaps as hook for extensions
%% add printer for Renaming case of Value
%%
%% Revision 1.15  2005/06/07 05:36:21  mcdonald
%% revised error messages to be more informative/less misleading
%%
%% Revision 1.14  2005/04/01 21:43:23  gilham
%% Changed evaluateProve to support OtherValues in addition to Specs.
%% Fixed a problem with invalid file names for proof files.
%% Fixed some bugs in the definition of unionProofDecls
%%
%% Revision 1.13  2005/02/10 09:53:05  mcdonald
%% added hook for other obligations
%%
%% still unclear what to do for obligations of complex things
%% that contain many specs, morphisms, etc. -- hard to make it
%% a single spec
%%
%% Revision 1.12  2005/01/28 03:12:51  mcdonald
%% tweak to avoid compiler warnings
%%
%% Revision 1.11  2004/11/12 23:02:24  cyrluk
%% Added other for ProofGen.
%%
%% Revision 1.10  2004/11/12 19:04:53  becker
%% Added the signature and default implementations to
%% evaluateProofGenOther  and evaluateProofGenLocalOther
%% to dispatch the generation of proof obligations to functions
%% outside Specware.
%%
%%
%%
