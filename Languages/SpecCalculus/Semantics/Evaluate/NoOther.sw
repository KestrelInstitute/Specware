\subsection{Evalution of extension-specific terms in the Spec Calculus}

This is the default version, to be used in Specware itself and in any
extensions of Specware that don't use OtherTerm, OtherValue, etc.

\begin{spec}
SpecCalc qualifying spec 

  import Signature
  import UnitId/Utilities

  def SpecCalc.evaluateOther _ (* args *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Unexpected OtherTerm at " ^ (uidToString unitId) ^ "\n"))
  }

  def SpecCalc.evaluateOtherSubstitute _(* spec_tm *) _(* spec_value *) _(* morph_tm *) _(* morph_value *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherSpecMorph _(* dom *) _(* cod *) _(* rules *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherPrint _ (* value *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherGenerate _ _ (* args valueInfo *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherQualify _ _ _ (* term valueinfo qualifier *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Qualify: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherProofGen _ (* value, term, optFileName, fromObligations? *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Qualify: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.evaluateOtherProofGenLocal _ (* value, term, optFileName, fromObligations? *) pos = {
    unitId <- getCurrentUID;
    raise (TypeCheck (pos, "Qualify: Unexpected OtherTerm at " ^ (uidToString unitId)^ "\n"))
  }

  def SpecCalc.ppOtherValue _ (* value *) = ppString "<some OtherValue>"

  def SpecCalc.ppOtherTerm  _ (* term *)  = ppString "<some OtherTerm>"

endspec
\end{spec}
 
%%
%% $Id$
%%
%% $Log$
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
