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

  def SpecCalc.ppOtherValue _ (* value *) = ppString "<some OtherValue>"

  def SpecCalc.ppOtherTerm  _ (* term *)  = ppString "<some OtherTerm>"

endspec
\end{spec}
 
