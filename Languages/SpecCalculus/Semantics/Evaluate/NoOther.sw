\subsection{Evalution of extension-specific terms in the Spec Calculus}

This is the default version, to be used in Specware itself and in any
extensions of Specware that don't use OtherTerm, OtherValue, etc.

\begin{spec}
SpecCalc qualifying spec 

  import Signature
  import URI/Utilities

  def SpecCalc.evaluateOther args pos = {
    uri <- getCurrentURI;
    raise (TypeCheck (pos, "Unexpected OtherTerm at " ^ (uriToString uri) ^ "\n"))
  }

  def SpecCalc.evaluateOtherSubstitute morph other morphTerm pos = {
    uri <- getCurrentURI;
    raise (TypeCheck (pos, "Unexpected OtherTerm at " ^ (uriToString uri)^ "\n"))
  }

  def SpecCalc.evaluateOtherSpecMorph spc morph rules pos = {
    uri <- getCurrentURI;
    raise (TypeCheck (pos, "Unexpected OtherTerm at " ^ (uriToString uri)^ "\n"))
  }

  def SpecCalc.ppOtherValue value = ppString "<some OtherValue>"

  def SpecCalc.ppOtherTerm  term  = ppString "<some OtherTerm>"

endspec
\end{spec}
 
