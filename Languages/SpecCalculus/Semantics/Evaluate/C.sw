(**
  wrapper for calling the C generator
**)


SpecCalc qualifying spec
  import Signature  
  import ../SpecPath
  import /Languages/MetaSlang/CodeGen/C/GCfree/CG

  op evaluateCGen : ValueInfo * Option String -> Env ValueInfo

  def evaluateCGen (valueInfo as (Spec spc,_,_), optFileNm) = {
     baseUnitId <- pathToRelativeURI "/Library/Base";
     (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "base") baseUnitId;
      let _ = generateCCode (subtractSpec spc baseSpec, spc, optFileNm) in
      return valueInfo}

end-spec
