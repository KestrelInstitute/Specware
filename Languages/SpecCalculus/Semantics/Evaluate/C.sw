(**
  wrapper for calling the C generator
**)


SpecCalc qualifying spec
  import UnitId
  import /Languages/MetaSlang/CodeGen/C/GCfree/CG

  op evaluateCGen : ValueInfo * Option String -> Env ValueInfo

  def evaluateCGen (valueInfo as (Spec spc,_,_), optFileNm) = {
     baseUnitId <- pathToRelativeUID "/Library/Base";
     (Spec baseSpec,_,_) <- SpecCalc.evaluateUnitId (Internal "base") baseUnitId;
      let _ = generateCCode (subtractSpec spc baseSpec, spc, optFileNm) in
      return valueInfo}

end-spec
