(**
  wrapper for calling the C generator
**)


SpecCalc qualifying spec
  import UnitId
  % import /Languages/MetaSlang/CodeGen/C/CG

  op  evaluateCGen: ValueInfo * Option String -> SpecCalc.Env ValueInfo
  % def evaluateCGen (valueInfo as (Spec spc,_,_), optFileNm) = {
    % (optBaseUnitId,baseSpec) <- getBase;
    % return (generateCCode (baseSpec, subtractSpec spc baseSpec, spc, optFileNm));
    % return valueInfo}
endspec
