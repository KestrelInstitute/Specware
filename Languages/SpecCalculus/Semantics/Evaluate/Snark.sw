
SpecCalc qualifying spec
  import UnitId
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
  import /Languages/Snark/SpecToSnark

  %% Hopefully these will be unnecessary in the final system

  % sort Env a = SpecCalc.Env a
  %sort Spec = MetaSlang.Spec

  op SpecCalc.evaluateSnarkGen : ValueInfo * (SpecCalc.Term Position) * Option String
                                -> SpecCalc.Env ValueInfo

  %% Need to add error detection code
  def SpecCalc.evaluateSnarkGen (valueInfo as (Spec spc,_,_), cterm, optFileNm) =
    {%(preamble,_) <- compileImports(importedSpecsList spc.importedSpecs,[],[spc]);
     cUID <- SpecCalc.getUID(cterm);
     snarkFileName <- UIDtoSnarkFile (cUID, optFileNm);
     (optBaseUnitId,baseSpec) <- getBase;
     let _ = ensureDirectoriesExist snarkFileName in
     let _ = toSnarkFile (subtractSpec spc baseSpec, snarkFileName,[]) in
%     let _ = System.fail ("evaluateSnarkGen ") in
     {print("Translated to Snark");
      return valueInfo}}

  op UIDtoSnarkFile: UnitId * Option String -> SpecCalc.Env String
  def UIDtoSnarkFile ((unitId as {path,hashSuffix}), optFileNm) =
    case optFileNm
      of Some filNam -> return filNam
       | _ ->
    {prefix <- removeLastElem path;
     mainName <- lastElem path;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/snark/" ^ mainName ^ ".lisp"
     in
     {print("Snark file name " ^ filNm ^ "\n");
      return filNm}}

endspec
