(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


SpecCalc qualifying spec
  import UnitId
  import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
  import /Languages/Snark/SpecToSnark
  import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm

  %% Hopefully these will be unnecessary in the final system

  % type Env a = SpecCalc.Env a
  %type Spec = MetaSlang.Spec

  op SpecCalc.evaluateSnarkGen : ValueInfo * SCTerm * Option String -> SpecCalc.Env ValueInfo
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
    {prefix <- removeLast path;
     mainName <- last path;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/snark/" ^ mainName ^ ".lisp"
     in
     {print("Snark file name " ^ filNm ^ "\n");
      return filNm}}

endspec
