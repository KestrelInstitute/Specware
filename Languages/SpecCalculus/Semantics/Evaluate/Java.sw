(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying spec
  import UnitId
  import /Languages/MetaSlang/CodeGen/Java/ToJava
  import /Languages/Java/JavaPrint
  import /Languages/MetaSlang/Specs/SubtractSpec

  %% Need to add error detection code
  def SpecCalc.evaluateJavaGen (valueInfo as (Spec spc,_,_), cterm, optpath) =
    let optFileNm = None in
    {%(preamble,_) <- compileImports(importedSpecsList spc.importedSpecs,[],[spc]);
     optspec <- return(getOptSpec optpath);
     cUID <- SpecCalc.getUID cterm;
     javaFileName <- UIDtoJavaFile (cUID, optFileNm);
     (optBaseUnitId,baseSpec) <- getBase;
     %let _ = ensureDirectoriesExist javaFileName in
     %let spc0 = subtractSpec spc baseSpec in
     %let _ = specToJava(spc,javaFileName) in
     let _ = specToJava(baseSpec,spc,optspec,javaFileName) in
     %let _ = toJavaFile (subtractSpec spc baseSpec, javaFileName,[]) in
%     let _ = System.fail ("evaluateJavaGen ") in
     %{
     % print("Translated to Java");
      return valueInfo
     %}
    }

  op UIDtoJavaFile: UnitId * Option String -> SpecCalc.Env String
  def UIDtoJavaFile ((unitId as {path,hashSuffix}), optFileNm) =
    case optFileNm
      of Some filNam -> return filNam
       | _ ->
    {prefix <- removeLast path;
     mainName <- last path;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/java/" ^ mainName ^ ".java"
     in
     %{(*print("Java file name " ^ filNm ^ "\n");*)
      return filNm
      %}
      }
(*
  def toJavaFile (spc, file, preamble) =  
      toJavaFileEnv (spc, file, preamble) 

  def toJavaFileEnv (spc, file, preamble) =
      %let _ = writeLine("Writing Java file "^file) in
      let spc = specToJava (spc,file) in
      ppJSpecToFile (spc, file, preamble)

  op ppJSpecToFile : CompUnit * String * Text -> ()

  def ppJSpecToFile (spc, file, preamble) =
    let p = ppCompUnit spc in
    let t = format (80, p) in
    toFile (file, t ++ preamble)
*)

endspec
