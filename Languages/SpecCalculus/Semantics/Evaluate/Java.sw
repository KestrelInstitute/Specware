SpecCalc qualifying spec
  import Signature  
  import ../SpecPath
  import /Languages/MetaSlang/CodeGen/Java/ToJava
  import /Languages/Java/JavaPrint

  op SpecCalc.evaluateJavaGen : ValueInfo * (SpecCalc.Term Position) * Option String -> SpecCalc.Env ValueInfo

  %% Need to add error detection code
  def SpecCalc.evaluateJavaGen (valueInfo as (Spec spc,_,_), cterm, optFileNm) =
    {%(preamble,_) <- compileImports(importedSpecsList spc.importedSpecs,[],[spc]);
     cURI <- SpecCalc.getURI cterm;
     javaFileName <- URItoJavaFile (cURI, optFileNm);
     baseUnitId <- pathToRelativeURI "/Library/Base";
     (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "base") baseUnitId;
     let _ = ensureDirectoriesExist javaFileName in
     let _ = toJavaFile((subtractSpec spc baseSpec), javaFileName,[]) in
%     let _ = System.fail ("evaluateJavaGen ") in
     {print("Translated to Java");
      return valueInfo}}

  op URItoJavaFile: URI * Option String -> SpecCalc.Env String
  def URItoJavaFile ((uri as {path,hashSuffix}), optFileNm) =
    case optFileNm
      of Some filNam -> return filNam
       | _ ->
    {prefix <- removeLastElem path;
     mainName <- lastElem path;
     let filNm = (uriToFullPath {path=prefix,hashSuffix=None})
        ^ "/java/" ^ mainName ^ ".java"
     in
     {print("Java file name " ^ filNm ^ "\n");
      return filNm}}

  def toJavaFile (spc, file, preamble) =  
      toJavaFileEnv (spc, file, preamble) 

  def toJavaFileEnv (spc, file, preamble) =
      let _ = writeLine("Writing Java file "^file) in
      let spc = specToJava (spc) in
      ppJSpecToFile (spc, file, preamble)

  op ppJSpecToFile : CompUnit * String * Text -> ()

  def ppJSpecToFile (spc, file, preamble) =
    let p = ppCompUnit spc in
    let t = format (80, p) in
    toFile (file, t ++ preamble)

endspec
