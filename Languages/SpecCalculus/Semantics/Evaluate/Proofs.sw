spec

 import Signature
 import UnitId

(* op SCTermTo
      snarkLogFileName <- UIDtoSnarkLogFile unitId;
     _ <- return (ensureDirectoriesExist snarkLogFileName);
*)

 sort SCDecl = SpecCalc.Decl Position
 
 op generateProof: Spec * SCTerm * Property * Boolean * String * ProverOptions -> SCDecl
 def generateProof (spc, scTerm, prop, multipleFiles, prover_name, prover_options) =
   let assertions = All in
   let (_, propName, _, _) = prop in
   let proveTerm = Prove (propName, scTerm, prover_name, assertions, prover_options) in
   let proofName = propName ^ "_proof" in
   let ProveTerm_A: (SpecCalc.Term Position) = (proveTerm, noPos) in
   (proofName, ProveTerm_A)

 op generateProofsInSpec: Spec * SCTerm * Boolean * String * ProverOptions -> List SCDecl
 def generateProofsInSpec (spc, scTerm, multipleFiles, prover_name, prover_options) =
   let props = spc.properties in
   map (fn (prop) -> generateProof(spc, scTerm, prop, multipleFiles, prover_name, prover_options)) props

% op ppProof: SCDecl -> WadlerLindig.Pretty

% def ppProof(proof) =
%   SpecCalc.ppTerm(proof)

 op ppProofs: List SCDecl -> WadlerLindig.Pretty

 def ppProofs(proofs) =
   ppDecls(proofs)
%   ppSep ppNewline (map ppProof proofs)

 op ppProofsToFile: List SCDecl * String -> ()

 def ppProofsToFile(proofs, file) =
   let prettyProofs = ppProofs(proofs) in
   let fileContentsString = ppFormat(prettyProofs) in
   let fileContentsPretty = PrettyPrint.string(fileContentsString) in
   let fileContentsText = format(80, fileContentsPretty) in
   toFile(file, fileContentsText)
(*   IO.withOpenFileForWrite
    (file,
     fn stream ->  write(stream, fileContents))
*)

 op toProofFileEnv: Spec * SCTerm * Boolean * String -> ()

 def toProofFileEnv (spc, spcTerm, multipleFiles, file) =
   let _ = writeLine("Writing Proof file "^file) in
   let proofDecls = generateProofsInSpec(spc, spcTerm, multipleFiles, "Snark", OptionString ([string ("")])) in
   ppProofsToFile(proofDecls, file)

  op toProofFile    : Spec * SCTerm * Boolean * String -> ()

  def toProofFile (spc, spcTerm, multipleFiles, file) =  
      toProofFileEnv (spc, spcTerm, multipleFiles, file) 


  op SpecCalc.evaluateProofGen : ValueInfo * (SpecCalc.Term Position) * Option String
                                -> SpecCalc.Env ValueInfo

  %% Need to add error detection code
  def SpecCalc.evaluateProofGen (valueInfo as (Spec spc,_,_), cterm, optFileNm) =
    {%(preamble,_) <- compileImports(importedSpecsList spc.importedSpecs,[],[spc]);
     cUID <- SpecCalc.getUID(cterm);
     (proofFileName, multipleFiles) <-  UIDtoProofFile(cUID, optFileNm);
     (optBaseUnitId,baseSpec) <- getBase;
     let _ = ensureDirectoriesExist proofFileName in
     let _ = toProofFile ((subtractSpec spc baseSpec), cterm, multipleFiles, proofFileName) in
%     let _ = System.fail ("evaluateProofGen ") in
     {print("Generated Proof file.");
      return valueInfo}}

(*
  op UIDtoProofFile: UnitId * Option String -> SpecCalc.Env String
  def UIDtoProofFile ((unitId as {path,hashSuffix}), optFileNm) =
    case optFileNm
      of Some filNam -> return filNam
       | _ ->
    {prefix <- removeLastElem path;
     mainName <- lastElem path;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/proofs/" ^ mainName ^ ".sw"
     in
     {print("Proof file name " ^ filNm ^ "\n");
      return filNm}}
*)

 op UIDtoProofFile: UnitId * Option String -> SpecCalc.Env(String * Boolean)
 def UIDtoProofFile ((unitId as {path,hashSuffix}), optFileNm) = 
   case optFileNm
      of Some filNam -> return (filNam, false)
       | _ ->
	{
   (file, bool) <-
   case hashSuffix of
     | None -> UIDtoSingleProofFile(unitId)
     | Some _ -> UIDtoMultipleProofFile(unitId);
   return (file, bool)
 }

 op UIDtoSingleProofFile: UnitId -> Env (String * Boolean)
 def UIDtoSingleProofFile (unitId as {path,hashSuffix}) = {
    prefix <- (removeLastElem path);
    mainName <- lastElem path;
    let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
%        ^ "/proofs/" ^ mainName ^ ".log"
        ^  "/" ^ mainName ^ "_Proofs" ^".sw"
     in
      return (filNm, false)}

 op UIDtoMultipleProofFile: UnitId -> Env (String * Boolean)
 def UIDtoMultipleProofFile (unitId as {path,hashSuffix}) =
   let Some hashSuffix = hashSuffix in
    {prefix <- removeLastElem path;
     newSubDir <- lastElem path;
     mainName <- return hashSuffix;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
%        ^ "/proofs/" ^ newSubDir ^ "/" ^ mainName ^ ".log"
        ^ "/" ^ newSubDir ^ "_" ^ mainName ^ "_Proofs" ^ ".sw"
     in
      return (filNm, true)}


endspec
