spec

 import Signature
 import UnitId
 import Obligations

(* op SCTermTo
      snarkLogFileName <- UIDtoSnarkLogFile unitId;
     _ <- return (ensureDirectoriesExist snarkLogFileName);
*)

 sort SCDecl = SpecCalc.Decl Position
 
 op generateProof: Spec * SCTerm * Property * Boolean * Boolean * String * ProverOptions * GlobalContext * List UnitId * Option UnitId -> SCDecl
 def generateProof (spc, _(*scTerm*), prop, _(*multipleFiles*), fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID) =
   let def printProofName(qid as Qualified (qual, id)) =
        if qual = UnQualified then
	  id^"_proof"
	else qual^"_"^id^"_proof" in
   let assertions = All in
   let (_, propName, _, _) = prop in
   let specFullUId = case findUnitIdforUnit(Spec spc, globalContext) of
                   | Some uid -> uid
                   | _ -> fail("can't find uid") in
   let specUId = relativeUidToUidAndSWPATH(specFullUId, fileUID, swpath) in
   let scTerm = if fromObligations?
                  then (Obligations (UnitId (UnitId_Relative specUId), noPos), noPos)
		else(UnitId (SpecPath_Relative specUId), noPos) in
   let proveTerm = Prove (propName, scTerm, prover_name, assertions, prover_options, None) in
   let proofName = printProofName(propName) in
   let ProveTerm_A: (SpecCalc.Term Position) = (proveTerm, noPos) in
   (proofName, ProveTerm_A)

 op generateProofMorphism: Morphism * SCTerm * Property * Boolean * Boolean * String * ProverOptions * GlobalContext * List UnitId * Option UnitId -> SCDecl
 def generateProofMorphism (morph, _(*scTerm*), prop, _(*multipleFiles*), fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID) =
   let def printProofName(qid as Qualified (qual, id)) =
        if qual = UnQualified then
	  id^"_proof"
	else qual^"_"^id^"_proof" in
   let assertions = All in
   let (_, propName, _, _) = prop in
   let specFullUId = case findUnitIdforUnit(Morph morph, globalContext) of
                   | Some uid -> uid
                   | _ -> fail("can't find uid") in
   let specUId = relativeUidToUidAndSWPATH(specFullUId, fileUID, swpath) in
   let scTerm = if fromObligations?
                  then (Obligations (UnitId (UnitId_Relative specUId), noPos), noPos)
		else(UnitId (SpecPath_Relative specUId), noPos) in
   let proveTerm = Prove (propName, scTerm, prover_name, assertions, prover_options, None) in
   let proofName = printProofName(propName) in
   let ProveTerm_A: (SpecCalc.Term Position) = (proveTerm, noPos) in
   (proofName, ProveTerm_A)

 op relativeUidToUidAndSWPATH: UnitId * Option UnitId * List UnitId -> UnitId
 def relativeUidToUidAndSWPATH(uid as {path,hashSuffix}, baseUid, swpath) =
   case baseUid of
     | None -> relativeUidToSWPATH(uid, swpath)
     | Some baseUid ->
     let uIdRelativeToBase = relativeUidToUid(uid, baseUid) in
     case uIdRelativeToBase of
       | Some newUid -> newUid
       | _ -> relativeUidToSWPATH(uid, swpath)

 op relativeUidToUid: UnitId * UnitId -> Option UnitId
 def relativeUidToUid(uid, baseUid) =
   let tailUidPath = tailListList(uid.path, baseUid.path) in
   case tailUidPath of
     | Some tailPath -> Some ({path = tailPath, hashSuffix = uid.hashSuffix})
     | _ -> None
 
 op relativeUidToSWPATH: UnitId * List UnitId -> UnitId
 def relativeUidToSWPATH(uid, swpath) =
   let def goodUid(swUid) =
         let uIdRelativeToSwUid = relativeUidToUid(uid, swUid) in
	 case uIdRelativeToSwUid of
	   | Some foundUid -> true
	   | _ -> false in
   let foundSwUid = find goodUid swpath in
   case foundSwUid of
     | Some res -> res
     | _ -> fail("can't happen")

 op tailListList: fa (a) List a * List a -> Option (List a)
 def tailListList(l1, l2) =
   let l1Head = sublist(l1, 0, length(l2)) in
   if l1Head = l2 
     then Some (nthTail(l1, length(l2)-1))
   else None


 op baseUnitIdSCTerm?: SCTerm -> Boolean
 def baseUnitIdSCTerm?(scTerm) =
   case scTerm of
     | (UnitId ( UnitId_Relative (uid)), _) -> let path = uid.path in hd(path) = "Base"
     | _ -> false

 op unionProofDecls: List SCDecl * List SCDecl -> List SCDecl
 def unionProofDecls(pfDecls1, pfDecls2) =
    let def insert (pd as (pdName, _), pfDecls) = 
    case pfDecls of
      | [] -> [pd]
      | pd1::pds ->
          let (pdName1, _) = pd1 in
	  if pdName = pdName1 then
            pds
          else
            Cons (pd1, ListUtilities.insert (pd, pds)) in
     foldl insert pfDecls1 pfDecls2


 op generateProofsInSpec: Spec * SCTerm * Boolean * Spec * Boolean * String * ProverOptions * List ClaimName * GlobalContext * List UnitId * Option UnitId -> List SCDecl
 def generateProofsInSpec (spc, scTerm, fromObligations?, baseSpc, multipleFiles, prover_name, prover_options, basePropNames, globalContext, swpath, fileUID) =
   let imports = (spc.importInfo).imports in
   %let _ = debug("import check") in
   let importProofDecls =
   foldr (fn (imprt, res) -> 
	  let (importSCTerm, importSpc) = imprt in
	  let importProofs =
	    if baseUnitIdSCTerm?(importSCTerm)
	      then []
	    else generateProofsInSpec(importSpc, importSCTerm, fromObligations?, baseSpc, multipleFiles, prover_name, prover_options, basePropNames, globalContext, swpath, fileUID) in
	  unionProofDecls(importProofs, res))
         []
	 imports in
   let importPropNames =
   map (fn (proofDecl) ->
	let (prfName, prfTerm) = proofDecl in
	let (Prove (claimName, _, _, _, _, _), _) = prfTerm in
	claimName)
       importProofDecls in
   let localProofDecls =
   generateLocalProofsInSpec(spc, scTerm, multipleFiles,
			     fromObligations?, prover_name, prover_options,
			     importPropNames++basePropNames, globalContext, swpath, fileUID) in
   let _ = debug("genprfsinspc") in
   unionProofDecls(localProofDecls, importProofDecls)

 op generateProofsInMorph: Morphism * SCTerm * Boolean * Spec * Boolean * String * ProverOptions * List ClaimName * GlobalContext * List UnitId * Option UnitId -> List SCDecl
 def generateProofsInMorph (morph, scTerm, fromObligations?, baseSpc, multipleFiles, prover_name, prover_options, basePropNames, globalContext, swpath, fileUID) =
   let spc = morphismObligations(morph, globalContext, noPos) in
   let imports = (spc.importInfo).imports in
   %let _ = debug("import check") in
   let importProofDecls =
   foldr (fn (imprt, res) -> 
	  let (importSCTerm, importSpc) = imprt in
	  let importProofs =
	    if baseUnitIdSCTerm?(importSCTerm)
	      then []
	    else generateProofsInSpec(importSpc, importSCTerm, fromObligations?, baseSpc, multipleFiles, prover_name, prover_options, basePropNames, globalContext, swpath, fileUID) in
	  unionProofDecls(importProofs, res))
         []
	 imports in
   let importPropNames =
   map (fn (proofDecl) ->
	let (prfName, prfTerm) = proofDecl in
	let (Prove (claimName, _, _, _, _, _), _) = prfTerm in
	claimName)
       importProofDecls in
   let localProofDecls =
   generateLocalProofsInMorph(morph, scTerm, multipleFiles,
			      fromObligations?, prover_name, prover_options,
			      importPropNames++basePropNames, globalContext, swpath, fileUID) in
   let _ = debug("genprfsinspc") in
   unionProofDecls(localProofDecls, importProofDecls)

 op generateLocalProofsInSpec: Spec * SCTerm * Boolean * Boolean * String * ProverOptions * List ClaimName * GlobalContext * List UnitId * Option UnitId -> List SCDecl
 def generateLocalProofsInSpec (spc, scTerm, multipleFiles, fromObligations?, prover_name, prover_options, previousPropNames, globalContext, swpath, fileUID) =
   let usedSpc = if fromObligations? then specObligations(spc, scTerm) else spc in 
   let props = usedSpc.properties in
   let localProps = filter (fn (prop) -> let (propType, propName, _, _) = prop in 
			                  ~(member(propName, previousPropNames))
			                  & ~(propType = Axiom)) props in
   map (fn (prop) -> generateProof(spc, scTerm, prop, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID)) localProps

 op generateLocalProofsInMorph: Morphism * SCTerm * Boolean * Boolean * String * ProverOptions * List ClaimName * GlobalContext * List UnitId * Option UnitId -> List SCDecl
 def generateLocalProofsInMorph (morph, scTerm, multipleFiles, fromObligations?, prover_name, prover_options, previousPropNames, globalContext, swpath, fileUID) =
   let usedSpc = morphismObligations(morph, globalContext, noPos) in 
   let props = usedSpc.properties in
   let localProps = filter (fn (prop) -> let (propType, propName, _, _) = prop in 
			                  ~(member(propName, previousPropNames))
			                  & ~(propType = Axiom)) props in
   map (fn (prop) -> generateProofMorphism(morph, scTerm, prop, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID)) localProps

 % The difference between generateProofsInSpecLocal and generateLocalProofsInSpec is that generateProofsInSpecLocal is used by the
 % lpunits commands to only generate local proofs, while generateLocalProofsInSpec is the original code used as part of the full punits command.
 % Eventually I'll only use generateProofsInSpecLocal.
 op generateProofsInSpecLocal: Spec * SCTerm * Boolean * Boolean * String * ProverOptions * GlobalContext * List UnitId * Option UnitId -> List SCDecl
 def generateProofsInSpecLocal (spc, scTerm, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID) =
   let usedSpc = if fromObligations? then specObligations(spc, scTerm) else spc in 
   let props = usedSpc.properties in
   let _ = map (fn (pn) -> writeLine(printQualifiedId(pn))) (usedSpc.importInfo).localProperties in
   let localPropNames = if fromObligations?
			  then ((usedSpc.importInfo).localProperties)++(spc.importInfo).localProperties
			else (usedSpc.importInfo).localProperties in
   let localProps = filter (fn (prop) -> let (propType, propName, _, _) = prop in 
			                  (member(propName, localPropNames))
			                  & ~(propType = Axiom)) props in
   map (fn (prop) -> generateProof(spc, scTerm, prop, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID)) localProps

 op generateProofsInMorphLocal: Morphism * SCTerm * Boolean * Boolean * String * ProverOptions * GlobalContext * List UnitId * Option UnitId -> List SCDecl
 def generateProofsInMorphLocal (morph, scTerm, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID) =
   let usedSpc = morphismObligations(morph, globalContext, noPos) in 
   let props = usedSpc.properties in
   let _ = map (fn (pn) -> writeLine(printQualifiedId(pn))) (usedSpc.importInfo).localProperties in
   let localPropNames = if fromObligations?
			  then ((usedSpc.importInfo).localProperties)
			else (usedSpc.importInfo).localProperties in
   let localProps = filter (fn (prop) -> let (propType, propName, _, _) = prop in 
			                  (member(propName, localPropNames))
			                  & ~(propType = Axiom)) props in
   map (fn (prop) -> generateProofMorphism(morph, scTerm, prop, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID)) localProps

% op ppProof: SCDecl -> WadlerLindig.Pretty

% def ppProof(proof) =
%   SpecCalc.ppTerm(proof)

 op ppProofs: List SCDecl -> WadlerLindig.Pretty

 def ppProofs(proofs) =
   ppAppend (ppDecls(proofs)) ppNewline
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

 op toProofFileEnv: Spec * SCTerm * Boolean * Boolean * Spec * Boolean * GlobalContext * List UnitId * Option UnitId * String -> ()
 def toProofFileEnv (spc, spcTerm, fromObligations?, local?, baseSpc, multipleFiles, globalContext, swpath, fileUID, file) =
   %let _ = writeLine("Writing Proof file "^file) in
   let basePropNames = map (fn (_, pn, _, _) -> pn) baseSpc.properties in
   let proofDecls =
     if local?
       then generateProofsInSpecLocal(spc, spcTerm, multipleFiles, fromObligations?, "Snark", OptionString ([string ("")]), globalContext, swpath, fileUID)
     else generateProofsInSpec(spc, spcTerm, fromObligations?, baseSpc, multipleFiles, "Snark", OptionString ([string ("")]), basePropNames, globalContext, swpath, fileUID) in
   ppProofsToFile(proofDecls, file)

 op toProofFileMorphEnv: Morphism * SCTerm * Boolean * Boolean * Spec * Boolean * GlobalContext * List UnitId * Option UnitId * String -> ()
 def toProofFileMorphEnv (morph, morphTerm, fromObligations?, local?, baseSpc, multipleFiles, globalContext, swpath, fileUID, file) =
   %let _ = writeLine("Writing Proof file "^file) in
   let basePropNames = map (fn (_, pn, _, _) -> pn) baseSpc.properties in
   let proofDecls =
     if local?
       then generateProofsInMorphLocal(morph, morphTerm, multipleFiles, fromObligations?, "Snark", OptionString ([string ("")]), globalContext, swpath, fileUID)
     else generateProofsInMorph(morph, morphTerm, fromObligations?, baseSpc, multipleFiles, "Snark", OptionString ([string ("")]), basePropNames, globalContext, swpath, fileUID) in
   ppProofsToFile(proofDecls, file)

  op toProofFile    : Spec * SCTerm * Spec * Boolean * GlobalContext * List UnitId * Option UnitId * String * Boolean * Boolean -> ()
  def toProofFile (spc, spcTerm, baseSpc, multipleFiles, globalContext, swpath, fileUID, file, fromObligations?, local?) =  
      toProofFileEnv (spc, spcTerm, fromObligations?, local?, baseSpc, multipleFiles, globalContext, swpath, fileUID, file) 

  op toProofFileMorph    : Morphism * SCTerm * Spec * Boolean * GlobalContext * List UnitId * Option UnitId * String * Boolean * Boolean -> ()
  def toProofFileMorph (morph, morphTerm, baseSpc, multipleFiles, globalContext, swpath, fileUID, file, fromObligations?, local?) =  
      toProofFileMorphEnv (morph, morphTerm, fromObligations?, local?, baseSpc, multipleFiles, globalContext, swpath, fileUID, file) 

(*
 op localThmsToProofFile: Spec * SCTerm * Boolean * Spec * Boolean * Option fileUID * String -> ()
 def localThmsToProofFile (spc, spcTerm, fromObligations?, baseSpc, multipleFiles, globalContext, swpath, fileUID, file) =
   let basePropNames = map (fn (_, pn, _, _) -> pn) baseSpc.properties in
   let proofDecls = generateProofsInSpecLocal(spc, spcTerm, fromObligations?, baseSpc, multipleFiles, "Snark", OptionString ([string ("")]), basePropNames, globalContext, swpath, fileUID) in
   ppProofsToFile(proofDecls, file)
*)


  op SpecCalc.evaluateProofGen : ValueInfo * (SpecCalc.Term Position) * Option String * Boolean
                                -> SpecCalc.Env ValueInfo

  %% Need to add error detection code

  def SpecCalc.evaluateProofGen (valueInfo as (value,_,_), cterm, optFileNm, fromObligations?) =
    {%(preamble,_) <- compileImports(importedSpecsList spc.importedSpecs,[],[spc]);
     cUID <- SpecCalc.getUID(cterm);
     globalContext <- getGlobalContext;

     (proofFileUID, proofFileName, multipleFiles) <-  UIDtoProofFile(cUID, optFileNm);
     (optBaseUnitId,baseSpec) <- getBase;
     swpath <- getSpecPath;
     %let _ = printSpecToTerminal(baseSpec) inI should 
     print (";;; Generating proof file " ^ proofFileName ^ "\n");
     return (ensureDirectoriesExist proofFileName);
     case value of
       | Spec spc -> return (toProofFile (spc, cterm, baseSpec, multipleFiles, globalContext, swpath, proofFileUID, proofFileName, fromObligations?, false))
       | Morph morph -> return (toProofFileMorph (morph, cterm, baseSpec, multipleFiles, globalContext, swpath, proofFileUID, proofFileName, fromObligations?, false))
       | _ -> raise (Unsupported ((positionOf cterm),
				  "Can generate proofs only for Specs and Morphisms."));
%     let _ = System.fail ("evaluateProofGen ") in
     {print("Generated Proof file.");
      return valueInfo}}

  op SpecCalc.evaluateProofGenLocal : ValueInfo * (SpecCalc.Term Position) * Option String * Boolean
                                -> SpecCalc.Env ValueInfo

  def SpecCalc.evaluateProofGenLocal(valueInfo as (value,_,_), cterm, optFileName, fromObligations?) =
    {cUID <- SpecCalc.getUID cterm;
     globalContext <- getGlobalContext;
     (proofFileUID, proofFileName, multipleFiles) <- UIDtoProofFile (cUID, optFileName);
     (optBaseUnitId,baseSpec) <- getBase;
     swpath <- getSpecPath;
     print (";;; Generating proof file " ^ proofFileName ^ "\n");
     let _ = ensureDirectoriesExist proofFileName in
     case value of
       | Spec spc -> return (toProofFile (spc, cterm, baseSpec, multipleFiles, globalContext, swpath, proofFileUID, proofFileName, fromObligations?, true))
       | Morph morph -> return (toProofFileMorph (morph, cterm, baseSpec, multipleFiles, globalContext, swpath, proofFileUID, proofFileName, fromObligations?, true))
       | _ -> raise (Unsupported ((positionOf cterm),
				  "Can generate proofs only for Specs and Morphisms."));
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

 op UIDtoProofFile: UnitId * Option String -> SpecCalc.Env(Option UnitId * String * Boolean)
 def UIDtoProofFile ((unitId as {path,hashSuffix}), optFileNm) = 
   case optFileNm
      of Some filNam -> return (None, filNam, false)
       | _ ->
	{
   (fileUID, file, bool) <-
   case hashSuffix of
     | None -> UIDtoSingleProofFile(unitId)
     | Some _ -> UIDtoMultipleProofFile(unitId);
   return (Some fileUID, file, bool)
 }

 op UIDtoSingleProofFile: UnitId -> Env (UnitId * String * Boolean)
 def UIDtoSingleProofFile (unitId as {path,hashSuffix}) = {
    prefix <- (removeLastElem path);
    mainName <- lastElem path;
    fileUID <- return {path=prefix,hashSuffix=None};
    let filNm = (uidToFullPath fileUID)
%        ^ "/proofs/" ^ mainName ^ ".log"
        ^  "/" ^ mainName ^ "_Proofs" ^".sw"
     in
      return (fileUID, filNm, false)}

 op UIDtoMultipleProofFile: UnitId -> Env (UnitId * String * Boolean)
 def UIDtoMultipleProofFile (unitId as {path,hashSuffix}) =
   let Some hashSuffix = hashSuffix in
    {prefix <- removeLastElem path;
     newSubDir <- lastElem path;
     mainName <- return hashSuffix;
     fileUID <- return {path=prefix,hashSuffix=None};
     let filNm = (uidToFullPath fileUID)
%        ^ "/proofs/" ^ newSubDir ^ "/" ^ mainName ^ ".log"
        ^ "/" ^ newSubDir ^ "_" ^ mainName ^ "_Proofs" ^ ".sw"
     in
      return (fileUID, filNm, true)}


endspec
