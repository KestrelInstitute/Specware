(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying
spec

 import Signature    % including SCTerm
 import UnitId
 import Obligations

 op generateProof: Spec * SCTerm * Property * Bool * Bool * String * ProverOptions * GlobalContext * UnitIds * Option UnitId -> SCDecl
 def generateProof (spc, scTerm, prop, _(*multipleFiles*), fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID) =
   let def printProofName(qid as Qualified (qual, id)) =
        if qual = UnQualified then
	  id^"_proof"
	else qual^"_"^id^"_proof" in
   let assertions = All in
   let (_, propName, _, _,_) = prop in
   let scTerm    = scTermFromScTerm(Spec spc, scTerm, globalContext, fileUID, swpath, fromObligations?) in
   let proveTerm = Prove (propName, scTerm, prover_name, assertions, prover_options, ProverBase, None) in
   let proofName = printProofName(propName) in
   let ProveTerm_A: SCTerm = (proveTerm, noPos) in
   (proofName, ProveTerm_A)

 op generateProofMorphism: Morphism * SCTerm * Property * Bool * Bool * String * ProverOptions * GlobalContext * UnitIds * Option UnitId -> SCDecl
 def generateProofMorphism (morph, scTerm, prop, _(*multipleFiles*), fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID) =
   let def printProofName(qid as Qualified (qual, id)) =
        if qual = UnQualified then
	  id^"_proof"
	else qual^"_"^id^"_proof" in
   let assertions = All in
   let (_, propName, _, _,_) = prop in
   let scTerm = scTermFromScTerm(Morph morph, scTerm, globalContext, fileUID, swpath, fromObligations?) in
   let proveTerm = Prove (propName, scTerm, prover_name, assertions, prover_options, ProverBase, None) in
   let proofName = printProofName(propName) in
   let ProveTerm_A: SCTerm = (proveTerm, noPos) in
   (proofName, ProveTerm_A)

 op scTermFromScTerm: Value * SCTerm * GlobalContext * Option UnitId * UnitIds * Bool -> SCTerm
 def scTermFromScTerm(v, scTerm, globalContext, fileUID, swpath, fromObligations?) =
   case findUnitIdForUnit(v, globalContext) of
     | Some specFullUId ->
     let specUId = relativeUidToUidAndSWPATH(specFullUId, fileUID, swpath) in
     if fromObligations?
       then (Obligations specUId (* (UnitId (UnitId_Relative specUId), noPos) *), noPos)
     else specUId %(UnitId (SpecPath_Relative specUId), noPos)
     | _ ->
       let (_, pos) = scTerm in
       if fromObligations?
	 then (Obligations scTerm, pos)
       else scTerm

 (* 
  uid is an absolute path of the spec or morphism for which the proof units are generated.
  baseUid is an absolute path of the spec for the file for where the proof units are to be written.
  (This maybe left unspecified.)
  If baeUid is given then relativeUidToUidAndSWPATH returns a relativeUid that is equivalent to the
  absoulte UiD, but is relative to baseUid.
  e.g. if baseUid = /sub1/base.sw, and uid = /sub1/sub2/file.sw, then
  relativeUidToUidAndSWPATH = sub2/file.sw.
  If baseUid is None, then relativeUidToUidAndSWPATH returns a Uid that is equivalent to uid, but with respect to SWPATH.
  *)
 
 op relativeUidToUidAndSWPATH: UnitId * Option UnitId * UnitIds -> SCTerm
 def relativeUidToUidAndSWPATH(uid as {path,hashSuffix}, baseUid, swpath) =
   case baseUid of
     | None -> (UnitId (SpecPath_Relative (relativeUidToSWPATH(uid, swpath))), noPos)
     | Some baseUid ->
     let uIdRelativeToBase = relativeUidToUid(uid, baseUid) in
     case uIdRelativeToBase of
       | Some newUid -> (UnitId (UnitId_Relative newUid), noPos)
       | _ -> (UnitId (SpecPath_Relative (relativeUidToSWPATH(uid, swpath))), noPos)

 op relativeUidToUid: UnitId * UnitId -> Option UnitId
 def relativeUidToUid(uid, baseUid) =
   let tailUidPath = tailListList(uid.path, baseUid.path) in
   case tailUidPath of
     | Some tailPath -> Some ({path = tailPath, hashSuffix = uid.hashSuffix})
     | _ -> None
 
 op relativeUidToSWPATH: UnitId * UnitIds -> UnitId
 def relativeUidToSWPATH(uid, swpath) =
   %let _ = String.writeLine("\n relativeUidToSWPATH UID = "^showUID(uid)^"\n swPath = "^(foldr concat "," (map (fn (path) -> (showUID(path)^" ; ")) swpath))) in 
   let foundSwUid = findOption (fn (swUid) -> relativeUidToUid(uid, swUid)) swpath in
   case foundSwUid of
     | Some res -> res
     | _ -> fail("can't happen")

 op baseUnitIdSCTerm?: SCTerm -> Bool
 def baseUnitIdSCTerm?(scTerm) =
   case scTerm of
     | (UnitId ( UnitId_Relative (uid)), _) -> let path = uid.path in head(path) = "Base"
     | _ -> false

 op unionProofDecls: SCDecls * SCDecls -> SCDecls
 def unionProofDecls(pfDecls1, pfDecls2) =
    let def insert (pfDecls, pd as (pdName, _)) = 
    case pfDecls of
      | [] -> [pd]
      | pd1::pds ->
          let (pdName1, _) = pd1 in
	  if pdName = pdName1 then
            pfDecls
          else
            Cons (pd1, insert (pds, pd)) in
     foldl insert pfDecls1 pfDecls2

 op generateProofsInSpec: Spec * SCTerm * Bool * Spec * Bool * String * ProverOptions * ClaimNames * GlobalContext * UnitIds * Option UnitId -> SCDecls
 def generateProofsInSpec (spc, scTerm, fromObligations?, baseSpc, multipleFiles, prover_name, prover_options, basePropNames, globalContext, swpath, fileUID) =
   %let imports = (spc.importInfo).imports in
   %let _ = debug("import check") in
   let importProofDecls =
   foldr (fn (el, res) ->
	  case el of
	    | Import(importSCTerm, importSpc,_,_) ->
	      let importProofs =
	          if importSpc = getBaseSpec() %baseUnitIdSCTerm?(importSCTerm)
		    then []
		  else generateProofsInSpec(importSpc, importSCTerm, fromObligations?, baseSpc,
					    multipleFiles, prover_name, prover_options, basePropNames,
					    globalContext, swpath, fileUID)
	      in
	      unionProofDecls(importProofs, res)
	    | _ -> res)
         []
	 spc.elements in
   let importPropNames =
   map (fn (proofDecl) ->
	let (prfName, prfTerm) = proofDecl in
	let (Prove (claimName, _, _, _, _, _, _), _) = prfTerm in
	claimName)
       importProofDecls in
   let localProofDecls =
   generateLocalProofsInSpec(spc, scTerm, multipleFiles,
			     fromObligations?, prover_name, prover_options,
			     importPropNames++basePropNames, globalContext, swpath, fileUID) in
   let _ = debug("genprfsinspc") in
   unionProofDecls(localProofDecls, importProofDecls)

 op generateProofsInMorph: Morphism * SCTerm * Bool * Spec * Bool * String * ProverOptions * ClaimNames * GlobalContext * UnitIds * Option UnitId -> SCDecls
 def generateProofsInMorph (morph, scTerm, fromObligations?, baseSpc, multipleFiles, prover_name, prover_options, basePropNames, globalContext, swpath, fileUID) =
   let spc = morphismObligations(morph, globalContext, noPos) in
   %let imports = (spc.importInfo).imports in
   %let _ = debug("import check") in
   let importProofDecls =
   foldr (fn (el, res) ->
	  case el of
	    | Import(importSCTerm, importSpc,_,_) ->
	      let importProofs =
	          if importSpc = getBaseSpec() % baseUnitIdSCTerm?(importSCTerm)
		    then []
		  else generateProofsInSpec(importSpc, importSCTerm, fromObligations?, baseSpc,
					    multipleFiles, prover_name, prover_options, basePropNames,
					    globalContext, swpath, fileUID) in
	      unionProofDecls(importProofs, res)
	    | _ -> res)
         []
	 spc.elements in
   let importPropNames =
   map (fn (proofDecl) ->
	let (prfName, prfTerm) = proofDecl in
	let (Prove (claimName, _, _, _, _, _, _), _) = prfTerm in
	claimName)
       importProofDecls in
   let localProofDecls =
   generateLocalProofsInMorph(morph, scTerm, multipleFiles,
			      fromObligations?, prover_name, prover_options,
			      importPropNames++basePropNames, globalContext, swpath, fileUID) in
   let _ = debug("genprfsinspc") in
   unionProofDecls(localProofDecls, importProofDecls)

 op generateLocalProofsInSpec: Spec * SCTerm * Bool * Bool * String * ProverOptions * ClaimNames * GlobalContext * UnitIds * Option UnitId -> SCDecls
 def generateLocalProofsInSpec (spc, scTerm, multipleFiles, fromObligations?, prover_name, prover_options, previousPropNames, globalContext, swpath, fileUID) =
   let usedSpc = if fromObligations? then specObligations(spc, scTerm) else spc in 
   let props = allProperties usedSpc in
   let localProps = filter (fn (prop) -> let (propType, propName, _, _, _) = prop in 
			                 propName nin? previousPropNames
			                  && ~(propType = Axiom)) props in
   map (fn (prop) -> generateProof(spc, scTerm, prop, multipleFiles, fromObligations?, prover_name,
				   prover_options, globalContext, swpath, fileUID))
     localProps

 op generateLocalProofsInMorph: Morphism * SCTerm * Bool * Bool * String * ProverOptions * ClaimNames * GlobalContext * UnitIds * Option UnitId -> SCDecls
 def generateLocalProofsInMorph (morph, scTerm, multipleFiles, fromObligations?, prover_name, prover_options, previousPropNames, globalContext, swpath, fileUID) =
   let usedSpc = morphismObligations(morph, globalContext, noPos) in 
   let props = allProperties usedSpc in
   let localProps = filter (fn (prop) -> let (propType, propName, _, _, _) = prop in 
			                 propName nin? previousPropNames
			                  && ~(propType = Axiom)) props in
   map (fn (prop) -> generateProofMorphism(morph, scTerm, prop, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID)) localProps

 % The difference between generateProofsInSpecLocal and generateLocalProofsInSpec is that generateProofsInSpecLocal is used by the
 % lpunits commands to only generate local proofs, while generateLocalProofsInSpec is the original code used as part of the full punits command.
 % Eventually I'll only use generateProofsInSpecLocal.
 op generateProofsInSpecLocal: Spec * SCTerm * Bool * Bool * String * ProverOptions * GlobalContext * UnitIds * Option UnitId -> SCDecls
 def generateProofsInSpecLocal (spc, scTerm, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID) =
   let usedSpc = if fromObligations? then specObligations(spc, scTerm) else spc in 
   let props = localProperties usedSpc in
   %let _ = map (fn (pn) -> writeLine(printQualifiedId(pn))) (usedSpc.importInfo).localProperties in
   let localProps = filter (fn (propType, propName, _, _, _) -> ~(propType = Axiom)) props in
   map (fn (prop) -> generateProof(spc, scTerm, prop, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID)) localProps

 op generateProofsInMorphLocal: Morphism * SCTerm * Bool * Bool * String * ProverOptions * GlobalContext * UnitIds * Option UnitId -> SCDecls
 def generateProofsInMorphLocal (morph, scTerm, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID) =
   let usedSpc = morphismObligations(morph, globalContext, noPos) in 
   let props = localProperties usedSpc in
   %let _ = map (fn (pn) -> writeLine(printQualifiedId(pn))) (usedSpc.importInfo).localProperties in
   let localProps = filter (fn (propType, propName, _, _, _) -> ~(propType = Axiom)) props in
   map (fn (prop) -> generateProofMorphism(morph, scTerm, prop, multipleFiles, fromObligations?, prover_name, prover_options, globalContext, swpath, fileUID)) localProps

% op ppProof: SCDecl -> WadlerLindig.Pretty

% def ppProof(proof) =
%   SpecCalc.ppTerm(proof)

 op ppProofs: SCDecls -> WLPretty
 def ppProofs(proofs) =
   ppAppend (ppDecls(proofs)) ppNewline
%   ppSep ppNewline (map ppProof proofs)

 op ppProofsToFile: SCDecls * String -> ()

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

 op toProofFileEnv: Spec * SCTerm * Bool * Bool * Spec * Bool * GlobalContext * UnitIds * Option UnitId * String -> ()
 def toProofFileEnv (spc, spcTerm, fromObligations?, local?, baseSpc, multipleFiles, globalContext, swpath, fileUID, file) =
   %let _ = writeLine("Writing Proof file "^file) in
   let basePropNames = map (fn (_, pn, _, _, _) -> pn) (allProperties baseSpc) in
   let proofDecls =
     if local?
       then generateProofsInSpecLocal(spc, spcTerm, multipleFiles, fromObligations?, "Snark", OptionString ([string ("")]), globalContext, swpath, fileUID)
     else generateProofsInSpec(spc, spcTerm, fromObligations?, baseSpc, multipleFiles, "Snark", OptionString ([string ("")]), basePropNames, globalContext, swpath, fileUID) in
   ppProofsToFile(proofDecls, file)

 op toProofFileMorphEnv: Morphism * SCTerm * Bool * Bool * Spec * Bool * GlobalContext * UnitIds * Option UnitId * String -> ()
 def toProofFileMorphEnv (morph, morphTerm, fromObligations?, local?, baseSpc, multipleFiles, globalContext, swpath, fileUID, file) =
   %let _ = writeLine("Writing Proof file "^file) in
   let basePropNames = map (fn (_, pn, _, _, _) -> pn) (allProperties baseSpc) in
   let proofDecls =
     if local?
       then generateProofsInMorphLocal(morph, morphTerm, multipleFiles, fromObligations?, "Snark", OptionString ([string ("")]), globalContext, swpath, fileUID)
     else generateProofsInMorph(morph, morphTerm, fromObligations?, baseSpc, multipleFiles, "Snark", OptionString ([string ("")]), basePropNames, globalContext, swpath, fileUID) in
   ppProofsToFile(proofDecls, file)

  op toProofFile    : Spec * SCTerm * Spec * Bool * GlobalContext * UnitIds * Option UnitId * String * Bool * Bool -> ()
  def toProofFile (spc, spcTerm, baseSpc, multipleFiles, globalContext, swpath, fileUID, file, fromObligations?, local?) =  
      toProofFileEnv (spc, spcTerm, fromObligations?, local?, baseSpc, multipleFiles, globalContext, swpath, fileUID, file) 

  op toProofFileMorph    : Morphism * SCTerm * Spec * Bool * GlobalContext * UnitIds * Option UnitId * String * Bool * Bool -> ()
  def toProofFileMorph (morph, morphTerm, baseSpc, multipleFiles, globalContext, swpath, fileUID, file, fromObligations?, local?) =  
      toProofFileMorphEnv (morph, morphTerm, fromObligations?, local?, baseSpc, multipleFiles, globalContext, swpath, fileUID, file) 

(*
 op localThmsToProofFile: Spec * SCTerm * Bool * Spec * Bool * Option fileUID * String -> ()
 def localThmsToProofFile (spc, spcTerm, fromObligations?, baseSpc, multipleFiles, globalContext, swpath, fileUID, file) =
   let basePropNames = map (fn (_, pn, _, _) -> pn) baseSpc.properties in
   let proofDecls = generateProofsInSpecLocal(spc, spcTerm, fromObligations?, baseSpc, multipleFiles, "Snark", OptionString ([string ("")]), basePropNames, globalContext, swpath, fileUID) in
   ppProofsToFile(proofDecls, file)
*)

  op SpecCalc.evaluateProofGen : ValueInfo * SCTerm * Option String * Bool -> SpecCalc.Env ValueInfo
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
       | Other other -> SpecCalc.evaluateOtherProofGen(other, cterm, optFileNm, fromObligations?) (positionOf(cterm))
       | _ -> raise (Unsupported ((positionOf cterm),  "Can generate proofs only for Specs and Morphisms."));
%     let _ = System.fail ("evaluateProofGen ") in
     {print("Generated Proof file: " ^ proofFileName ^ "\n");
      return valueInfo}}

  op SpecCalc.evaluateProofGenLocal : ValueInfo * SCTerm * Option String * Bool -> SpecCalc.Env ValueInfo
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
       | Other other -> SpecCalc.evaluateOtherProofGenLocal(other, cterm, optFileName, fromObligations?) (positionOf(cterm))
       | _ -> raise (Unsupported ((positionOf cterm), "Can generate proofs only for Specs and Morphisms."));
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

 op UIDtoProofFile: UnitId * Option String -> SpecCalc.Env(Option UnitId * String * Bool)
 def UIDtoProofFile ((unitId as {path,hashSuffix}), optFileNm) = 
   case optFileNm
      of Some filNam ->
	let fileUid = normalizeUID(pathStringToCanonicalUID(filNam,false)) in
	let filePath = addDevice?(fileUid.path) in
	let fileUid = {path=butLast filePath, hashSuffix=None} in
	return (Some fileUid, filNam, false)
       | _ ->
	{
   (fileUID, file, bool) <-
   case hashSuffix of
     | None -> UIDtoSingleProofFile(unitId)
     | Some _ -> UIDtoMultipleProofFile(unitId);
   return (Some fileUID, file, bool)
 }

 op UIDtoSingleProofFile: UnitId -> Env (UnitId * String * Bool)
 def UIDtoSingleProofFile (unitId as {path,hashSuffix}) = {
    prefix <- (removeLast path);
    mainName <- last path;
    fileUID <- return {path=prefix,hashSuffix=None};
    let filNm = (uidToFullPath fileUID)
%        ^ "/proofs/" ^ mainName ^ ".log"
        ^  "/" ^ mainName ^ "_Proofs" ^".sw"
     in
      return (fileUID, filNm, false)}

 op UIDtoMultipleProofFile: UnitId -> Env (UnitId * String * Bool)
 def UIDtoMultipleProofFile (unitId as {path,hashSuffix}) =
   let Some hashSuffix = hashSuffix in
    {prefix <- removeLast path;
     newSubDir <- last path;
     mainName <- return hashSuffix;
     fileUID <- return {path=prefix,hashSuffix=None};
     let filNm = (uidToFullPath fileUID)
%        ^ "/proofs/" ^ newSubDir ^ "/" ^ mainName ^ ".log"
        ^ "/" ^ newSubDir ^ "_" ^ mainName ^ "_Proofs" ^ ".sw"
     in
      return (fileUID, filNm, true)}


endspec


%%
%% $Id$
%%
%% $Log$
%% Revision 1.35  2011/10/14 10:53:38  mcdonald
%% pervasive internal cleanup affecting about 350 files
%%
%% Among other things:
%%
%% 'sort' should now be fully removed in favor of 'type'
%% (but 'sort' is still accepted for the time being)
%% As a side effect, some files that had "Sort" in their names
%% have been renamed to use "Type", to avoid confusion.
%%
%% The type 'Boolean' should now be fully removed in favor of 'Bool'
%% (but 'Boolean' is still defined as 'Bool' for now)
%%
%% The internal types for structures in the Metaslang abstract syntax
%% are now universally referenced as 'MSType', 'MSTerm', and 'MSPattern',
%% to make it easier to avoid conflicts with descriptions of types, terms,
%% and patterns in other langauges such as SpecCalculus, Lisp, Java, C,
%% Haskell, Isabelle, etc.
%%
%% Some imports have been restructured to more cleanly share declarations.
%%
%% And probably some other minor changes as well...
%%
%% Revision 1.34  2011/10/11 07:37:55  mcdonald
%% internal revisions to simplify specs:
%%
%% pervasive change to eliminate polymorphism in SpecCalculus terms
%%
%% also misc changes to simplify imports
%%
%% also misc changes to clarify some names of some types
%%
%% Revision 1.33  2009/12/08 22:52:40  westfold
%% Update Specware to not use deprecated ops
%%
%% Revision 1.32  2009/08/20 01:21:02  westfold
%% && ||
%%
%% Revision 1.31  2008/09/14 14:27:14  mcdonald
%% massive update to use reversed order of args for function passed to foldl
%%
%% Revision 1.30  2007/05/24 00:41:05  westfold
%% Remove WFO spec move wfo to Functions
%% Improve SNARK's handling of succ
%% Make punits recognize import of base spec
%%
%% Revision 1.29  2007/05/09 20:47:08  westfold
%% Add position information to ASpecElements
%%
%% Revision 1.28  2006/08/10 01:20:04  westfold
%% Cache terms for computing UnitIds as well as values.
%%
%% Revision 1.27  2005/08/05 02:04:40  mcdonald
%% show proof file name
%%
%% Revision 1.26  2005/04/01 21:43:24  gilham
%% Changed evaluateProve to support OtherValues in addition to Specs.
%% Fixed a problem with invalid file names for proof files.
%% Fixed some bugs in the definition of unionProofDecls
%%
%% Revision 1.25  2005/03/23 02:13:34  westfold
%% Major update to include sequence of spec elements in spec.
%%
%% Revision 1.24  2004/11/30 20:09:35  westfold
%% Fix handling of devices in windows for uids and swpath
%%
%% Revision 1.23  2004/11/12 23:02:24  cyrluk
%% Added other for ProofGen.
%%
%% Revision 1.22  2004/11/12 19:04:53  becker
%% Added the signature and default implementations to
%% evaluateProofGenOther  and evaluateProofGenLocalOther
%% to dispatch the generation of proof obligations to functions
%% outside Specware.
%%
%%
%%
