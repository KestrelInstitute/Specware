SpecCalc qualifying spec {
  import UnitId
  %import SpecUnion
  import /Languages/Snark/SpecToSnark
  import /Provers/DP/ToFourierMotzkin
  import /Languages/MetaSlang/Transformations/ExplicateHiddenAxioms
  import /Languages/MetaSlang/Transformations/RemoveQuotient
  import /Languages/MetaSlang/CodeGen/CodeGenTransforms
  import UnitId/Utilities                                    % for uidToString, if used...

 op PARSER4.READ_LIST_OF_S_EXPRESSIONS_FROM_STRING: String -> ProverOptions
  
 def SpecCalc.evaluateProve (claimName, specTerm, proverName, assertions, possibleOptions, baseOptions, answerVariable) pos = {
     unitId <- getCurrentUnitId;
     print (";;; Elaborating proof-term at " ^ (uidToString unitId) ^ "\n");
     (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo specTerm;
     (optBaseUnitId,baseSpec) <- getBase;
     baseProverSpec <- getBaseProverSpec;
     rewriteProverSpec <- getRewriteProverSpec;
     proverLogFileName <- UIDtoLogFile(unitId, if proverName = "Both" then "Snark" else proverName, "log");
     finalSpecFileName <- UIDtoLogFile(unitId, if proverName = "Both" then "Snark" else proverName, "sw");
     _ <- return (ensureDirectoriesExist proverLogFileName);
     proofName <- return (UIDtoProofName unitId);
     specName <- return (SpecTermToSpecName(specTerm));
     userSpec <- (
		  case coerceToSpec value of
		    | Spec spc -> return spc %specUnion([spc, baseProverSpec])
		    | _ -> raise (Proof (pos, "Argument to prove command is not coerceable to a spec.")));
     expandedSpec <- return (transformSpecForFirstOrderProver baseSpec userSpec);
     _ <- return (writeLine("    Expanded spec file: " ^ finalSpecFileName));
     _ <- return (writeLine("    Snark Log file: " ^ proverLogFileName));
     _ <- return (printFlatSpecToFile(finalSpecFileName, expandedSpec));
     _ <- return (if specwareDebug? then writeString(printSpec(expandedSpec)) else ());
     proverOptions <- 
       (case possibleOptions of
	  | OptionString proverOptions -> return (proverOptions)
	  | OptionName proverOptionName -> 
	        proverOptionsFromSpec(proverOptionName, userSpec, specName)
	  | Error   (msg, str)     -> raise  (SyntaxError (msg ^ str)));
     includeBase <- return proverUseBase?;
     proved <- (proveInSpec (proofName,
			     claimName, 
			     expandedSpec,
			     specName,
			     baseProverSpec,
			     rewriteProverSpec,
			     proverName, 
			     assertions, 
			     proverOptions,
			     includeBase,
			     answerVariable,
			     proverLogFileName,
			     pos));
     result <- return (Proof {status = if proved then Proved else Unproved, 
			      unit   = unitId});
     return (result, timeStamp, depUIDs)
   }


  op transformSpecForFirstOrderProver: AnnSpec.Spec -> AnnSpec.Spec -> AnnSpec.Spec
  def transformSpecForFirstOrderProver baseSpc spc =
    let spc = addMissingFromBase(baseSpc,spc,builtinSortOp) in
    let xSpc = transformSpecForFirstOrderProverInt spc in
(*
    if proverUseBase?
      then let _ = writeLine("Including the Base Spec") in 
	    xSpc
    else
*)
      let xBaseSpec = transformSpecForFirstOrderProverInt baseSpc in
      %let xBaseSpec = basespc in
      %let res = subtractSpec xspc xBaseSpec in
      let res = subtractSpecProperties(xSpc, xBaseSpec) in
      res

  op transformSpecForFirstOrderProverInt: AnnSpec.Spec -> AnnSpec.Spec
  def transformSpecForFirstOrderProverInt spc =
    %let _ = writeLine("orig") in
    %let _ = writeLine(printSpec spc) in
    let spc = unfoldSortAliases spc in
    let spc = removeCurrying spc in
    %let _ = writeLine("remCur") in
    %let _ = writeLine(printSpec spc) in
    let spc = removeQuotient spc in
    %let _ = writeLine("remQ") in
    %let _ = writeLine(printSpec spc) in
    %let spc = instantiateHOFns spc in
    %let _ = writeLine("instHO") in
    %let _ = writeLine(printSpec spc) in
    %let spc = lambdaToInner spc in
    let spc = poly2monoForSnark(spc,true) in
    %let _ = writeLine("remPoly") in
    %let _ = writeLine(printSpec spc) in
    %let spc = addEqOpsToSpec spc in
    %let _ = printSpecWithSortsToTerminal spc in
    let spc = lambdaLift spc in
    %let _ = writeLine("lambdaLift") in
    %let _ = writeLine(printSpec spc) in
    %let spc = foldRecordSorts(spc) in
    let (spc,constrOps) = addSortConstructorsToSpecForSnark spc in
    let (spc,constrOps) = addProductSortConstructorsToSpec spc in
    let (spc,constrOps) = addProductAccessorsToSpec spc in
    %let _ = writeLine("ConsAccAdds") in
    %let _ = writeLine(printSpec spc) in
    %let spc = conformOpDecls spc in
    %let spc = adjustAppl spc in
    let spc = instantiateHOFns spc in
    %let spc = simpSpecFMTerm spc in
    %let _ = writeLine("snd InsHO") in
    %let _ = writeLine(printSpec spc) in
    let spc = explicateHiddenAxioms(spc) in
    %let _ = writeLine(printSpec spc) in
    spc

  op getBaseProverSpec : Env Spec
  def getBaseProverSpec = 
    {
     (optBaseUnitId,baseSpec) <- getBase;
     proverBaseUnitId <- pathToRelativeUID "/Library/ProverBase/Top";
     (Spec baseProverSpec,_,_) <- SpecCalc.evaluateUID (Internal "ProverBase") proverBaseUnitId;
     return baseProverSpec % 
     %return (subtractSpecProperties(baseProverSpec, baseSpec)) %baseProverSpec % 
    }

  op getRewriteProverSpec : Env Spec
  def getRewriteProverSpec = 
    {
     (optBaseUnitId,baseSpec) <- getBase;
     proverRewriteUnitId <- pathToRelativeUID "/Library/Base/ProverRewrite";
     (Spec rewriteProverSpec,_,_) <- SpecCalc.evaluateUID (Internal "ProverRewrite") proverRewriteUnitId;
     return (subtractSpecProperties(rewriteProverSpec, baseSpec))
    }

 def proverOptionsFromSpec (name, spc, specName) = {
   possibleOptionsOp <- return(AnnSpec.findTheOp (spc, name));
   optionsDef <-
      (case possibleOptionsOp of
	 | Some info ->
	   if definedOpInfo? info then
	     let opTerm = firstOpDefInnerTerm info in
	     return opTerm
	   else
	     raise (SyntaxError ("Cannot find prover option definition, " ^ printQualifiedId name ^
				 (case specName of
				    | Some specName -> ", in Spec, " ^ specName ^ "."
				    | _ -> ".")))
	 | _ -> raise (SyntaxError ("Cannot find prover option definition, " ^ printQualifiedId name ^
				    (case specName of
				       | Some specName -> ", in Spec, " ^ specName ^ "."
				       | _ -> "."))));
   optionsString <-
      (case optionsDef of
	 | Fun (String (opString),_,_) -> return (opString)
	 | _ -> raise (SyntaxError ("Prover option definition, " ^ printQualifiedId(name) ^ 
		                    ", is not a string.")));
   possibleOptions <- return(PARSER4.READ_LIST_OF_S_EXPRESSIONS_FROM_STRING(optionsString));
   proverOptions <- (case possibleOptions of
	  | OptionString (proverOptions) -> return (proverOptions)
	  | Error   (msg, str)     -> raise  (SyntaxError (msg ^ str)));
   return proverOptions
  }

 op UIDtoLogFile: UnitId * String * String -> SpecCalc.Env String
 def UIDtoLogFile (unitId as {path,hashSuffix}, proverName, suffix) = {
   result <-
   case hashSuffix of
     | None -> UIDtoSingleLogFile(unitId, proverName, suffix)
     | Some _ -> UIDtoMultipleLogFile(unitId, proverName, suffix);
   return result
 }

 op UIDtoSingleLogFile: UnitId * String * String -> SpecCalc.Env String
 def UIDtoSingleLogFile (unitId as {path,hashSuffix}, proverName, suffix) =
    {prefix <- removeLastElem path;
     mainName <- lastElem path;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/"^proverName^"/" ^ mainName ^ "." ^ suffix
     in
      return filNm}

 op UIDtoMultipleLogFile: UnitId * String * String -> SpecCalc.Env String
 def UIDtoMultipleLogFile (unitId as {path,hashSuffix}, proverName, suffix) =
   let Some hashSuffix = hashSuffix in
    {prefix <- removeLastElem path;
     newSubDir <- lastElem path;
     mainName <- return hashSuffix;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/"^proverName^"/" ^ newSubDir ^ "/" ^ mainName ^ "." ^ suffix
     in
      return filNm}

 op UIDtoProofName: UnitId -> Option String
 def UIDtoProofName (unitId as {path,hashSuffix}) =
    hashSuffix

 op SpecTermToSpecName: SCTerm -> (Option String)
 def SpecTermToSpecName (scterm as (term,_)) =
   case term of
     | UnitId rUID -> Some (showRelativeUID(rUID))
     | Spec _ -> None
     | _ -> None

 op claimNameMatch: ClaimName * ClaimName -> Boolean
 def claimNameMatch(cn, pn) =
   let Qualified(cq, cid) = cn in
   let Qualified(pq, pid) = pn in
   if cq = UnQualified
     then pid = cid
   else cq = pq & cid = pid

 op proveInSpec: Option String * ClaimName * Spec * Option String * Spec * Spec * String * 
                 Assertions * List LispCell * Boolean * AnswerVar * String * Position -> SpecCalc.Env Boolean
 def proveInSpec (proofName, claimName, spc, specName, baseSpc, rewriteSpc, proverName,
		  assertions, proverOptions, includeBase, answerVariable, proverLogFileName, pos) = {
   result <-
   let baseHypothesis = allProperties baseSpc in
   let rewriteHypothesis = allProperties rewriteSpc in
   let _ = debug("pinspec") in
   let findClaimInSpec = firstUpTo (fn (_, propertyName, _, _) -> claimNameMatch(claimName, propertyName))
                                   (allProperties spc) in
   case findClaimInSpec of
     | None -> raise (Proof (pos, "Claim name is not in spec."))
     | Some (claim, validHypothesis) ->
	 let actualHypothesis = actualHypothesis(validHypothesis, assertions, pos) in
	 let missingHypothesis = missingHypothesis(actualHypothesis, assertions) in
	   case missingHypothesis of 
		 | [] -> return (proveWithHypothesis(proofName, claim, actualHypothesis, spc, specName, baseHypothesis, baseSpc,
						     rewriteHypothesis, rewriteSpc,
						     proverName, proverOptions, includeBase, answerVariable, proverLogFileName))
		 | _ -> raise (Proof (pos, "assertions: "^printMissingHypothesis(missingHypothesis)^" not in spec.\n
				      Asserions in spec: "^printMissingHypothesis(map (fn((_,pn,_,_)) -> pn)actualHypothesis)));
   return result}

 op actualHypothesis: List Property * Assertions * Position -> List Property

 def actualHypothesis (validHypothesis, assertions, _ (* pos *)) =
     case assertions of
      | All -> validHypothesis
      | Explicit possibilities -> 
         let hypothesis = filter (fn (_, propertyName, _, _) -> member(propertyName, (possibilities))) validHypothesis in
	   hypothesis

 op missingHypothesis: List Property * Assertions -> List ClaimName

 def missingHypothesis (actualHypothesis, assertions) =
     case assertions of
      | All -> []
      | Explicit possibilities -> 
         let missingHypothesis = filter (fn (claimName:ClaimName) -> ~(exists(fn (_, propName:ClaimName,_,_) -> claimNameMatch(claimName, propName)) actualHypothesis)) possibilities in
	   missingHypothesis

 op printMissingHypothesis: List ClaimName -> String
 def printMissingHypothesis(cns) =
   case cns of
     | []  -> ""
     | [p] -> printQualifiedId(p)
     | p :: ps -> printQualifiedId(p)^", "^printMissingHypothesis(ps)

 op displayProofResult: String * (Option String) * String * ClaimName * (Option String) * Boolean -> Boolean
 def displayProofResult(proverName, proofName, claimType, claimName, specName, proved) =
   let _ =
   case proofName of
     | None -> 
         (case specName of
	   | None -> displaySingleAnonymousProofResult(proverName, claimType, claimName, proved)
	   | Some specName -> displaySingleProofResult(proverName, claimType, claimName, specName, proved))
     | Some proofName ->
	 case specName of
	   | None -> displayMultipleAnonymousProofResult(proverName, proofName, claimType, claimName, proved)
	   | Some specName -> 
	       displayMultipleProofResult(proverName, proofName, claimType, claimName, specName, proved) in
     proved


  def displaySingleAnonymousProofResult(proverName, claimType, claimName, proved) =
    let provedString = provedString(proved) in
    let proverString = proverString(proverName) in
    let _ = writeLine(claimType^" "^printQualifiedId(claimName)^" "^provedString^" "^proverString) in
      proved

  def displaySingleProofResult(proverName, claimType, claimName, specName, proved) =
    let provedString = provedString(proved) in
    let proverString = proverString(proverName) in
    let _ = writeLine(claimType^" "^printQualifiedId(claimName)^" in "^specName^" "^provedString^" "^proverString) in
      proved

  def displayMultipleAnonymousProofResult(proverName, proofName, claimType, claimName, proved) =
    let provedString = provedString(proved) in
    let proverString = proverString(proverName) in
    let _ = writeLine(proofName^": "^claimType^" "^printQualifiedId(claimName)^" "^provedString^" "^proverString) in
      proved

  def displayMultipleProofResult(proverName, proofName, claimType, claimName, specName, proved) =
    let provedString = if proved then "is Proved!" else "is NOT proved" in
    let proverString = proverString(proverName) in
    let _ = writeLine(proofName^": "^claimType^" "^printQualifiedId(claimName)^" in "^specName^" "^provedString^" "^proverString) in
      proved

 op provedString: Boolean -> String
 def provedString(proved) =
   if proved
     then "is Proved!"
   else "is NOT proved."

 op proverString: String -> String
 def proverString(proverName) =
   case proverName of
     | "FourierM" -> "using simple inequality reasoning."
     | "Snark" -> "using Snark."

 op proveWithHypothesis: Option String * Property * List Property * Spec * Option String * List Property * Spec *
                         List Property * Spec *
                         String * List LispCell * Boolean * AnswerVar * String -> Boolean

 def proveWithHypothesis(proofName, claim, hypothesis, spc, specName, baseHypothesis, baseSpc,
			 rewriteHypothesis, rewriteSpc,
			 proverName, proverOptions, includeBase, answerVariable, snarkLogFileName) =
   if proverName = "FourierM"
     then 
       proveWithHypothesisFM(proofName, claim, spc, specName, proverName, false)
   else
     if proverName = "Snark"
       then proveWithHypothesisSnark(proofName, claim, hypothesis, spc, specName, baseHypothesis, baseSpc,
				     rewriteHypothesis, rewriteSpc,
				     proverName, proverOptions, includeBase, answerVariable, snarkLogFileName)
     else
       let fmRes = proveWithHypothesisFM(proofName, claim, spc, specName, "FourierM", true) in
       fmRes ||
       proveWithHypothesisSnark(proofName, claim, hypothesis, spc, specName, baseHypothesis, baseSpc,
				rewriteHypothesis, rewriteSpc,
				"Snark", proverOptions, includeBase, answerVariable, snarkLogFileName)


 op proveWithHypothesisSnark: Option String * Property * List Property * Spec * Option String * List Property * Spec *
                         List Property * Spec *
                         String * List LispCell * Boolean * AnswerVar * String -> Boolean

 def proveWithHypothesisSnark(proofName, claim, hypothesis, spc, specName, baseHypothesis, baseSpc,
			      rewriteHypothesis, rewriteSpc,
			      proverName, proverOptions, includeBase, answerVariable, snarkLogFileName) =
   let _ = debug("preovWithHyp") in
   let _ = if ~(proverName = "Snark") then writeLine(proverName ^ " is not supported; using Snark instead.") else () in
   let (claimType,claimName,_,_) = claim in
   let def getClaimType(ct) = 
         case ct of
	   | Conjecture -> "Conjecture" 
	   | Theorem -> "Theorem" 
	   | Axiom -> "Axiom" in
   let claimType = getClaimType(claimType) in
   let snarkSortDecls = snarkSorts(spc) in
   let snarkOpDecls = snarkOpDecls(spc) in
   let context = newContext in
   let snarkBaseHypothesis = if includeBase
			       then  map (fn (prop) -> snarkProperty(context, baseSpc, prop))
				     baseHypothesis
			     else [] in
   let snarkRewriteHypothesis = map (fn (prop) -> snarkRewrite(context, rewriteSpc, prop))
                                     rewriteHypothesis in
   %let snarkHypothesis = map (fn (prop) -> snarkProperty(context, spc, prop)) hypothesis in
   let snarkSubsortHypothesis = snarkSubsortProperties(context, spc) in
   let snarkPropertyHypothesis = foldr (fn (prop, list) -> snarkPropertiesFromProperty(context, spc, prop)++list) [] hypothesis in
   let snarkHypothesis = snarkSubsortHypothesis ++ snarkPropertyHypothesis in
   let snarkConjecture =
     case answerVariable of
       | None -> snarkConjectureRemovePattern(context, spc, claim)
       | Some var -> snarkAnswer(context, spc, claim, [var]) in
   let snarkEvalForm = makeSnarkProveEvalForm(proverOptions, snarkSortDecls, snarkOpDecls, snarkBaseHypothesis, snarkRewriteHypothesis,
					      snarkHypothesis, snarkConjecture, snarkLogFileName) in
     let _ = if specwareDebug? then writeLine("Calling Snark by evaluating: ") else () in
     let _ = if specwareDebug? then LISP.PPRINT(snarkEvalForm) else Lisp.list [] in
     let result = Lisp.apply(Lisp.symbol("CL","FUNCALL"),
			     [Lisp.eval(Lisp.list [Lisp.symbol("CL","FUNCTION"),
						   Lisp.list [Lisp.symbol("SNARK","LAMBDA"),
							      Lisp.nil(),snarkEvalForm]])]) in
     let proved = ":PROOF-FOUND" = anyToString(result) in
     let _ = displayProofResult(proverName, proofName, claimType, claimName, specName, proved) in
       proved

 op proveWithHypothesisFM: Option String * Property * Spec * Option String * String * Boolean -> Boolean

 def proveWithHypothesisFM(proofName, claim, spc, specName, proverName, preProof?) =
   let _ = debug("preovWithHyp") in
   let (claimType,claimName,_,_) = claim in
   let def getClaimType(ct) = 
         case ct of
	   | Conjecture -> "Conjecture" 
	   | Theorem -> "Theorem" 
	   | Axiom -> "Axiom" in
   let claimType = getClaimType(claimType) in
   let context = emptyToFMContext in
   %let fmSubsortHypothesis = fmSubsortProperties(context, spc) in
   %let fmSubsortHypothesis = [] in
   %let fmPropertyHypothesis = foldr (fn (prop, list) -> [toFMProperty(context, spc, prop)]++list) [] hypothesis in
   %let fmHypothesis = fmSubsortHypothesis ++ fmPropertyHypothesis in
   %let fmConjecture = toFMProperty(context, spc, claim) in
   let proved = proveMSProb(spc, [], claim) in
   let _ = if proved || ~preProof?
	     then displayProofResult(proverName, proofName, claimType, claimName, specName, proved)
	   else proved in
   proved

 %print-clocks??
 op makeSnarkProveDecls: List LispCell * List LispCell * List LispCell * List LispCell * List LispCell
                           * List LispCell * LispCell -> LispCell

 def makeSnarkProveDecls(proverOptions, snarkSortDecl, snarkOpDecls, snarkBaseHypothesis, snarkRewriteHypothesis,
			 snarkHypothesis, snarkConjecture) =
   let setOfSupportOn = Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(false)]) in
   let setOfSupportOff = Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(true)]) in
   
   Lisp.list
   [Lisp.list([Lisp.symbol("SNARK","INITIALIZE")]),
    Lisp.list([Lisp.symbol("SNARK","RUN-TIME-LIMIT"), Lisp.nat(20)]),
    Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(false)]),
    Lisp.list([Lisp.symbol("SNARK","USE-LISP-TYPES-AS-SORTS"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-CODE-FOR-NUMBERS"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-NUMBERS-AS-CONSTRUCTORS"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-RESOLUTION"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-CONDITIONAL-ANSWER-CREATION"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-WELL-SORTING"), Lisp.bool(false)])]
   Lisp.++ (Lisp.list snarkSortDecl)
   Lisp.++ (Lisp.list snarkOpDecls)
   Lisp.++ (Lisp.list proverOptions)
   Lisp.++ (Lisp.list [setOfSupportOn])
   Lisp.++ (Lisp.list snarkBaseHypothesis)
   Lisp.++ (Lisp.list snarkRewriteHypothesis)
   Lisp.++ (Lisp.list [setOfSupportOff])
   Lisp.++ (Lisp.list proverOptions)
   Lisp.++ (Lisp.list baseAxioms)
   Lisp.++ (Lisp.list snarkHypothesis)
   Lisp.++ (Lisp.list [snarkConjecture])

 op makeSnarkProveEvalForm: List LispCell * List LispCell * List LispCell * List LispCell * List LispCell
                           * List LispCell * LispCell * String -> LispCell

 def makeSnarkProveEvalForm(proverOptions, snarkSortDecl, snarkOpDecls, snarkBaseHypothesis, snarkRewriteHypothesis,
			    snarkHypothesis, snarkConjecture, snarkLogFileName) =
   %let _ = if specwareDebug? then toScreen("Proving snark fmla: ") else () in
   %let _ = if specwareDebug? then LISP.PPRINT(snarkConjecture) else Lisp.list [] in
   %let _ = if specwareDebug? then writeLine(" using: ") else () in
   %let _ = if specwareDebug? then LISP.PPRINT(Lisp.list(snarkHypothesis)) else Lisp.list [] in
   let snarkProverDecls = makeSnarkProveDecls(proverOptions, snarkSortDecl, snarkOpDecls, snarkBaseHypothesis, snarkRewriteHypothesis,
					      snarkHypothesis, snarkConjecture) in
   	 Lisp.list 
	 [Lisp.symbol("CL-USER","WITH-OPEN-FILE"),
	  Lisp.list [Lisp.symbol("CL-USER","LOGFILE"),
		     Lisp.string(snarkLogFileName),
		     Lisp.symbol("KEYWORD","DIRECTION"),
		     Lisp.symbol("KEYWORD","OUTPUT"),
		     Lisp.symbol("KEYWORD","IF-EXISTS"),
		     Lisp.symbol("KEYWORD","SUPERSEDE")],
	  Lisp.list
	  [
	   Lisp.symbol("CL","LET"),
	   Lisp.list [Lisp.list [Lisp.symbol("CL-USER","*ERROR-OUTPUT*"),
				 Lisp.symbol("CL-USER","LOGFILE")],
		      Lisp.list [Lisp.symbol("CL-USER","*STANDARD-OUTPUT*"),
				 Lisp.symbol("CL-USER","LOGFILE")],
		      Lisp.list [Lisp.symbol("CL-USER","*PRINT-LEVEL*"),
				 Lisp.symbol("CL-USER","NIL")],
		      Lisp.list [Lisp.symbol("CL-USER","*PRINT-LENGTH*"),
				 Lisp.symbol("CL-USER","NIL")]],
	   Lisp.list([Lisp.symbol("CL","WRITE-LINE"), Lisp.string("Snark is invoked by evaluating:")]),
	   Lisp.list([Lisp.symbol("CL","PPRINT"),
		      Lisp.quote(Lisp.list[Lisp.symbol("CL","LET"), Lisp.list []] Lisp.++ snarkProverDecls)])
	  ]
	  Lisp.++ snarkProverDecls
		    ]

}
