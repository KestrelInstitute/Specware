SpecCalc qualifying spec {
  import UnitId
  import SpecUnion
  import /Languages/Snark/SpecToSnark
  import /Provers/DP/ToFourierMotzkin
  import /Languages/MetaSlang/Transformations/ExplicateHiddenAxioms
  import /Languages/MetaSlang/CodeGen/CodeGenTransforms
  import UnitId/Utilities                                    % for uidToString, if used...

 op PARSER4.READ_LIST_OF_S_EXPRESSIONS_FROM_STRING: String -> ProverOptions

 %op explicateHiddenAxioms:AnnSpec.Spec -> AnnSpec.Spec
  
 def SpecCalc.evaluateProve (claim_name, spec_term, prover_name, assertions, possible_options, answer_var) pos = {
     unitId <- getCurrentUnitId;
     print (";;; Elaborating proof-term at " ^ (uidToString unitId) ^ "\n");
     (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo spec_term;
     (optBaseUnitId,baseSpec) <- getBase;
     baseProverSpec <- getBaseProverSpec;
     rewriteProverSpec <- getRewriteProverSpec;
     %proverBaseUnitId <- pathToRelativeUID "/Library/Base/ProverBase";
     %(Spec baseProverSpec,_,_) <- SpecCalc.evaluateUID (Internal "ProverBase") proverBaseUnitId;
     proverLogFileName <- UIDtoLogFile(unitId, if prover_name = "Both" then "Snark" else prover_name);
     _ <- return (ensureDirectoriesExist proverLogFileName);
     proof_name <- return (UIDtoProofName unitId);
     spec_name <- return (SpecTermToSpecName(spec_term));
     uspc <- (
	     case coerceToSpec value of
	       | Spec spc -> return spc %specUnion([spc, baseProverSpec])
               | _ -> raise (Proof (pos, "Argument to prove command is not coerceable to a spec.")));
     subSpec <- return(subtractSpec uspc baseSpec);
     %subSpec <- return (subtractSpecProperties(uspc, baseSpec));
     %noHOSpec <- return(subtractSpecProperties(instantiateHOFns(uspc), baseSpec));
     %liftedNoHOSpec <- return(subtractSpecProperties(lambdaLift(noHOSpec), baseSpec));
     %liftedNoHOSpec <- return(lambdaLift(noHOSpec));
     %expandedSpec:Spec <- return(explicateHiddenAxioms(liftedNoHOSpec));
     %expandedSpec <- return (transformSpecForFirstOrderProver baseSpec subSpec);
     expandedSpec <- return (transformSpecForFirstOrderProver baseSpec uspc);
     %_ <- return (if specwareDebug? then writeString(printSpec(liftedNoHOSpec)) else ());
     %expandedSpec:Spec <- return(explicateHiddenAxioms(liftedNoHOSpec));
     %expandedSpec:Spec <- return(explicateHiddenAxioms(uspc));
     _ <- return (if specwareDebug? then writeString(printSpec(expandedSpec)) else ());
     %expandedSpec:Spec <- return(explicateHiddenAxioms(noHOSpec));
     %expandedSpec:Spec <- return(uspc);
     prover_options <- 
       (case possible_options of
	  | OptionString prover_options -> return (prover_options)
	  | OptionName prover_option_name -> 
	        proverOptionsFromSpec(prover_option_name, uspc, spec_name)
	  | Error   (msg, str)     -> raise  (SyntaxError (msg ^ str)));
     proved:Boolean <- (proveInSpec (proof_name,
				     claim_name, 
				     %subtractSpecProperties(expandedSpec, baseSpec),
				     expandedSpec,
				     spec_name,
				     baseProverSpec,
				     rewriteProverSpec,
				     prover_name, 
				     assertions, 
				     prover_options,
				     answer_var,
				     proverLogFileName,
				     pos));
     result <- return (Proof {status = if proved then Proved else Unproved, 
			      unit   = unitId});
     return (result, timeStamp, depUIDs)
   }


  op transformSpecForFirstOrderProver: AnnSpec.Spec -> AnnSpec.Spec -> AnnSpec.Spec
  def transformSpecForFirstOrderProver basespc spc =
    let spc = addMissingFromBase(basespc,spc,builtinSortOp) in
    let xspc = transformSpecForFirstOrderProverInt spc in
%    if proverUseBase? then let _ = writeLine("PRB") in xspc else
      let xBaseSpec = transformSpecForFirstOrderProverInt basespc in
      %let xBaseSpec = basespc in
      %let res = subtractSpec xspc xBaseSpec in
      let res = subtractSpecProperties(xspc, xBaseSpec) in
      res
    

  op transformSpecForFirstOrderProverInt: AnnSpec.Spec -> AnnSpec.Spec
  def transformSpecForFirstOrderProverInt spc =
    %let _ = writeLine("orig") in
    %let _ = writeLine(printSpec spc) in
    let spc = unfoldSortAliases spc in
    let spc = removeCurrying spc in
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
     return baseProverSpec % (subtractSpec baseProverSpec baseSpec)
    }

  op getRewriteProverSpec : Env Spec
  def getRewriteProverSpec = 
    {
     (optBaseUnitId,baseSpec) <- getBase;
     proverRewriteUnitId <- pathToRelativeUID "/Library/Base/ProverRewrite";
     (Spec rewriteProverSpec,_,_) <- SpecCalc.evaluateUID (Internal "ProverRewrite") proverRewriteUnitId;
     return (subtractSpec rewriteProverSpec baseSpec)
    }

 def proverOptionsFromSpec (name, spc, spec_name) = {
   possible_options_op <- return(AnnSpec.findTheOp (spc, name));
   options_def <-
      (case possible_options_op of
	 | Some info ->
	   if definedOpInfo? info then
	     let opTerm = firstOpDefInnerTerm info in
	     return opTerm
	   else
	     raise (SyntaxError ("Cannot find prover option definition, " ^ printQualifiedId name ^
				 (case spec_name of
				    | Some spec_name -> ", in Spec, " ^ spec_name ^ "."
				    | _ -> ".")))
	 | _ -> raise (SyntaxError ("Cannot find prover option definition, " ^ printQualifiedId name ^
				    (case spec_name of
				       | Some spec_name -> ", in Spec, " ^ spec_name ^ "."
				       | _ -> "."))));
   options_string <-
      (case options_def of
	 | Fun (String (opString),_,_) -> return (opString)
	 | _ -> raise (SyntaxError ("Prover option definition, " ^ printQualifiedId(name) ^ 
		                    ", is not a string.")));
   possible_options <- return(PARSER4.READ_LIST_OF_S_EXPRESSIONS_FROM_STRING(options_string));
   prover_options <- (case possible_options of
	  | OptionString (prover_options) -> return (prover_options)
	  | Error   (msg, str)     -> raise  (SyntaxError (msg ^ str)));
   return prover_options
  }

 op UIDtoLogFile: UnitId * String -> SpecCalc.Env String
 def UIDtoLogFile (unitId as {path,hashSuffix}, proverName) = {
   result <-
   case hashSuffix of
     | None -> UIDtoSingleLogFile(unitId, proverName)
     | Some _ -> UIDtoMultipleLogFile(unitId, proverName);
   return result
 }

 op UIDtoSingleLogFile: UnitId * String -> SpecCalc.Env String
 def UIDtoSingleLogFile (unitId as {path,hashSuffix}, proverName) =
    {prefix <- removeLastElem path;
     mainName <- lastElem path;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/"^proverName^"/" ^ mainName ^ ".log"
     in
      return filNm}

 op UIDtoMultipleLogFile: UnitId * String -> SpecCalc.Env String
 def UIDtoMultipleLogFile (unitId as {path,hashSuffix}, proverName) =
   let Some hashSuffix = hashSuffix in
    {prefix <- removeLastElem path;
     newSubDir <- lastElem path;
     mainName <- return hashSuffix;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/"^proverName^"/" ^ newSubDir ^ "/" ^ mainName ^ ".log"
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
                 Assertions * List LispCell * AnswerVar * String * Position -> SpecCalc.Env Boolean
 def proveInSpec (proof_name, claim_name, spc, spec_name, base_spc, rewrite_spc, prover_name,
		  assertions, prover_options, answer_var, proverLogFileName, pos) = {
   result <-
   let baseHypothesis = base_spc.properties in
   let rewriteHypothesis = rewrite_spc.properties in
   let _ = debug("pinspec") in
   let findClaimInSpec = firstUpTo (fn (_, propertyName, _, _) -> claimNameMatch(claim_name, propertyName))
                                   spc.properties in
   case findClaimInSpec of
     | None -> raise (Proof (pos, "Claim name is not in spec."))
     | Some (claim, validHypothesis) ->
	 let actualHypothesis = actualHypothesis(validHypothesis, assertions, pos) in
	 let missingHypothesis = missingHypothesis(actualHypothesis, assertions) in
	   case missingHypothesis of 
		 | [] -> return (proveWithHypothesis(proof_name, claim, actualHypothesis, spc, spec_name, baseHypothesis, base_spc,
						     rewriteHypothesis, rewrite_spc,
						     prover_name, prover_options, answer_var, proverLogFileName))
		 | _ -> raise (Proof (pos, "assertions: "^printMissingHypothesis(missingHypothesis)^" not in spec."));
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
   foldl (fn (cn, s) -> printQualifiedId(cn)^s) "" cns

 op displayProofResult: String * (Option String) * String * ClaimName * (Option String) * Boolean * String -> Boolean
 def displayProofResult(prover_name, proof_name, claim_type, claim_name, spec_name, proved, proverLogFileName) =
   let _ =
   case proof_name of
     | None -> 
         (case spec_name of
	   | None -> displaySingleAnonymousProofResult(prover_name, claim_type, claim_name, proved)
	   | Some spec_name -> displaySingleProofResult(prover_name, claim_type, claim_name, spec_name, proved))
     | Some proof_name ->
	 case spec_name of
	   | None -> displayMultipleAnonymousProofResult(prover_name, proof_name, claim_type, claim_name, proved)
	   | Some spec_name -> 
	       displayMultipleProofResult(prover_name, proof_name, claim_type, claim_name, spec_name, proved) in
   let _ = writeLine("    Snark Log file: " ^ proverLogFileName) in
     proved


  def displaySingleAnonymousProofResult(prover_name, claim_type, claim_name, proved) =
    let provedString = provedString(proved) in
    let proverString = proverString(prover_name) in
    let _ = writeLine(claim_type^" "^printQualifiedId(claim_name)^" "^provedString^" "^proverString) in
      proved

  def displaySingleProofResult(prover_name, claim_type, claim_name, spec_name, proved) =
    let provedString = provedString(proved) in
    let proverString = proverString(prover_name) in
    let _ = writeLine(claim_type^" "^printQualifiedId(claim_name)^" in "^spec_name^" "^provedString^" "^proverString) in
      proved

  def displayMultipleAnonymousProofResult(prover_name, proof_name, claim_type, claim_name, proved) =
    let provedString = provedString(proved) in
    let proverString = proverString(prover_name) in
    let _ = writeLine(proof_name^": "^claim_type^" "^printQualifiedId(claim_name)^" "^provedString^" "^proverString) in
      proved

  def displayMultipleProofResult(prover_name, proof_name, claim_type, claim_name, spec_name, proved) =
    let provedString = if proved then "is Proved!" else "is NOT proved" in
    let proverString = proverString(prover_name) in
    let _ = writeLine(proof_name^": "^claim_type^" "^printQualifiedId(claim_name)^" in "^spec_name^" "^provedString^" "^proverString) in
      proved

 op provedString: Boolean -> String
 def provedString(proved) =
   if proved
     then "is Proved!"
   else "is NOT proved."

 op proverString: String -> String
 def proverString(prover_name) =
   case prover_name of
     | "FourierM" -> "using simple inequality reasoning."
     | "Snark" -> "using Snark."

 op proveWithHypothesis: Option String * Property * List Property * Spec * Option String * List Property * Spec *
                         List Property * Spec *
                         String * List LispCell * AnswerVar * String -> Boolean

 def proveWithHypothesis(proof_name, claim, hypothesis, spc, spec_name, base_hypothesis, base_spc,
			 rewrite_hypothesis, rewrite_spc,
			 prover_name, prover_options, answer_var, snarkLogFileName) =
   if prover_name = "FourierM"
     then 
       proveWithHypothesisFM(proof_name, claim, hypothesis, spc, spec_name, base_hypothesis, base_spc,
			     rewrite_hypothesis, rewrite_spc,
			     prover_name, prover_options, snarkLogFileName, false)
   else
     if prover_name = "Snark"
       then proveWithHypothesisSnark(proof_name, claim, hypothesis, spc, spec_name, base_hypothesis, base_spc,
				     rewrite_hypothesis, rewrite_spc,
				     prover_name, prover_options, answer_var, snarkLogFileName)
     else
       let fmRes = proveWithHypothesisFM(proof_name, claim, hypothesis, spc, spec_name, base_hypothesis, base_spc,
					 rewrite_hypothesis, rewrite_spc,
					 "FourierM", prover_options, snarkLogFileName, true) in
       fmRes ||
       proveWithHypothesisSnark(proof_name, claim, hypothesis, spc, spec_name, base_hypothesis, base_spc,
				rewrite_hypothesis, rewrite_spc,
				"Snark", prover_options, answer_var, snarkLogFileName)


 op proveWithHypothesisSnark: Option String * Property * List Property * Spec * Option String * List Property * Spec *
                         List Property * Spec *
                         String * List LispCell * AnswerVar * String -> Boolean

 def proveWithHypothesisSnark(proof_name, claim, hypothesis, spc, spec_name, base_hypothesis, base_spc,
			 rewrite_hypothesis, rewrite_spc,
			 prover_name, prover_options, answer_var, snarkLogFileName) =
   let _ = debug("preovWithHyp") in
   let _ = if ~(prover_name = "Snark") then writeLine(prover_name ^ " is not supported; using Snark instead.") else () in
   let (claim_type,claim_name,_,_) = claim in
   let def claimType(ct) = 
         case ct of
	   | Conjecture -> "Conjecture" 
	   | Theorem -> "Theorem" 
	   | Axiom -> "Axiom" in
   let claim_type = claimType(claim_type) in
   let snarkSortDecls = snarkSorts(spc) in
   let snarkOpDecls = snarkOpDecls(spc) in
   let context = newContext in
   let snarkBaseHypothesis = 
     if proverUseBase?
       then map (fn (prop) -> snarkProperty(context, base_spc, prop)) base_hypothesis
     else [] in
   let snarkRewriteHypothesis = map (fn (prop) -> snarkRewrite(context, rewrite_spc, prop))
                                     rewrite_hypothesis in
   %let snarkHypothesis = map (fn (prop) -> snarkProperty(context, spc, prop)) hypothesis in
   let snarkSubsortHypothesis = snarkSubsortProperties(context, spc) in
   let snarkPropertyHypothesis = foldr (fn (prop, list) -> snarkPropertiesFromProperty(context, spc, prop)++list) [] hypothesis in
   let snarkHypothesis = snarkSubsortHypothesis ++ snarkPropertyHypothesis in
   let snarkConjecture =
     case answer_var of
       | None -> snarkConjectureRemovePattern(context, spc, claim)
       | Some var -> snarkAnswer(context, spc, claim, [var]) in
   let snarkEvalForm = makeSnarkProveEvalForm(prover_options, snarkSortDecls, snarkOpDecls, snarkBaseHypothesis, snarkRewriteHypothesis,
					      snarkHypothesis, snarkConjecture, snarkLogFileName) in
     let _ = if specwareDebug? then writeLine("Calling Snark by evaluating: ") else () in
     let _ = if specwareDebug? then LISP.PPRINT(snarkEvalForm) else Lisp.list [] in
     let result = Lisp.apply(Lisp.symbol("CL","FUNCALL"),
			     [Lisp.eval(Lisp.list [Lisp.symbol("CL","FUNCTION"),
						   Lisp.list [Lisp.symbol("SNARK","LAMBDA"),
							      Lisp.nil(),snarkEvalForm]])]) in
     let proved = ":PROOF-FOUND" = anyToString(result) in
     let _ = displayProofResult(prover_name, proof_name, claim_type, claim_name, spec_name, proved, snarkLogFileName) in
       proved

 op proveWithHypothesisFM: Option String * Property * List Property * Spec * Option String * List Property * Spec *
                         List Property * Spec *
                         String * List LispCell * String * Boolean -> Boolean

 def proveWithHypothesisFM(proof_name, claim, hypothesis, spc, spec_name, base_hypothesis, base_spc,
			 rewrite_hypothesis, rewrite_spc,
			 prover_name, prover_options, logFileName, preProof?) =
   let _ = debug("preovWithHyp") in
   let (claim_type,claim_name,_,_) = claim in
   let def claimType(ct) = 
         case ct of
	   | Conjecture -> "Conjecture" 
	   | Theorem -> "Theorem" 
	   | Axiom -> "Axiom" in
   let claim_type = claimType(claim_type) in
   let context = emptyToFMContext in
   %let fmSubsortHypothesis = fmSubsortProperties(context, spc) in
   %let fmSubsortHypothesis = [] in
   %let fmPropertyHypothesis = foldr (fn (prop, list) -> [toFMProperty(context, spc, prop)]++list) [] hypothesis in
   %let fmHypothesis = fmSubsortHypothesis ++ fmPropertyHypothesis in
   %let fmConjecture = toFMProperty(context, spc, claim) in
   let proved = proveMSProb(spc, [], claim) in
   let _ = if proved || ~preProof?
	     then displayProofResult(prover_name, proof_name, claim_type, claim_name, spec_name, proved, logFileName)
	   else proved in
   proved

 %print-clocks??

 op makeSnarkProveDecls: List LispCell * List LispCell * List LispCell * List LispCell * List LispCell
                           * List LispCell * LispCell * String -> LispCell

 def makeSnarkProveDecls(prover_options, snarkSortDecl, snarkOpDecls, snarkBaseHypothesis, snarkRewriteHypothesis,
			 snarkHypothesis, snarkConjecture, snarkLogFileName) =
   let setOfSupportOn = Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(false)]) in
   let setOfSupportOff = Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(true)]) in
   
   Lisp.list
   [Lisp.list([Lisp.symbol("SNARK","INITIALIZE")]),
    Lisp.list([Lisp.symbol("SNARK","RUN-TIME-LIMIT"), Lisp.nat(20)]),
    Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(false)]),
    Lisp.list([Lisp.symbol("SNARK","USE-LISP-TYPES-AS-SORTS"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-CODE-FOR-NUMBERS"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-CODE-FOR-NUMBERS"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-NUMBERS-AS-CONSTRUCTORS"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-RESOLUTION"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-CONDITIONAL-ANSWER-CREATION"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-WELL-SORTING"), Lisp.bool(false)])]
   Lisp.++ (Lisp.list snarkSortDecl)
   Lisp.++ (Lisp.list snarkOpDecls)
   Lisp.++ (Lisp.list prover_options)
   Lisp.++ (Lisp.list [setOfSupportOn])
   Lisp.++ (Lisp.list snarkBaseHypothesis)
   Lisp.++ (Lisp.list snarkRewriteHypothesis)
   Lisp.++ (Lisp.list [setOfSupportOff])
   Lisp.++ (Lisp.list prover_options)
   Lisp.++ (Lisp.list baseAxioms)
   Lisp.++ (Lisp.list snarkHypothesis)
   Lisp.++ (Lisp.list [snarkConjecture])
  

 op makeSnarkProveEvalForm: List LispCell * List LispCell * List LispCell * List LispCell * List LispCell
                           * List LispCell * LispCell * String -> LispCell

 def makeSnarkProveEvalForm(prover_options, snarkSortDecl, snarkOpDecls, snarkBaseHypothesis, snarkRewriteHypothesis,
			    snarkHypothesis, snarkConjecture, snarkLogFileName) =
   %let _ = if specwareDebug? then toScreen("Proving snark fmla: ") else () in
   %let _ = if specwareDebug? then LISP.PPRINT(snarkConjecture) else Lisp.list [] in
   %let _ = if specwareDebug? then writeLine(" using: ") else () in
   %let _ = if specwareDebug? then LISP.PPRINT(Lisp.list(snarkHypothesis)) else Lisp.list [] in
   let setOfSupportOn = Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(false)]) in
   let setOfSupportOff = Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(true)]) in
   let snarkProverDecls = makeSnarkProveDecls(prover_options, snarkSortDecl, snarkOpDecls, snarkBaseHypothesis, snarkRewriteHypothesis,
					      snarkHypothesis, snarkConjecture, snarkLogFileName) in
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
				 Lisp.symbol("CL-USER","LOGFILE")]],
	   Lisp.list([Lisp.symbol("CL","WRITE-LINE"), Lisp.string("Snark is invoked by evaluating:")]),
	   Lisp.list([Lisp.symbol("CL","PPRINT"),
		      Lisp.quote(Lisp.list[Lisp.symbol("CL","LET"), Lisp.list []] Lisp.++ snarkProverDecls)])
	  ]
	  Lisp.++ snarkProverDecls
		    ]


}

