SpecCalc qualifying spec {
  import UnitId
  import Spec/SpecUnion
  import /Languages/Snark/SpecToSnark
  import UnitId/Utilities                                    % for uidToString, if used...

 op PARSER4.READ_LIST_OF_S_EXPRESSIONS_FROM_STRING: String -> ProverOptions
  
 def SpecCalc.evaluateProve (claim_name, spec_term, prover_name, assertions, possible_options) pos = {
     unitId <- getCurrentUnitId;
     print (";;; Processing prove at " ^ (uidToString unitId) ^ "\n");
     (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo spec_term;
     (optBaseUnitId,baseSpec) <- getBase;
     proverBaseUnitId <- pathToRelativeUID "/Library/Base/ProverBase";
     (Spec baseProverSpec,_,_) <- SpecCalc.evaluateUID (Internal "ProverBase") proverBaseUnitId;
     snarkLogFileName <- UIDtoSnarkLogFile unitId;
     _ <- return (ensureDirectoriesExist snarkLogFileName);
     proof_name <- return (UIDtoProofName unitId);
     spec_name <- return (SpecTermToSpecName(spec_term));
     uspc <- (
	     case coerceToSpec value of
	       | Spec spc -> return spc %specUnion([spc, baseProverSpec])
               | _ -> raise (Proof (pos, "Argument to prove command is not coerceable to a spec.")));
     prover_options <- 
       (case possible_options of
	  | OptionString prover_options -> return (prover_options)
	  | OptionName prover_option_name -> 
	        proverOptionsFromSpec(prover_option_name, uspc, spec_name)
	  | Error   (msg, str)     -> raise  (SyntaxError (msg ^ str)));
     proved:Boolean <- (proveInSpec (proof_name,
				     claim_name, 
				     subtractSpec uspc baseSpec,
				     spec_name,
				     baseProverSpec,
				     prover_name, 
				     assertions, 
				     prover_options,
				     snarkLogFileName,
				     pos));
     result <- return (Proof {status = if proved then Proved else Unproved, 
			      unit   = unitId});
     return (result, timeStamp, depUIDs)
   }

 def proverOptionsFromSpec(name, spc, spec_name) = {
   possible_options_op <- return(findTheOp(spc, name));
   options_def <-
      (case possible_options_op of
	 | Some (_,_,_,[(_,opTerm)]) -> return (opTerm)
	 | _ -> raise (SyntaxError ("Cannot find prover option definition, " ^ printQualifiedId(name) ^
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

 op UIDtoSnarkLogFile: UnitId -> SpecCalc.Env String
 def UIDtoSnarkLogFile (unitId as {path,hashSuffix}) = {
   result <-
   case hashSuffix of
     | None -> UIDtoSingleSnarkLogFile(unitId)
     | Some _ -> UIDtoMultipleSnarkLogFile(unitId);
   return result
 }

 op UIDtoSingleSnarkLogFile: UnitId -> SpecCalc.Env String
 def UIDtoSingleSnarkLogFile (unitId as {path,hashSuffix}) =
    {prefix <- removeLastElem path;
     mainName <- lastElem path;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/snark/" ^ mainName ^ ".log"
     in
      return filNm}

 op UIDtoMultipleSnarkLogFile: UnitId -> SpecCalc.Env String
 def UIDtoMultipleSnarkLogFile (unitId as {path,hashSuffix}) =
   let Some hashSuffix = hashSuffix in
    {prefix <- removeLastElem path;
     newSubDir <- lastElem path;
     mainName <- return hashSuffix;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/snark/" ^ newSubDir ^ "/" ^ mainName ^ ".log"
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

 op proveInSpec: Option String * ClaimName * Spec * Option String * Spec * String * 
                 Assertions * List LispCell * String * Position -> SpecCalc.Env Boolean
 def proveInSpec (proof_name, claim_name, spc, spec_name, base_spc, prover_name,
		  assertions, prover_options, snarkLogFileName, pos) = {
   result <-
   let baseHypothesis = base_spc.properties in
   let findClaimInSpec = firstUpTo (fn (_, propertyName, _, _) -> claim_name = propertyName)
                                   spc.properties in
   case findClaimInSpec of
     | None -> raise (Proof (pos, "Claim name is not in spec."))
     | Some (claim, validHypothesis) ->
	 let actualHypothesis = actualHypothesis(validHypothesis, assertions, pos) in
	   if (case assertions of All -> true | Explicit possibilities -> length actualHypothesis = length possibilities)
	     then return (proveWithHypothesis(proof_name, claim, actualHypothesis, spc, spec_name, baseHypothesis, base_spc,
					      prover_name, prover_options, snarkLogFileName))
	   else raise (Proof (pos, "assertion not in spec."));
   return result}

 op actualHypothesis: List Property * Assertions * Position -> List Property

 def actualHypothesis(validHypothesis, assertions, pos) =
     case assertions of
      | All -> validHypothesis
      | Explicit possibilities -> 
         let hypothesis = filter (fn (_, propertyName:String, _, _) -> member(propertyName, (possibilities:(List String)))) validHypothesis in
	   hypothesis

 op displayProofResult: (Option String) * String * String * (Option String) * Boolean * String -> Boolean
 def displayProofResult(proof_name, claim_type, claim_name, spec_name, proved, snarkLogFileName) =
   let _ =
   case proof_name of
     | None -> 
         (case spec_name of
	   | None -> displaySingleAnonymousProofResult(claim_type, claim_name, proved)
	   | Some spec_name -> displaySingleProofResult(claim_type, claim_name, spec_name, proved))
     | Some proof_name ->
	 case spec_name of
	   | None -> displayMultipleAnonymousProofResult(proof_name, claim_type, claim_name, proved)
	   | Some spec_name -> 
	       displayMultipleProofResult(proof_name, claim_type, claim_name, spec_name, proved) in
   let _ = writeLine("    Snark Log file: " ^ snarkLogFileName) in
     proved


  def displaySingleAnonymousProofResult(claim_type, claim_name, proved) =
    let provedString = if proved then "is Proved!" else "is NOT proved." in
    let _ = writeLine(claim_type^" "^claim_name^" "^provedString) in
      proved

  def displaySingleProofResult(claim_type, claim_name, spec_name, proved) =
    let provedString = if proved then "is Proved!" else "is NOT proved." in
    let _ = writeLine(claim_type^" "^claim_name^" in "^spec_name^" "^provedString) in
      proved

  def displayMultipleAnonymousProofResult(proof_name, claim_type, claim_name, proved) =
    let provedString = if proved then "is Proved!" else "is NOT proved." in
    let _ = writeLine(proof_name^": "^claim_type^" "^claim_name^" "^provedString) in
      proved

  def displayMultipleProofResult(proof_name, claim_type, claim_name, spec_name, proved) =
    let provedString = if proved then "is Proved!" else "is NOT proved." in
    let _ = writeLine(proof_name^": "^claim_type^" "^claim_name^" in "^spec_name^" "^provedString) in
      proved

 op proveWithHypothesis: Option String * Property * List Property * Spec * Option String * List Property * Spec *
                         String * List LispCell * String -> Boolean

 def proveWithHypothesis(proof_name, claim, hypothesis, spc, spec_name, base_hypothesis, base_spc,
			 prover_name, prover_options, snarkLogFileName) =
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
   let snarkBaseHypothesis = map (fn (prop) -> snarkProperty(context, base_spc, prop))
                                 base_hypothesis in
   let snarkHypothesis = map (fn (prop) -> snarkProperty(context, spc, prop)) hypothesis in
   let snarkConjecture = snarkConjecture(context, spc, claim) in
   let snarkEvalForm = makeSnarkProveEvalForm(prover_options, snarkSortDecls, snarkOpDecls, snarkBaseHypothesis, snarkHypothesis, snarkConjecture, snarkLogFileName) in
     let _ = if specwareDebug? then writeLine("Calling Snark by evaluating: ") else () in
     let _ = if specwareDebug? then LISP.PPRINT(snarkEvalForm) else Lisp.list [] in
     let result = Lisp.apply(Lisp.symbol("CL","FUNCALL"),
			[Lisp.list [Lisp.symbol("SNARK","LAMBDA"),Lisp.nil(),snarkEvalForm]]) in
     let proved = ":PROOF-FOUND" = System.toString(result) in
     let _ = displayProofResult(proof_name, claim_type, claim_name, spec_name, proved, snarkLogFileName) in
       proved

 op makeSnarkProveEvalForm: List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * Lisp.LispCell * String -> Lisp.LispCell

 def makeSnarkProveEvalForm(prover_options, snarkSortDecl, snarkOpDecls, snarkBaseHypothesis, snarkHypothesis, snarkConjecture, snarkLogFileName) =
   let _ = if specwareDebug? then toScreen("Proving snark fmla: ") else () in
   let _ = if specwareDebug? then LISP.PPRINT(snarkConjecture) else Lisp.list [] in
   let _ = if specwareDebug? then writeLine(" using: ") else () in
   let _ = if specwareDebug? then LISP.PPRINT(Lisp.list(snarkHypothesis)) else Lisp.list [] in

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
	   Lisp.list([Lisp.symbol("SNARK","INITIALIZE")]),
	   Lisp.list([Lisp.symbol("SNARK","RUN-TIME-LIMIT"), Lisp.nat(60)]),
           Lisp.list([Lisp.symbol("SNARK","USE-LISP-TYPES-AS-SORTS"), Lisp.bool(true)]),
           Lisp.list([Lisp.symbol("SNARK","USE-CODE-FOR-NUMBERS"), Lisp.bool(true)]),
	   Lisp.list([Lisp.symbol("SNARK","USE-RESOLUTION"), Lisp.bool(true)])
	  ]
	  Lisp.++ (Lisp.list snarkSortDecl)
	  Lisp.++ (Lisp.list snarkOpDecls)
	  Lisp.++ (Lisp.list prover_options)
	  Lisp.++ (Lisp.list snarkBaseHypothesis)
	  Lisp.++ (Lisp.list baseAxioms)
	  Lisp.++ (Lisp.list snarkHypothesis)
	  Lisp.++ (Lisp.list [snarkConjecture])]


}

