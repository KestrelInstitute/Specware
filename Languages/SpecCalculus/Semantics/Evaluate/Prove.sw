SpecCalc qualifying spec {
  import Signature
  import Spec/SpecUnion
  import ../SpecPath
  import /Languages/Snark/SpecToSnark
  import URI/Utilities                                    % for uriToString, if used...
  
 def SpecCalc.evaluateProve (claim_name, spec_term, prover_name, assertions, possible_options) pos = {
     %% -------------------------------------------
     %% next two lines are optional:
     uri <- getCurrentURI;
     print (";;; Processing prove at "^(uriToString uri)^"\n");
     %% -------------------------------------------
          (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo spec_term;
     (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "base")
                                                 (SpecPath_Relative {path = ["Library","Base"],
								     hashSuffix = None});
     (Spec baseProverSpec,_,_) <- SpecCalc.evaluateURI (Internal "ProverBase")
                                                       (SpecPath_Relative {path = ["Library","Base","ProverBase"],
									   hashSuffix = None});
     URI <- getCurrentURI;
     snarkLogFileName <- URItoSnarkLogFile (URI);
     _ <- return (ensureDirectoriesExist snarkLogFileName);
     proof_name <- return (URItoProofName (URI));
     spec_name <- return (SpecTermToSpecName(spec_term));
     uspc <- (
	     case coerceToSpec value of
	       | Spec spc -> return spc %specUnion([spc, baseProverSpec])
               | _ -> raise (Proof (pos, "Argument to prove command is not coerceable to a spec.")));
     prover_options <- 
       (case possible_options of
	  | Options prover_options -> return (prover_options)
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
			      unit   = URI});
     return (result, timeStamp, depURIs)
   }

 op URItoSnarkLogFile: URI -> SpecCalc.Monad String
 def URItoSnarkLogFile (uri as {path,hashSuffix}) = {
   result <-
   case hashSuffix of
     | None -> URItoSingleSnarkLogFile(uri)
     | Some _ -> URItoMultipleSnarkLogFile(uri);
   return result
 }

 op URItoSingleSnarkLogFile: URI -> SpecCalc.Env String
 def URItoSingleSnarkLogFile (uri as {path,hashSuffix}) =
    {prefix <- removeLastElem path;
     mainName <- lastElem path;
     let filNm = (uriToPath {path=prefix,hashSuffix=None})
        ^ "/snark/" ^ mainName ^ ".log"
     in
      return filNm}

 op URItoMultipleSnarkLogFile: URI -> SpecCalc.Env String
 def URItoMultipleSnarkLogFile (uri as {path,hashSuffix}) =
   let Some hashSuffix = hashSuffix in
    {prefix <- removeLastElem path;
     newSubDir <- lastElem path;
     mainName <- return hashSuffix;
     let filNm = (uriToPath {path=prefix,hashSuffix=None})
        ^ "/snark/" ^ newSubDir ^ "/" ^ mainName ^ ".log"
     in
      return filNm}

 op URItoProofName: URI -> Option String
 def URItoProofName (uri as {path,hashSuffix}) =
    hashSuffix

 op SpecTermToSpecName: SCTerm -> (Option String)
 def SpecTermToSpecName (scterm as (term,_)) =
   case term of
     | URI rURI -> Some (showRelativeURI(rURI))
     | Spec _ -> None
     | _ -> None

 op proveInSpec: Option String * ClaimName * Spec * Option String * Spec * String * 
                 Assertions * List LispCell * String * Position -> SpecCalc.Monad Boolean
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
%     let _ = writeLine("Calling Snark by evaluating: ") in
%     let _ = LISP.PPRINT(snarkEvalForm) in
     let result = Lisp.apply(Lisp.symbol("LISP","FUNCALL"),
			[Lisp.list [Lisp.symbol("SNARK","LAMBDA"),Lisp.nil(),snarkEvalForm]]) in
     let proved = ":PROOF-FOUND" = toString(result) in
     let _ = displayProofResult(proof_name, claim_type, claim_name, spec_name, proved, snarkLogFileName) in
       proved

 op makeSnarkProveEvalForm: List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * Lisp.LispCell * String -> Lisp.LispCell

 def makeSnarkProveEvalForm(prover_options, snarkSortDecl, snarkOpDecls, snarkBaseHypothesis, snarkHypothesis, snarkConjecture, snarkLogFileName) =
%   let _ = toScreen("Proving snark fmla: ") in
%   let _ = LISP.PPRINT(snarkConjecture) in
%   let _ = writeLine(" using: ") in
%   let _ = LISP.PPRINT(Lisp.list(snarkHypothesis)) in
%    let _ = printSortToTerminal srt in

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
	   Lisp.symbol("LISP","LET"),
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
	  Lisp.++ (Lisp.list prover_options)
	  Lisp.++ (Lisp.list snarkSortDecl)
	  Lisp.++ (Lisp.list snarkOpDecls)
	  Lisp.++ (Lisp.list snarkBaseHypothesis)
	  Lisp.++ (Lisp.list baseAxioms)
	  Lisp.++ (Lisp.list snarkHypothesis)
	  Lisp.++ (Lisp.list [snarkConjecture])]


}

