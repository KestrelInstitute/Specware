SpecCalc qualifying spec {
  import Signature
  import ../SpecPath
  import /Languages/Snark/SpecToSnark
  
 def SpecCalc.evaluateProve (claim_name, spec_term, prover_name, assertions, possible_options) pos = {
     (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo spec_term;
     (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "base")
                     (SpecPath_Relative {path = ["Library","Base"],
                                         hashSuffix = None});
     URI <- getCurrentURI;
     snarkLogFileName <- URItoSnarkLogFile (URI);
     _ <- return (ensureDirectoriesExist snarkLogFileName);
     proof_name <- return (URItoProofName (URI));
     spec_name <- return (SpecTermToSpecName(spec_term));
     options <- 
       (case possible_options of
	  | Options options  -> return (options)
	  | Error   (msg, str) -> raise  (SyntaxError (msg ^ str)));
     proved:Boolean <-
       (case value of
	  | Spec spc -> (proveInSpec (proof_name,
				      claim_name, 
				      subtractSpec spc baseSpec,
				      spec_name,
				      prover_name, 
				      assertions, 
				      options,
				      snarkLogFileName,
				      pos))
	  | _ -> raise (Proof (pos, "Argument to prove command is not a spec.")));
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

 op proveInSpec: Option String * ClaimName * Spec * Option String * String * 
                 Assertions * List LispCell * String * Position -> SpecCalc.Monad Boolean
 def proveInSpec (proof_name, claim_name, spc, spec_name, prover_name,
		  assertions, options, snarkLogFileName, pos) = {
   result <-
   let findClaimInSpec = firstUpTo (fn (_, propertyName, _, _) -> claim_name = propertyName)
                                   spc.properties in
   case findClaimInSpec of
     | None -> raise (Proof (pos, "Claim name is not in spec."))
     | Some (claim, validHypothesis) ->
	 let actualHypothesis = actualHypothesis(validHypothesis, assertions, pos) in
	   if (case assertions of All -> true | Explicit possibilities -> length actualHypothesis = length possibilities)
	     then return (proveWithHypothesis(proof_name, claim, actualHypothesis, spc, spec_name, 
				     prover_name, options, snarkLogFileName))
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

 op proveWithHypothesis: Option String * Property * List Property * Spec * Option String * String * 
                         List LispCell * String -> Boolean

 def proveWithHypothesis(proof_name, claim, hypothesis, spc, spec_name, prover_name,
			 options, snarkLogFileName) =
   let (claim_type,claim_name,_,_) = claim in
   let def claimType(ct) = 
         case ct of
	   | Conjecture -> "Conjecture" 
	   | Theorem -> "Theorem" 
	   | Axiom -> "Axiom" in
   let claim_type = claimType(claim_type) in
   let snarkSortDecls = snarkSorts(spc) in
   let snarkOpDecls = snarkOpDecls(spc) in
   let snarkHypothesis = map (fn (prop) -> snarkProperty(spc, prop)) hypothesis in
   let snarkConjecture = snarkConjecture(spc, claim) in
   let snarkEvalForm = makeSnarkProveEvalForm(options, snarkSortDecls, snarkOpDecls, snarkHypothesis, snarkConjecture, snarkLogFileName) in
%     let _ = writeLine("Calling Snark by evaluating: ") in
%     let _ = LISP.PPRINT(snarkEvalForm) in
     let result = Lisp.apply(Lisp.symbol("LISP","FUNCALL"),
			[Lisp.list [Lisp.symbol("SNARK","LAMBDA"),Lisp.nil(),snarkEvalForm]]) in
     let proved = ":PROOF-FOUND" = toString(result) in
     let _ = displayProofResult(proof_name, claim_type, claim_name, spec_name, proved, snarkLogFileName) in
       proved

 op makeSnarkProveEvalForm: List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * Lisp.LispCell * String -> Lisp.LispCell

 def makeSnarkProveEvalForm(options, snarkSortDecl, snarkOpDecls, snarkHypothesis, snarkConjecture, snarkLogFileName) =
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
	   Lisp.list([Lisp.symbol("SNARK","USE-RESOLUTION"), Lisp.bool(true)])
	  ]
	  Lisp.++ (Lisp.list options)
	  Lisp.++ (Lisp.list snarkSortDecl)
	  Lisp.++ (Lisp.list snarkOpDecls)
	  Lisp.++ (Lisp.list snarkHypothesis)
	  Lisp.++ (Lisp.list [snarkConjecture])]


}

