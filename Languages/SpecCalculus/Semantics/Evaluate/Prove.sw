SpecCalc qualifying spec {
  import Signature
  import ../SpecPath
  import /Languages/Snark/SpecToSnark
  
 def SpecCalc.evaluateProve (claim_name, spec_term, prover_name, assertions, option) pos = {
     (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo spec_term;
     (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "base")
                     (SpecPath_Relative {path = ["Library","Base"],
                                         hashSuffix = None});
     proved:Boolean <-
     (case value of
	| Spec spc -> return (proveInSpec (claim_name, 
				    subtractSpec spc baseSpec, 
				    prover_name, 
				    assertions, 
				    option,
				    pos))
	| _ -> raise (TypeCheck (pos, "Argument to prove command is not a spec.")));
     URI <- getCurrentURI;
     result <-  return (Proof (if proved then {status = Proved, unit = URI} else {status = Unproved, unit = URI}));
     return (result,timeStamp,depURIs)
   }

 op proveInSpec: ClaimName * Spec * String * Assertions * List LispCell * Position -> Boolean
 def proveInSpec (claim_name, spc, prover_name, assertions, option, pos) =
   let findClaimInSpec = firstUpTo (fn (_, propertyName, _, _) -> claim_name = propertyName) spc.properties in
   case findClaimInSpec of
%     | None -> %raise (TypeCheck (pos, "Claim name is not in spec."))
     | Some (claim, validHypothesis) -> proveWithHypothesis(claim, validHypothesis, spc, prover_name, assertions, option)


 op proveWithHypothesis: Property * List Property * Spec * String * Assertions * List LispCell -> Boolean
 def proveWithHypothesis(claim, possibleAssertions, spc, prover_name, assertions, option) =
   let hypothesis = 
         case assertions of
	   | All -> possibleAssertions
	   | Explicit possibilities -> filter (fn (_, propertyName:String, _, _) -> member(propertyName, (possibilities:(List String)))) possibleAssertions in
   let snarkSortDecls = snarkSorts(spc) in
   let snarkOpDecls = snarkOpDecls(spc) in
   let snarkHypothesis = map (fn (prop) -> snarkProperty(spc, prop)) hypothesis in
   let snarkConjecture = snarkConjecture(spc, claim) in
   let snarkEvalForm = makeSnarkProveEvalForm(option, snarkSortDecls, snarkOpDecls, snarkHypothesis, snarkConjecture) in
     let _ = writeLine("Calling Snark by evaluating: ") in
     let _ = LISP.PPRINT(snarkEvalForm) in
     let result = Lisp.apply(Lisp.symbol("LISP","FUNCALL"),
			[Lisp.list [Lisp.symbol("SNARK","LAMBDA"),Lisp.nil(),snarkEvalForm]]) in
     let proved = ":PROOF-FOUND" = toString(result) in
     let _ = if proved then writeLine("Theorem is Proved!") else writeLine("Theorem is not proved.") in
       proved

 op makeSnarkProveEvalForm: List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * List Lisp.LispCell * Lisp.LispCell -> Lisp.LispCell
 def makeSnarkProveEvalForm(option, snarkSortDecl, snarkOpDecls, snarkHypothesis, snarkConjecture) =
   let _ = toScreen("Proving snark fmla: ") in
   let _ = LISP.PPRINT(snarkConjecture) in
   let _ = writeLine(" using: ") in
   let _ = LISP.PPRINT(Lisp.list(snarkHypothesis)) in
%    let _ = printSortToTerminal srt in

   	 Lisp.list
	  [
	    Lisp.symbol("LISP","LET"), Lisp.list [],
	    Lisp.list([Lisp.symbol("SNARK","INITIALIZE")]),
	    Lisp.list([Lisp.symbol("SNARK","USE-RESOLUTION"), Lisp.bool(true)])
	  ]
	  Lisp.++ (Lisp.list snarkSortDecl)
	  Lisp.++ (Lisp.list snarkOpDecls)
	  Lisp.++ (Lisp.list snarkHypothesis)
          Lisp.++ (Lisp.list [snarkConjecture])


}

