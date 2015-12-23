(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SpecCalc qualifying spec 
  import UnitId

  import /Languages/MetaSlang/CodeGen/Generic/CodeGenTransforms
  import /Languages/MetaSlang/CodeGen/Generic/UnfoldTypeAliases            
  import /Languages/MetaSlang/CodeGen/Generic/Poly2Mono

  import /Languages/Snark/SpecToSnark
  import /Provers/DP/ToFourierMotzkin

  import /Languages/MetaSlang/Transformations/ExplicateHiddenAxioms
  import /Languages/MetaSlang/Transformations/RemoveQuotient
  import /Languages/MetaSlang/CodeGen/AddMissingFromBase

  import /Library/IO/Primitive/IO
  import UnitId/Utilities                                    % for uidToString, if used...


 op PARSER4.READ_LIST_OF_S_EXPRESSIONS_FROM_STRING: String -> ProverOptions
  
 def SpecCalc.evaluateProve (claimName, term, proverName, assertions, possibleOptions,
			     baseOptions, answerVariable) pos =
   {
    (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo term;

    value <- return (coerceToSpec value);
    valueName <- return (SpecTermToSpecName(term));
    result <- (case value of
		 | Spec spc -> evaluateSpecProve (claimName, spc, valueName, proverName, assertions,
						  possibleOptions, baseOptions, answerVariable) pos
		 | Other other -> evaluateOtherProve (claimName, other, valueName, proverName,
						      assertions, possibleOptions, baseOptions, answerVariable) pos
		 | _ -> raise (Proof (pos, "Argument to prove command is neither coerceable to a spec nor Other.")));
    return (result, timeStamp, depUIDs)
   }

  op evaluateSpecProve: ClaimName * Spec * Option String * ProverName * Assertions * ProverOptions
                          * ProverBaseOptions * AnswerVar -> Position
                        -> SpecCalc.Env Value
  def evaluateSpecProve (claimName, spc, specName, proverName, assertions, possibleOptions,
			 baseOptions, answerVariable) pos =
    {
     unitId <- getCurrentUnitId;
     print (";;; Elaborating proof-term at " ^ (uidToString unitId) ^ "\n");
     (optBaseUnitId,baseSpec) <- getBase;
     baseProverSpec <- getBaseProverSpec;
     %% print (printSpecFlat baseProverSpec);
     %% print (printSpecFlat baseSpec);
     baseProverSpec <- return(subtractSpecProperties(baseProverSpec,baseSpec));
     %% print (printSpecFlat baseProverSpec);
     % rewriteProverSpec <- getRewriteProverSpec;
     proverLogFileName <- UIDtoLogFile(unitId, if proverName = "Both" then "Snark" else proverName, "log");
     finalSpecFileName <- UIDtoLogFile(unitId, if proverName = "Both" then "Snark" else proverName, "sw");
     _ <- return (ensureDirectoriesExist proverLogFileName);
     proofName <- return (UIDtoProofName unitId);
     expandedSpec <- return (transformSpecForFirstOrderProver baseSpec spc);
     _ <- return (writeLine("    Expanded spec file: " ^ finalSpecFileName));
     _ <- return (writeLine("    Snark Log file: " ^ proverLogFileName));
     _ <- return (printFlatSpecToFile(finalSpecFileName, expandedSpec));
     _ <- return (if specwareDebug? then writeString(printSpec(expandedSpec)) else ());
     proverOptions <- 
       (case possibleOptions of
	  | OptionString proverOptions -> return (proverOptions)
	  | OptionName proverOptionName -> 
	        proverOptionsFromSpec(proverOptionName, spc, specName)
	  | Error   (msg, str)     -> raise  (SyntaxError (msg ^ str)));
     includeBase <- return proverUseBase?;
     proved <- (proveInSpec (proofName,
			     claimName, 
			     expandedSpec,
			     specName,
			     baseProverSpec,
			     % rewriteProverSpec,
			     proverName, 
			     assertions, 
			     proverOptions,
			     includeBase,
			     answerVariable,
			     proverLogFileName,
			     pos));
     return (Proof {status = if proved then Proved else Unproved, 
		    unit   = unitId})
    }

  op PrimitiveTypeOp? (Qualified (q, id) : QualifiedId) : Bool =
    case q of
      | "Bool"       -> id in? ["Bool", "show", "toString"]
      | "Integer"    -> id in? ["Int", "Int0", "+", "-", "*", "div", "rem", "<=", "<", "~", ">", ">=", "**", "isucc", "ipred", "toString"]
      | "IntegerAux" -> id in? ["-"]  % unary minus
      | "Nat"        -> id in? ["Nat", "show", "toString"]
      | "Char"       -> id in? ["Char", "chr", "ord", "compare"] 
      | "String"     -> id in? ["String", "compare", "append", "++", "^", "<", "newline", "length"]
      | "System"     -> id in? ["writeLine", "toScreen"]
      | _ -> false

  op transformSpecForFirstOrderProver: AnnSpec.Spec -> AnnSpec.Spec -> AnnSpec.Spec
  def transformSpecForFirstOrderProver baseSpc spc =
    let spc = addMissingFromBase(baseSpc,spc,PrimitiveTypeOp?) in
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
    let spc = unfoldTypeAliases spc in
    let spc = removeCurrying spc in
     %let _ = writeLine("remCur") in
     %let _ = writeLine(printSpec spc) in
    let spc = removeQuotient spc in
     %let _ = writeLine("remQ") in
     %let _ = writeLine(printSpec spc) in
     %let spc = aux_instantiateHOFns spc in%
     %let _ = writeLine("instHO") in
     %let _ = writeLine(printSpec spc) in
     %let spc = lambdaToInner spc in
    let spc = poly2monoForSnark(spc,true) in
     %let _ = writeLine("remPoly") in
     %let _ = writeLine(printSpec spc) in
     %let spc = addEqOps spc in
     %let _ = printSpecWithTypesToTerminal spc in
    let spc = lambdaLift spc false in
     %let _ = writeLine("lambdaLift") in
     %let _ = writeLine(printSpec spc) in
     %let spc = foldRecordTypes(spc) in
    let spc = addTypeConstructorsInternal (spc, true) in % true is for snark?
     %let _ = writeLine("ConsAccAdds") in
     %let _ = writeLine(printSpec spc) in
     %let spc = conformOpDecls spc in
     %let spc = adjustAppl spc in
    let spc = aux_instantiateHOFns spc true in  % temporary flag to enable test in makeUnfoldMap: tvs ~= []
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

%  op getRewriteProverSpec : Env Spec
%  def getRewriteProverSpec = 
%    {
%     (optBaseUnitId,baseSpec) <- getBase;
%     proverRewriteUnitId <- pathToRelativeUID "/Library/Base/ProverRewrite";
%     (Spec rewriteProverSpec,_,_) <- SpecCalc.evaluateUID (Internal "ProverRewrite") proverRewriteUnitId;
%     return (subtractSpecProperties(rewriteProverSpec, baseSpec))
%    }

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
    {prefix <- removeLast path;
     mainName <- last path;
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/"^proverName^"/" ^ mainName ^ "." ^ suffix
     in
      return filNm}

 op UIDtoMultipleLogFile: UnitId * String * String -> SpecCalc.Env String
 def UIDtoMultipleLogFile (unitId as {path,hashSuffix}, proverName, suffix) =
   let Some hashSuffix = hashSuffix in
    {prefix <- removeLast path;
     newSubDir <- last path;
     mainName <- return (convertToFileName hashSuffix);
     let filNm = (uidToFullPath {path=prefix,hashSuffix=None})
        ^ "/"^proverName^"/" ^ newSubDir ^ "/" ^ mainName ^ "." ^ suffix
     in
      return filNm}

 op UIDtoProofName: UnitId -> Option String
 def UIDtoProofName (unitId as {path,hashSuffix}) =
    hashSuffix

 op claimNameMatch: ClaimName * ClaimName -> Bool
 def claimNameMatch(cn, pn) =
   let Qualified(cq, cid) = cn in
   let Qualified(pq, pid) = pn in
   if cq = UnQualified
     then pid = cid
   else cq = pq && cid = pid

 op  proveInSpec: Option String * ClaimName * Spec * Option String * Spec * String * 
                  Assertions * LispCells * Bool * AnswerVar * String * Position -> SpecCalc.Env Bool
 def proveInSpec (proofName, claimName, spc, specName, baseSpc, % rewriteSpc,
                  proverName, assertions, proverOptions, includeBase, answerVariable, proverLogFileName, pos) = 
   let _ = debug("pinspec") in
   let props             = allProperties spc        in
   let baseHypothesis    = allProperties baseSpc    in
   % let rewriteHypothesis = allProperties rewriteSpc in
   let props_upto_conjecture = findLeftmostAndPreceding
                                 (fn (pType, pName, _, _, _) -> 
                                     pType in? [Conjecture,Theorem] && 
                                    claimNameMatch (claimName, pName))
                                 props
   in
     case props_upto_conjecture of
       | None -> 
         %% could not find conjecture foo
         if exists? (fn (pType, pName, _, _, _) -> 
                      pType = Axiom && claimNameMatch (claimName, pName)) 
                    props 
           then
             %% but could find axiom foo
             let _ = toScreen ("\n;;; For " 
                                 ^ (case proofName of 
                                      | Some s -> "proof " ^ s
                                      | _ -> "an anonymous proof")
                                 ^ ", the purported conjecture " ^ printQualifiedId claimName 
                                 ^ " is already an axiom in "
                                 ^ (case specName of 
                                      | Some s -> "spec " ^ s
                                      | _ -> "an anonymous spec")
                                 ^ "\n")
             in
               return true
         else
           raise (Proof (pos, "Claim " ^ printQualifiedId claimName ^ " is not in spec."))
       | Some (claim, validHypothesis) ->
         let actualHypothesis  = actualHypothesis  (validHypothesis,  assertions, pos) in
         let missingHypothesis = missingHypothesis (actualHypothesis, assertions)      in
         case missingHypothesis of 
           | [] -> 
             return (proveWithHypothesis (proofName, claim, actualHypothesis, spc, specName,
                                          baseHypothesis, baseSpc, % rewriteHypothesis,  rewriteSpc,
                                          proverName, proverOptions, includeBase, answerVariable,
                                          proverLogFileName))
           | _ -> 
             raise (Proof (pos, "assertions: "
                             ^ printMissingHypothesis missingHypothesis
                             ^ " not in spec.\nAsserions in spec: "
                             ^ printMissingHypothesis (map (fn((_,pn,_,_,_)) -> pn) actualHypothesis)))


 op actualHypothesis: Properties * Assertions * Position -> Properties

 def actualHypothesis (validHypothesis, assertions, _ (* pos *)) =
     case assertions of
      | All -> validHypothesis
      | Explicit possibilities -> 
	let hypothesis = filter (fn (_, propertyName, _, _, _) ->
				  propertyName in? possibilities)
			   validHypothesis
	in
	  hypothesis

 op missingHypothesis: Properties * Assertions -> ClaimNames

 def missingHypothesis (actualHypothesis, assertions) =
     case assertions of
      | All -> []
      | Explicit possibilities -> 
         let missingHypothesis = filter (fn (claimName:ClaimName) ->
					  ~(exists?(fn (_, propName:ClaimName,_,_,_) ->
						    claimNameMatch(claimName, propName))
					      actualHypothesis))
				   possibilities
	 in
	   missingHypothesis

 op printMissingHypothesis: ClaimNames -> String
 def printMissingHypothesis(cns) =
   case cns of
     | []  -> ""
     | [p] -> printQualifiedId(p)
     | p :: ps -> printQualifiedId(p)^", "^printMissingHypothesis(ps)

 op displayProofResult: String * (Option String) * String * ClaimName * (Option String) * Bool * String-> Bool
 def displayProofResult(proverName, proofName, claimType, claimName, specName, proved, runTime) =
   let _ =
   case proofName of
     | None -> 
         (case specName of
	   | None -> displaySingleAnonymousProofResult(proverName, claimType, claimName, proved, runTime)
	   | Some specName -> displaySingleProofResult(proverName, claimType, claimName, specName, proved, runTime))
     | Some proofName ->
	 case specName of
	   | None -> displayMultipleAnonymousProofResult(proverName, proofName, claimType, claimName, proved, runTime)
	   | Some specName -> 
	       displayMultipleProofResult(proverName, proofName, claimType, claimName, specName, proved, runTime) in
     proved


  def displaySingleAnonymousProofResult(proverName, claimType, claimName, proved, runTime) =
    let provedString = provedString(proved) in
    let proverString = proverString(proverName) in
    let timeString = timeString(runTime) in
    let _ = writeLine(claimType^" "^printQualifiedId(claimName)^provedString^proverString^timeString) in
      proved

  def displaySingleProofResult(proverName, claimType, claimName, specName, proved, runTime) =
    let provedString = provedString(proved) in
    let proverString = proverString(proverName) in
    let timeString = timeString(runTime) in
    let _ = writeLine(claimType^" "^printQualifiedId(claimName)^" in "^specName^provedString^proverString^timeString) in
      proved

  def displayMultipleAnonymousProofResult(proverName, proofName, claimType, claimName, proved, runTime) =
    let provedString = provedString(proved) in
    let proverString = proverString(proverName) in
    let timeString = timeString(runTime) in
    let _ = writeLine(proofName^": "^claimType^" "^printQualifiedId(claimName)^provedString^proverString^timeString) in
      proved

  def displayMultipleProofResult(proverName, proofName, claimType, claimName, specName, proved, runTime) =
    let provedString = provedString(proved) in
    let proverString = proverString(proverName) in
    let timeString = timeString(runTime) in
    let _ = writeLine(proofName^": "^claimType^" "^printQualifiedId(claimName)^" in "^specName^provedString^proverString^timeString) in
      proved

 op mes.print_total_run_time: () -> LispCell

 op snarkRunTime: () -> String
 def snarkRunTime() =
   let rt = mes.print_total_run_time() in
   LispString(rt)

 op printSnarkClocks: () -> LispCell
 def printSnarkClocks() =
   let evalForm = Lisp.list([Lisp.symbol("SNARK","PRINT-CLOCKS")]) in
   Lisp.apply(Lisp.symbol("CL","FUNCALL"),
			     [Lisp.eval(Lisp.list [Lisp.symbol("CL","FUNCTION"),
						   Lisp.list [Lisp.symbol("SNARK","LAMBDA"),
							      Lisp.nil(),evalForm]])])

 op provedString: Bool -> String
 def provedString(proved) =
   if proved
     then " is Proved!"
   else " is NOT proved"

 op proverString: String -> String
 def proverString(proverName) =
   case proverName of
     | "FourierM" -> " using simple inequality reasoning"
     | "Snark" -> " using Snark"

 op timeString: String -> String
 def timeString(runTime) =
   if runTime = "FM"
     then "."
   else " in "^runTime^" seconds."
   
 op proveWithHypothesis: Option String * Property * Properties * Spec * Option String * Properties * Spec *
                         % Properties * Spec *
                         String * LispCells * Bool * AnswerVar * String -> Bool

 def proveWithHypothesis(proofName, claim, hypothesis, spc, specName, baseHypothesis, baseSpc, % rewriteHypothesis,
                         % rewriteSpc,
                         proverName, proverOptions, includeBase, answerVariable, snarkLogFileName) =
   if proverName = "FourierM"
     then 
       proveWithHypothesisFM(proofName, claim, spc, specName, proverName, false)
   else
     if proverName = "Snark"
       then proveWithHypothesisSnark(proofName, claim, hypothesis, spc, specName, baseHypothesis, baseSpc, % rewriteHypothesis,
                                     % rewriteSpc,
                                     proverName, proverOptions, includeBase, answerVariable, snarkLogFileName)
     else
       let fmRes = proveWithHypothesisFM(proofName, claim, spc, specName, "FourierM", true) in
       fmRes ||
       proveWithHypothesisSnark(proofName, claim, hypothesis, spc, specName, baseHypothesis, baseSpc, % rewriteHypothesis,
                                % rewriteSpc,
                                "Snark", proverOptions, includeBase, answerVariable, snarkLogFileName)


 op proveWithHypothesisSnark: Option String * Property * Properties * Spec * Option String * Properties * Spec *
                         % Properties * % Spec *
                         String * LispCells * Bool * AnswerVar * String -> Bool

 def proveWithHypothesisSnark(proofName, claim, hypothesis, spc, specName, baseHypothesis, baseSpc, % rewriteHypothesis,
                              % rewriteSpc,
                              proverName, proverOptions, includeBase, answerVariable, snarkLogFileName) =
   let _ = debug("preovWithHyp") in
   let _ = if ~(proverName = "Snark") then writeLine(proverName ^ " is not supported; using Snark instead.") else () in
   let (claimType,claimName,_,_,_) = claim in
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
%   let snarkRewriteHypothesis = map (fn (prop) -> snarkRewrite(context, rewriteSpc, prop))
%                                     rewriteHypothesis in
   %let snarkHypothesis = map (fn (prop) -> snarkProperty(context, spc, prop)) hypothesis in
   let snarkSubsortHypothesis = snarkSubsortProperties(context, spc) in
   let snarkPropertyHypothesis = foldr (fn (prop, list) ->
					snarkPropertiesFromProperty(context, spc, prop)++list)
                                   [] hypothesis
   in
   let snarkHypothesis = snarkSubsortHypothesis ++ snarkPropertyHypothesis in
   let snarkConjecture =
     case answerVariable of
       | None -> snarkConjectureRemovePattern(context, spc, claim)
       | Some var -> snarkAnswer(context, spc, claim, [var]) in
   let snarkEvalForm = makeSnarkProveEvalForm(proverOptions, snarkSortDecls, snarkOpDecls,
					      snarkBaseHypothesis, % snarkRewriteHypothesis,
					      snarkHypothesis, snarkConjecture, snarkLogFileName) in
   let _ = if specwareDebug? then writeLine("Calling Snark by evaluating: ") else () in
   let _ = if specwareDebug? then LISP.PPRINT(snarkEvalForm) else Lisp.list [] in
   let result = Lisp.apply(Lisp.symbol("CL","FUNCALL"),
			   [Lisp.eval(Lisp.list [Lisp.symbol("CL","FUNCTION"),
						 Lisp.list [Lisp.symbol("SNARK","LAMBDA"),
							    Lisp.nil(),snarkEvalForm]])]) in
   let runTime = snarkRunTime() in
   let proved = anyToString(result) = (if caseSensitiveSubstrate? then ":proof-found" else ":PROOF-FOUND") in
   let _ = displayProofResult(proverName, proofName, claimType, claimName, specName, proved, runTime) in
     proved

 op proveWithHypothesisFM: Option String * Property * Spec * Option String * String * Bool -> Bool

 def proveWithHypothesisFM(proofName, claim, spc, specName, proverName, preProof?) =
   let _ = debug("preovWithHyp") in
   let (claimType,claimName,_,_,_) = claim in
   let def getClaimType(ct) = 
         case ct of
	   | Conjecture -> "Conjecture" 
	   | Theorem -> "Theorem" 
	   | Axiom -> "Axiom" in
   let claimType = getClaimType(claimType) in
   let context = emptyToFMContext in
   %let fmSubtypeHypothesis = fmSubtypeProperties(context, spc) in
   %let fmSubtypeHypothesis = [] in
   %let fmPropertyHypothesis = foldr (fn (prop, list) -> [toFMProperty(context, spc, prop)]++list) [] hypothesis in
   %let fmHypothesis = fmSubtypeHypothesis ++ fmPropertyHypothesis in
   %let fmConjecture = toFMProperty(context, spc, claim) in
   let runTime = "FM" in
   let proved = proveMSProb(spc, [], claim) in
   let _ = if proved || ~preProof?
	     then displayProofResult(proverName, proofName, claimType, claimName, specName, proved, runTime)
	   else proved in
   proved

 %print-clocks??
 op makeSnarkProveDecls: LispCells * LispCells * LispCells * LispCells % * LispCells
                           * LispCells * LispCell -> LispCell

 def makeSnarkProveDecls(proverOptions, snarkSortDecl, snarkOpDecls,
			 snarkBaseHypothesis, % snarkRewriteHypothesis,
			 snarkHypothesis, snarkConjecture) =
   let setOfSupportOn = Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(false)]) in
   let setOfSupportOff = Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(true)]) in
   let includeBase? = snarkBaseHypothesis ~= [] in
   
   Lisp.list
   [Lisp.list([Lisp.symbol("SNARK","INITIALIZE")]),
    Lisp.list([Lisp.symbol("SNARK","RUN-TIME-LIMIT"), Lisp.nat(10)]),
    Lisp.list([Lisp.symbol("SNARK","ASSERT-SUPPORTED"), Lisp.bool(false)]),
    Lisp.list([Lisp.symbol("SNARK","USE-LISP-TYPES-AS-SORTS"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-CODE-FOR-NUMBERS"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-NUMBERS-AS-CONSTRUCTORS"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-RESOLUTION"), Lisp.bool(true)]),
%    Lisp.list([Lisp.symbol("SNARK","USE-HYPERRESOLUTION"), Lisp.bool(true)]),
%    Lisp.list([Lisp.symbol("SNARK","USE-NEGATIVE-HYPERRESOLUTION"), Lisp.bool(true)]),

    Lisp.list([Lisp.symbol("SNARK","USE-PARAMODULATION"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-DEFAULT-ORDERING"), Lisp.bool(~includeBase?)]),
    Lisp.list([Lisp.symbol("SNARK","USE-LITERAL-ORDERING-WITH-RESOLUTION"),
               Lisp.quote(Lisp.symbol("SNARK","LITERAL-ORDERING-A"))]),
    Lisp.list([Lisp.symbol("SNARK","USE-LITERAL-ORDERING-WITH-PARAMODULATION"),
               Lisp.quote(Lisp.symbol("SNARK","LITERAL-ORDERING-A"))]),
    Lisp.list([Lisp.symbol("SNARK","USE-LITERAL-ORDERING-WITH-HYPERRESOLUTION"),
               Lisp.quote(Lisp.symbol("SNARK","LITERAL-ORDERING-P"))]),
    Lisp.list([Lisp.symbol("SNARK","USE-LITERAL-ORDERING-WITH-NEGATIVE-HYPERRESOLUTION"),
               Lisp.quote(Lisp.symbol("SNARK","LITERAL-ORDERING-N"))]),
    Lisp.list([Lisp.symbol("SNARK","DECLARE-FUNCTION"),
               Lisp.quote(Lisp.symbol("SNARK","-")),
               Lisp.nat(2),
               Lisp.symbol("KEYWORD","ALIAS"),
               Lisp.quote(Lisp.symbol("SNARK","MINUSBINARY"))]),
    Lisp.list([Lisp.symbol("SNARK","DECLARE-ORDERING-GREATERP"),
               Lisp.quote(Lisp.symbol("SNARK","<")),
               Lisp.quote(Lisp.symbol("SNARK","=<"))]),
    Lisp.list([Lisp.symbol("SNARK","DECLARE-ORDERING-GREATERP"),
               Lisp.quote(Lisp.symbol("SNARK",">")),
               Lisp.quote(Lisp.symbol("SNARK","=>"))]),

    Lisp.list([Lisp.symbol("SNARK","USE-CONDITIONAL-ANSWER-CREATION"), Lisp.bool(true)]),
    Lisp.list([Lisp.symbol("SNARK","USE-WELL-SORTING"), Lisp.bool(false)])]
   Lisp.++ (Lisp.list snarkSortDecl)
   Lisp.++ (Lisp.list snarkOpDecls)
   Lisp.++ (Lisp.list proverOptions)
   Lisp.++ (Lisp.list [setOfSupportOn])
   Lisp.++ (Lisp.list snarkBaseHypothesis)
%   Lisp.++ (Lisp.list snarkRewriteHypothesis)
%% ??   Lisp.++ (Lisp.list [setOfSupportOff])
   Lisp.++ (Lisp.list proverOptions)
   Lisp.++ (Lisp.list baseAxioms)
   Lisp.++ (Lisp.list [%Lisp.list([Lisp.symbol("SNARK","DECLARE-PREDICATE-SYMBOL"),
                                     %           Lisp.quote(Lisp.symbol("SNARK",">="))]),
                                     Lisp.list([Lisp.symbol("SNARK","DECLARE-ORDERING-GREATERP"),
                                                Lisp.quote(Lisp.symbol("SNARK","MINUSBINARY")),
                                                Lisp.quote(Lisp.symbol("SNARK","+")),
                                               % Lisp.quote(Lisp.symbol("SNARK","Integer.one")),
                                                Lisp.quote(Lisp.nat(1)),
                                               % Lisp.quote(Lisp.symbol("SNARK","Integer.zero")),
                                                Lisp.quote(Lisp.nat(0))]),
                       %                       Lisp.list([Lisp.symbol("SNARK","DECLARE-ORDERING-GREATERP"),
                                                          %                                  Lisp.quote(Lisp.symbol("SNARK","GTE")),
                                                          %                                  Lisp.quote(Lisp.symbol("SNARK","=<"))]),
Lisp.list([Lisp.symbol("SNARK","DECLARE-ORDERING-GREATERP"),
           Lisp.quote(Lisp.symbol("SNARK","embed__Cons")),
           Lisp.quote(Lisp.symbol("SNARK","List.length"))]),
Lisp.list([Lisp.symbol("SNARK","DECLARE-ORDERING-GREATERP"),
           Lisp.quote(Lisp.symbol("SNARK","embed__Cons")),
           Lisp.quote(Lisp.symbol("SNARK","+"))]),
Lisp.list([Lisp.symbol("SNARK","DECLARE-ORDERING-GREATERP"),
           Lisp.quote(Lisp.symbol("SNARK","Nat.succ")),
           Lisp.quote(Lisp.symbol("SNARK","+"))]),
Lisp.list([Lisp.symbol("SNARK","DECLARE-ORDERING-GREATERP"),
           Lisp.quote(Lisp.symbol("SNARK","embed__Cons")),
           Lisp.quote(Lisp.nat(1))])])

   Lisp.++ (Lisp.list snarkHypothesis)
   Lisp.++ (Lisp.list [snarkConjecture])

 op makeSnarkProveEvalForm: LispCells * LispCells * LispCells * LispCells % * LispCells
                           * LispCells * LispCell * String -> LispCell

 def makeSnarkProveEvalForm(proverOptions, snarkSortDecl, snarkOpDecls, snarkBaseHypothesis,
			    % snarkRewriteHypothesis,
			    snarkHypothesis, snarkConjecture, snarkLogFileName) =
   %let _ = if specwareDebug? then toScreen("Proving snark fmla: ") else () in
   %let _ = if specwareDebug? then LISP.PPRINT(snarkConjecture) else Lisp.list [] in
   %let _ = if specwareDebug? then writeLine(" using: ") else () in
   %let _ = if specwareDebug? then LISP.PPRINT(Lisp.list(snarkHypothesis)) else Lisp.list [] in
   let snarkProverDecls = makeSnarkProveDecls(proverOptions, snarkSortDecl, snarkOpDecls,
					      snarkBaseHypothesis, % snarkRewriteHypothesis,
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
				 Lisp.list[]],
		      Lisp.list [Lisp.symbol("CL-USER","*PRINT-LENGTH*"),
				 Lisp.list[]]],
	   Lisp.list([Lisp.symbol("CL","WRITE-LINE"), Lisp.string("Snark is invoked by evaluating:")]),
	   Lisp.list([Lisp.symbol("CL","PPRINT"),
		      Lisp.quote(Lisp.list[Lisp.symbol("CL","LET"), Lisp.list []] Lisp.++ snarkProverDecls)])
	  ]
	  Lisp.++ snarkProverDecls
		    ]

endspec


