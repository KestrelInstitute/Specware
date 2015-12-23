(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying spec 
%  import translate /Languages/SpecCalculus/Semantics/Specware by {Set._ +-> SWSet._} % for the Specware monad
  import /Provers/ProofChecker/TranslateMSToPC[/Provers/ProofChecker/Refinement]
  import /Provers/ProofGenerator/ContextProofsI
  import /Provers/ProofDebugger/Print[/Provers/ProofChecker/Refinement]%, /Provers/ProofDebugger/ProofPrinter[/Provers/ProofChecker/Refinement]
% import /Provers/ProofDebugger/Printer
 % import Prove
  import UnitId
  import /Library/IO/Primitive/IO
  import UnitId/Utilities                                    % for uidToString, if used...

  def SpecCalc.evaluateProofCheck (claimName, term, proverName, assertions, possibleOptions, baseOptions) pos =
    {
     (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo term;

     value <- return (coerceToSpec value);

     valueName <- return (SpecTermToSpecName(term));

     result <- (case value of
		  | Spec spc -> evaluateSpecProofCheck (claimName, spc, valueName, proverName, assertions, possibleOptions, baseOptions) 
		  | Other other -> evaluateOtherProofCheck (claimName, other, valueName, proverName, assertions, possibleOptions, baseOptions) pos
		  | _ -> raise (Proof (pos, "Argument to proofCheck command is neither coerceable to a spec nor Other.")));
     return (result, timeStamp, depUIDs)
    }

  op evaluateSpecProofCheck: PCClaimName * Spec * Option String * ProverName * Assertions * ProverOptions * ProverBaseOptions -> SpecCalc.Env Value
  def evaluateSpecProofCheck(Wellformed, spc, specName, proverName, assertions, possibleOptions, baseOptions) =
    {
      unitId <- getCurrentUnitId;
      ctxt <- specToContext spc;
      %fail "foo";
      ctxtProof <- return (contextProof ctxt);
      checkedProof <-  return (runCheck ctxtProof);
      proofChecked <-
      case checkedProof of
	% Actually ckeck that the judgement is well formed context of ctxt.
	| RETURN j -> {SpecCalc.print (ProofDebugger.printJudgement(j)); (return true)}
	| THROW exc -> {SpecCalc.print (ProofDebugger.printFailure(exc)); (return false)};

      SpecCalc.print (ProofDebugger.printContext ctxt);
      SpecCalc.print (printProof ctxtProof);
      return (Proof {status = if proofChecked then Proved else Unproved,
		     unit = unitId})
    }

endspec
