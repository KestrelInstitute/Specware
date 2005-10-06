SpecCalc qualifying spec 
%  import translate /Languages/SpecCalculus/Semantics/Specware by {Set._ +-> SWSet._} % for the Specware monad
  import /Provers/ProofChecker/TranslateMSToPC[/Provers/ProofChecker/Refinement]
  import /Provers/ProofGenerator/ContextProofsI
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
		  | Spec spc -> evaluateSpecProofCheck (claimName, spc, valueName, proverName, assertions, possibleOptions, baseOptions) pos
		  | Other other -> evaluateOtherProofCheck (claimName, other, valueName, proverName, assertions, possibleOptions, baseOptions) pos
		  | _ -> raise (Proof (pos, "Argument to proofCheck command is neither coerceable to a spec nor Other.")));
     return (result, timeStamp, depUIDs)
    }

  op evaluateSpecProofCheck: PCClaimName * Spec * Option String * ProverName * Assertions * ProverOptions * ProverBaseOptions -> Position -> SpecCalc.Env Value
  def evaluateSpecProofCheck(Wellformed, spc, specName, proverName, assertions, possibleOptions, baseOptions) pos =
    {
      unitId <- getCurrentUnitId;
      ctxt <- specToContext spc;
      %fail "foo";
      ctxtProof <- return (contextProof ctxt);
      checkedProof <- return (check ctxtProof);
      proofChecked <-
      case checkedProof of
	% Actually ckeck that the judgement is well formed context of ctxt.
	%| RETURN j -> {print (printJudgement(j)); (return true)}
	%| THROW exc -> {print (printFailure(exc)); (return false)};
	| RETURN j ->  return true
	| THROW exc -> return false;
      % print (printContext ctxt);
      return (Proof {status = if proofChecked then Proved else Unproved,
		     unit = unitId})
    }

endspec
