(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% Temporary test function for translation.

Translate qualifying spec
  import translate /Languages/SpecCalculus/Semantics/Specware by {Set._ +-> SWSet._} % for the Specware monad
  
  import TranslateMSToPC[Refinement]
  import ../ProofGenerator/ContextProofsI

  op test : String -> Bool
  def test path =
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      catch {
        (val,_,_) <- evaluateUID position unitId;
        case val of
          | Spec spc -> {
              ctxt <- specToContext spc;
              print (printContext ctxt);
              return ()
            }
          | _ -> {
              print "Unit is not a spec";
              return ()
            }
      } (fileNameHandler unitId);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler)

  op testProofGen: String -> Bool
  def testProofGen path =
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      catch {
        (val,_,_) <- evaluateUID position unitId;
        case val of
          | Spec spc -> {
              ctxt <- specToContext spc;
	      %fail "foo";
	      ctxtProof <- return (contextProof ctxt);
	      checkedProof <- return (check ctxtProof);
	      case checkedProof of
		% Actually ckeck that the judgement is well formed context of ctxt.
		| RETURN j -> print (printJudgement(j))
		| THROW exc -> print (printFailure(exc));
              print (printContext ctxt);
              return ()
            }
          | _ -> {
              print "Unit is not a spec";
              return ()
            }
      } (fileNameHandler unitId);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler)

endspec

