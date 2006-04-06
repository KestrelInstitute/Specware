
%% Temporary hack until real version is installed...

SpecCalc qualifying spec
  import Signature

  def SpecCalc.evaluateOpRefine args pos = {
    unitId <- getCurrentUID;
    print (";;; Elaborating OpRefine at " ^ (uidToString unitId) ^ "\n");
    raise (TypeCheck (pos, "OpRefine not yet defined!"))
    }
endspec

