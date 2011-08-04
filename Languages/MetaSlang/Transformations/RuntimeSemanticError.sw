SemanticError qualifying
spec
import /Library/Legacy/Utilities/System

%% Check 1 in numToCheck
op numToCheck: Nat = 10

op randomCheck?(): Bool =
   random numToCheck = 0

op [a] randomlyCheckPred(val_to_check: a, pred: a -> Bool): Bool =
  randomCheck?()
    => pred val_to_check

op [a] checkPredicate(val_to_check: a, pred:a -> Bool, err_msg_fn: a -> String): () =
   if randomlyCheckPred(val_to_check, pred) then ()
   else warn(err_msg_fn val_to_check^"\n"^anyToString val_to_check)

op [a] checkPredicates(val_to_check: a, pred_msg_prs: List((a -> Bool) * (a -> String))): () =
  app (fn (pred, err_msg_fn) -> checkPredicate(val_to_check, pred, err_msg_fn))
    pred_msg_prs

end-spec
