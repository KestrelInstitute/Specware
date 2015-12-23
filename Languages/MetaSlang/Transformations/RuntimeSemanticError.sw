(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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

op [a] assurePredicate(val_to_check: a, pred:a -> Bool, fix_fn: a -> a): a =
   if randomlyCheckPred(val_to_check, pred) then val_to_check
   else fix_fn val_to_check

op [a] checkPredicateComplain(val_to_check: a, pred:a -> Bool, err_msg_fn: a -> String): a =
   if randomlyCheckPred(val_to_check, pred) then val_to_check
   else (warn(err_msg_fn val_to_check^"\n"^anyToString val_to_check);
         val_to_check)

op [a] checkPredicateFail(val_to_check: a, pred:a -> Bool, err_msg_fn: a -> String): a =
   if randomlyCheckPred(val_to_check, pred) then val_to_check
   else (warn("failed: val=" ^ anyToString val_to_check ^ "\n" ^ " pref=" ^ anyToString pred ^ "\n");
         throwToRestart(err_msg_fn val_to_check^"\n"^anyToString val_to_check^"\n"^anyToString pred^"\n"))

op restartCount: Nat = 0

op [a] catchAndRestart: a -> a
op [a] throwToRestart: String -> a
op [a] catchAndRestartChangeMode: a -> a

op [a] catchRuntimeMonitorError: a * a -> a
op [a] catchRuntimeMonitorError1: a * a -> a

op [a] returnMostPopular(l: List a): a =
  let def addOrNew(groups, x) =
        case groups of
          | [] -> [[x]]
          | g :: r_groups ->
            if x = head g then (x :: g) :: r_groups
              else g :: addOrNew(r_groups, x)
  in
  let grouped = foldl addOrNew [] l in
  case grouped of
    | [x :: _] -> x                     % All equal
    | _ ->
  let max_size = foldl (fn (m, g) -> max(length g, m)) 0 grouped in
  let max_grouped = filter (fn g -> length g = max_size) grouped in
  case max_grouped of
    | [x :: _] -> (warn("Multiple results. Returning most popular.");
                   x)
    | (x :: _) :: _ ->
      (warn("Multiple results of equal popularity. Returning first.");
       x)

#translate Lisp 

-verbatim

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Verbatim text from language morphism in RuntimeSemanticError.sw

(define-condition semantic-error (error)
  ((text :initarg :text :reader text)))

  (defun throwToRestart (text)
  (format t "semantic error: ~a~%" text)
  (error 'semantic-error))

(defmacro catchAndRestart (expr)
  `(let ((f (lambda () ,expr)))
     (let ((restartCount 0)
           (done? nil)
           (result nil))
       (loop until done?
            do (handler-case (progn (setq result (funcall f))
                                    (setq done? t))
                 (semantic-error ()
                   (format t "Failed with restartCount ~a~%Trying next representation..." restartCount)
                   (incf restartCount))))
       result)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
-end

-morphism
 op SemanticError.catchAndRestart -> SemanticError::catchAndRestart
 op SemanticError.throwToRestart  -> SemanticError::throwToRestart

#end

end-spec
