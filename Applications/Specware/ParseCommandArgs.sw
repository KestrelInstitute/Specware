SpecwareShell qualifying spec

import /Library/Legacy/Utilities/IO      % read
import /Library/Legacy/Utilities/System  % writeLine

type Chars = List Char

type CommandArgs = List CommandArg
type CommandArg  = | String String
                   | Name   String
                   | Number Integer
                   | List   CommandArgs

type Result a = | Good  a
                | Error String

op parseCommandArgs (s : String) : Result CommandArgs =
 let

   def name_char? c =
     isAlphaNum c || c in? [#-, #/, ##, #.] % include chars that often appear in filenames

   def parse_string (unread_chars, rev_str_chars) : Result (Chars * CommandArg) =
     case unread_chars of
       | [] -> Error "String not terminated by quote"
       | #" :: chars ->
         Good (chars, String (implode (reverse rev_str_chars)))
       | c :: chars ->
         parse_string (chars, c :: rev_str_chars)

   def parse_name (unread_chars, rev_name_chars) =
     case unread_chars of
       | [] ->
         Good ([], Name (implode (reverse rev_name_chars)))
       | c :: chars ->
         if name_char? c then
           parse_name (chars, c :: rev_name_chars)
         else
           Good (unread_chars, Name (implode (reverse rev_name_chars)))

   def parse_number (unread_chars, rev_number_chars) =
     case unread_chars of
       | [] ->
         let n_str = implode (reverse rev_number_chars) in
         if intConvertible n_str then
           Good (unread_chars, Number (stringToInt n_str))
         else
           Error ("Cannot parse number: " ^ implode unread_chars)
       | c :: chars ->
         if isNum c then
           parse_number (chars, c :: rev_number_chars)
         else
           let n_str = implode (reverse rev_number_chars) in
           if intConvertible n_str then
             Good (unread_chars, Number (stringToInt n_str))
           else
             Error ("Cannot parse number: " ^ implode unread_chars)

   def parse_list (unread_chars, rev_elements) =
     case unread_chars of
       | [] -> Error "List not terminated by closing bracket"
       | #, :: chars ->
         parse_list (chars, rev_elements)
       | #] :: chars ->
         Good (chars, List (reverse rev_elements))
       | _ ->
         case parse_arg unread_chars of
           | Good (unread_chars, element) ->
             parse_list (unread_chars, element :: rev_elements)
           | error ->
             error

   def parse_arg unread_chars =
     case unread_chars of
       | [] -> Error "looking for an arg past end of input"
       | c :: chars -> 
         case c of 
           | #\s -> parse_arg chars
           | #" -> parse_string (chars, [])
           | #[ -> parse_list   (chars, [])
           | _ ->
             if isNum c then
               parse_number (unread_chars, [])
             else if name_char? c then
               parse_name (unread_chars, [])
             else
               Error ("cannot parse arg: " ^ implode unread_chars)

   def aux (unread_chars, rev_args) : Result (Chars * CommandArgs) =
     case parse_arg unread_chars of
       | Good (unread_chars, arg) ->
         let rev_args = arg :: rev_args in
         (case unread_chars of
            | [] -> Good ([], reverse rev_args)
            | _ ->
              aux (unread_chars, rev_args))
       | Error msg -> Error msg
         
 in
 case aux (explode s, []) of
   | Good ([], args) ->
     Good args
   | Error msg ->
     Error msg

op dispatch (cmd : String, args : CommandArgs) : () =
 let

   def cd_0 () =
     let current_dir = lispEval "(Specware::current-directory)" in
     let _ = writeLine current_dir in
     ()

   def cd_1 (dir) =
     let cmd = "(Specware::cd " ^ dir ^ ")" in
     let _ = lispEval cmd in
     ()

   def cinit () =
     let _ = reinitializeSpecware () in
     ()

   def com () =
     let cmd =
         "(let ((cl:*package* (find-package \"CL-USER\")))
           (multiple-value-bind (command pos)
              (read-from-string argstr)
              (if (fboundp command)
                 (let ((com-argstr (subseq argstr pos)))
                  (if (string= com-argstr \"\")
                     (funcall command)
                     (funcall command com-argstr)))
                 (format t \"Unknown command: ~a.\" command)))))"
     in
     let _ = lispEval cmd in
     ()

   def ctext_0 () =
     let cmd =
         "(if cl-user::*current-swe-spec* 
             (format t \"~&Current context: ~a\" cl-user::*current-swe-spec*)
             (format t \"~&Current context: Base Spec\")))"
     in
     let _ = lispEval cmd in
     ()

   def ctext_1 (x) =
     if x = "none" then
       let cmd = 
           "(progn 
               (setq cl-user::*current-swe-spec* nil)
               (format t \"~&Subsequent evaluation commands will import just the base spec.~%\"))"
       in
       let _ = lispEval cmd in
       ()
     else
       let cmd = "(cl-user::swe-spec argstr)" in
       let _ = lispEval cmd in
       ()
       
   def eval_0 (x) =
     let cmd = 
         "(let ((cl-user::*swe-use-interpreter?* t)
                (argstr *last-eval-expr* )
                (cl-user::*expr-begin-offset* (if (eq command 'e) -12 -9)))
            (if (null argstr)
               (warn \"No previous eval command.\")
               (progn (setq *last-eval-expr* argstr)
                  (cl-user::swe argstr))))"
     in
     let _ = lispEval cmd in
     ()

   def eval_1 (argstr) =
     let cmd = 
         "(let ((cl-user::*swe-use-interpreter?* t)
                (argstr " ^ argstr ^ ")
                (cl-user::*expr-begin-offset* (if (eq command 'e) -12 -9)))
             (setq *last-eval-expr* argstr)
             (cl-user::swe argstr))"
     in
     let _ = lispEval cmd in
     ()

   def eval_lisp_0 () =
     let cmd = 
         "(let ((cl-user::*swe-use-interpreter?* nil)
                (argstr *last-eval-expr* )
                (cl-user::*expr-begin-offset* (if (eq command 'el) -11 -4)))
               (if (null argstr)
                  (warn \"No previous eval command.\")
                  (progn 
                     (setq *last-eval-expr* argstr)
                     (cl-user::swe argstr))))"
     in
     let _ = lispEval cmd in
     ()

   def eval_lisp_1 (argstr) =
     let cmd = 
         "(let ((cl-user::*swe-use-interpreter?* nil)
                (argstr " ^ argstr ^ ")
                (cl-user::*expr-begin-offset* (if (eq command 'el) -11 -4)))
               (setq *last-eval-expr* argstr)
               (cl-user::swe argstr))"
     in
     let _ = lispEval cmd in
     ()

   def gen_acl2 () =
     let cmd = 
         "(let ((TypeObligations::generateTerminationConditions?  nil)
                (TypeObligations::generateExhaustivityConditions? t)
                (Simplify::simplifyUsingSubtypes?                 t)
                (Prover::treatNatSpecially?                       nil)
                (Utilities::namedTypesRaised?                     t))
             (cl-user::gen-acl2 argstr))"
     in
     let _ = lispEval cmd in
     ()

   def gen_coq_0 () =
     let cmd = 
         "(let ((TypeObligations::generateTerminationConditions?  nil)
                (TypeObligations::generateExhaustivityConditions? t)
                (Simplify::simplifyUsingSubtypes?                 t)
                (Prover::treatNatSpecially?                       nil)
                (Utilities::namedTypesRaised?                     t)
                (uid (if (not (null cl-user::*last-unit-Id-_loaded*))
                         cl-user::*last-unit-Id-_loaded*
                         (progn (format t \"No previous unit processed~%\")
                                   nil))))))
           (unless (null uid)
             (setq cl-user::*last-unit-Id-_loaded* uid)
             (CoqTermPrinter::printUIDToCoqFile uid)))"
     in
     let _ = lispEval cmd in
     ()

   def gen_coq_1 (argstr) =
     let cmd = 
         "(let ((TypeObligations::generateTerminationConditions?  nil)
                (TypeObligations::generateExhaustivityConditions? t)
                (Simplify::simplifyUsingSubtypes?                 t)
                (Prover::treatNatSpecially?                       nil)
                (Utilities::namedTypesRaised?                     t)
                (uid " ^ argstr ^ "))
           (setq cl-user::*last-unit-Id-_loaded* uid)
           (CoqTermPrinter::printUIDToCoqFile uid))"
     in
     let _ = lispEval cmd in
     ()
         

   def gen_obligs () =
     let cmd =
         "(let ((TypeObligations::generateTerminationConditions? nil)
                (TypeObligations::generateExhaustivityConditions? t)
                (Simplify::simplifyUsingSubtypes? t)
                (Prover::treatNatSpecially? nil)
                (Utilities::namedTypesRaised? t)
             (uid (if (not (null argstr))
                     argstr
                     (if (not (null cl-user::*last-unit-Id-_loaded*))
                            cl-user::*last-unit-Id-_loaded*
                            (progn (format t "No previous unit processed~%")
                               nil)))))
             (unless (null uid)
                (setq cl-user::*last-unit-Id-_loaded* uid)
                (IsaTermPrinter::printUIDtoThyFile-3 uid t t))))" ; do simplify
     in
     let _ = lispEval cmd in
     ()


   def gen_obligs_no_simp () =
     (*
     (let ((TypeObligations::generateTerminationConditions? nil)
             (TypeObligations::generateExhaustivityConditions? t)
             (Simplify::simplifyUsingSubtypes? t)
             (Prover::treatNatSpecially? nil)
             (Utilities::namedTypesRaised? t)
             (uid (if (not (null argstr))
                     argstr
                     (if (not (null cl-user::*last-unit-Id-_loaded*))
                            cl-user::*last-unit-Id-_loaded*
                            (progn (format t "No previous unit processed~%")
                               nil)))))
             (unless (null uid)
                (setq cl-user::*last-unit-Id-_loaded* uid)
                (IsaTermPrinter::printUIDtoThyFile-3 uid t nil))))  ; don't simplify
     *)
    ()

   def gen_haskell () =
     (*
     (let ((uid (if (not (null argstr))
                   argstr
                   (if (not (null cl-user::*last-unit-Id-_loaded*))
                          cl-user::*last-unit-Id-_loaded*
                          (progn (format t "No previous unit processed~%")
                             nil)))))
             (unless (null uid)
                (setq cl-user::*last-unit-Id-_loaded* uid)
                (Haskell::printUIDtoHaskellFile-3 uid nil t))))
     *)
    ()

   def gen_haskell_top () =
     (*
     (let ((uid (if (not (null argstr))
                   argstr
                   (if (not (null cl-user::*last-unit-Id-_loaded*))
                          cl-user::*last-unit-Id-_loaded*
                          (progn (format t "No previous unit processed~%")
                             nil)))))
             (unless (null uid)
                (setq cl-user::*last-unit-Id-_loaded* uid)
                (Haskell::printUIDtoHaskellFile-3 uid t t))))
     *)
    ()

   def help () =
     (*
     (let ((cl-user::*sw-help-strings*
              (append *sw-shell-help-strings*
                 (if *developer?*
                    *sw-shell-dev-help-strings*
                    '()))))
      (cl-user::sw-help argstr) ; refers to cl-user::*sw-help-strings*
     *)
    ()

   def lisp () =
      (*
      (if (null argstr)
         (format t "Error: ~a requires an argument" *raw-command*)
         (with-break-possibility (lisp-value (multiple-value-list (eval (read-from-string argstr)))))))
     *)
    ()
      
   def obligs () =
     (*
      (cl-user::show (concatenate 'string "\"obligations "
                        (if (null argstr)
                           cl-user::*last-unit-Id-_loaded*
                           (cl-user::norm-unitid-str argstr))
                        "\""))
     *)
    ()
      
  def trace_rewrites () =
    let cmd = 
        "(progn
             (setq MetaSlangRewriter::traceRewriting 2)
             (format t \"Rewrite tracing turned on.\")
             (when (and (not (null argstr))
                        (string= \"t\" (cl-user::strip-extraneous argstr)))
                (setq MetaSlangRewriter::debugApplyRewrites? t)))"
     in
     let _ = lispEval cmd in
     ()


   def transform () = 
     (*
     (let* ((spec-uid (cl-user::norm-unitid-str argstr))
              (val (cdr (Specware::evaluateUnitId (or spec-uid cl-user::*last-unit-Id-_loaded*)))))
              (if (or (null val) (not (eq (car val) ':|Spec|)))
                 (format t "Not a spec!")
                 (let ((spc (cdr val)))
                  (when spec-uid (setq cl-user::*last-unit-Id-_loaded* spec-uid))
                  (initialize-transform-session spc)
                  (setq *current-command-processor* 'process-transform-shell-command)
                  (format t "Entering Transformation Construction Shell")))
              (values)))
     *)
    ()

   def untrace_rewrites () =
     (*
     (setq MetaSlangRewriter::traceRewriting 0)
     (format t "Rewrite tracing turned off.")
     (setq MetaSlangRewriter::traceRewriting 0)
     (setq MetaSlangRewriter::debugApplyRewrites? nil)
     (HigherOrderMatching::turnOffHOMatchTracing-0)
     *)
    ()

   def uses () =
     (*
     (if (null argstr)
        (warn "No identifier.")
        (let* ((inp_elts (String-Spec::splitStringAt-2 argstr " "))
                 (ids (String-Spec::splitStringAt-2 (car inp_elts) "."))
                 (qid (if (null (cdr ids))
                         (MetaSlang::mkUnQualifiedId (car ids))
                         (MetaSlang::mkQualifiedId-2 (car ids) (cadr ids))))
                 (spc (cl-user::sc-val (if (null (cadr inp_elts))
                                          cl-user::*last-unit-Id-_loaded*
                                          (cl-user::norm-unitid-str (cadr inp_elts)))))
                 (results (Refs::usedBy_*-3 (list qid) (list qid) spc))
                 (cl:*print-length* nil))
           ;(format t "qid: ~a~%spc: ~a~%" qid (cadr inp_elts))
           (when (not (null (car results)))
              (format t "Ops: ~a~%" (reverse (map 'list #'MetaSlang::PrintQualifiedId (car results)))))
           (when (not (null (cdr results)))
              (format t "Types: ~a~%" (reverse (map 'list #'MetaSlang::PrintQualifiedId (cdr results)))))
           (values)))
        *)
        ()
     
 in
 case (cmd, args) of
   | ("cd",         [])          -> cd    ()
   | ("cinit",      [])          -> cinit ()
   | ("ctext",      [])          -> ctext ()
   | ("dir",        [Name name]) -> (cl-user::ls   name)
   | ("dir",        [])          -> (cl-user::ls   "")
   | ("dirr",       [Name name]) -> (cl-user::dirr name)
   | ("dirr"        [])          -> (cl-user::dirr "")
   | ("e",          [Name name]) -> eval_1 (name)
   | ("e",          [])          -> eval_0 ()
   | ("eval",       [Name name]) -> eval_1 (name)
   | ("eval"        [])          -> eval_0 ()

   | "eval-lisp"               -> eval_lisp ()
   | "el"                      -> eval_lisp ()

   | "help"                    -> help  ()
   | "ls"                      -> (cl-user::ls     (or argstr "")))
   | "path  "                  -> (cl-user::swpath argstr))
   | "p"                       -> (cl-user::sw     argstr) 
   | "proc "                   -> (cl-user::sw     argstr) 
   | "pwd"                     -> (princ (Specware::current-directory)) 
   | "reproc"                  -> (let ((cl-user::*force-reprocess-of-unit* t)) (cl-user::sw     argstr)) 
   | "rp"                      -> (let ((cl-user::*force-reprocess-of-unit* t)) (cl-user::sw     argstr)) 
   | "show  "                  -> (cl-user::show     argstr) 
   | "showx "                  -> (cl-user::showx    argstr) 
   | "showdeps"                -> (cl-user::showdeps argstr) 
   | "showimports"             -> (cl-user::showimports argstr) 
   | "showdata"                -> (cl-user::showdata argstr) 
   | "showdatav"               -> (cl-user::showdatav argstr) 
   | "checkspec"               -> (cl-user::checkspec argstr) 

   | "gen-acl2"                -> gen_acl2 ()

   | "gen-coq"                 -> gen_coq ()

   | "gen-c"                   -> (cl-user::swc    argstr) 
   | "gen-c-thin"              -> (cl-user::gen-c-thin    argstr) 

   | "gen-java"                -> (cl-user::swj    argstr) 

   | "gen-haskell"             -> gen_haskell     ()
   | "gen-h"                   -> gen_haskell     ()
   | "gen-haskell-top"         -> gen_haskell_top ()
   | "gen-ht"                  -> gen_haskell_top ()

   | "gen-lisp"                -> (cl-user::swl argstr)
   | "gen-l"                   -> (cl-user::swl argstr)
   | "gen-lisp-top"            -> (let ((cl-user::*slicing-lisp?* t)) (cl-user::swl argstr))
   | "gen-lt"                  -> (let ((cl-user::*slicing-lisp?* t)) (cl-user::swl argstr))
   | "lgen-lisp"               -> (cl-user::swll   argstr)

   | "make"                    -> (if (null argstr) (cl-user::make) (cl-user::make argstr)))

   | "oblig"                   -> obligs ()
   | "obligations"             -> obligs ()
   | "obligs"                  -> obligs ()

   | "gen-obligations"         -> gen-obligs ()
   | "gen-oblig"               -> gen-obligs ()
   | "gen-obligs"              -> gen-obligs ()

   | "gen-obligations-no-simp" -> gen-obligs_no_simp ()
   | "gen-oblig-no-simp"       -> gen-obligs_no_simp ()
   | "gen-obligs-no-simp"      -> gen-obligs_no_simp ()

   | "pc"                      -> (cl-user::swpc argstr)
   | "proofcheck"              -> (cl-user::swpc argstr)

   | "prove"                   -> (cl-user::sw (concatenate 'string "prove " argstr)) 
   | "prwb"                    -> (if argstr (cl-user::swprb argstr) (cl-user::swprb)))

   | "punits"                  -> (cl-user::swpf   argstr))
   | "lpunits"                 -> (cl-user::lswpf  argstr)) ; No local version yet

   | "transform"               -> transform () 

   | "trace-eval"              -> (setq MSInterpreter::traceEval? t)   (format t "Tracing of eval turned on.")        
   | "untrace-eval"            -> (setq MSInterpreter::traceEval? nil) (format t "Tracing of eval turned off.")       

   | "uses"                    -> uses ()

   %% Non-user commands

   | "cf"                      -> (cl-user::cf argstr))

   | "cl"                      -> (with-break-possibility (cl-user::cl argstr)))

   | "com"                     -> com ()

   | "dev"                     -> (princ (if argstr   (setq *developer?* (not (member argstr '("nil" "NIL" "off") :test 'string=)))  *developer?*))

   | "lisp"                    -> lisp ()
   | "l"                       -> lisp ()

   | "f-b"                     -> (when (fboundp 'cl-user::f-b)   (funcall 'cl-user::f-b argstr)))
   | "f-unb"                   -> (when (fboundp 'cl-user::f-unb) (funcall 'cl-user::f-unb (or argstr ""))))

   | "ld"                      -> (with-break-possibility (cl-user::ld argstr)))

   | "pa"                      -> (cl-user::pa argstr))

   | "set-base"                -> (cl-user::set-base argstr))

   | "show-base-unit-id"       -> (cl-user::show-base-unit-id))

   | "swdbg"                   -> (if argstr (cl-user::swdbg argstr) (cl-user::swdbg)))

   | "tr"                      -> (cl-user::tr argstr))
   | "untr"                    -> (cl-user::untr))

   | "trace-rewrites"          -> trace_rewrites   ()
   | "trr"                     -> trace_rewrites   ()
   | "untrace-rewrites"        -> untrace_rewrites ()
   | "untrr"                   -> untrace_rewrites ()

   | "wiz"                     -> (if argstr (cl-user::wiz   argstr) (cl-user::wiz)))

   | _ ->
     if constantp? cmd && args = [] then
       cmd
     else
       let _ = writeLine ("Unknown command `" ^ anyToString cmd ^ "'. Type `help' to see available commands.") in
       cmd


op new_shell (cmd : String, args_str : String) : () =
 let _ = writeLine ("cmd:  " ^ cmd)  in
 let _ = writeLine ("args: " ^ args_str) in
 case parse_command_args args_str of
   | Good args ->
     let _ = writeLine ("args: " ^ anyToString args) in
     dispatch (cmd, args)
   | Error msg ->
     writeLine ("confusion: " ^ msg)

end-spec

