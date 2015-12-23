(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SpecwareShell qualifying spec

import /Library/Legacy/Utilities/IO      % read
import /Library/Legacy/Utilities/System  % writeLine

import TypedValues
import CommandParser
import SystemCommands
import SpecwareCommands
import CodeGenCommands
import ProverCommands
import WizardCommands

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op dispatch (cmd : String, args : TypedValues, ctxt : CommandContext) 
 : Result (TypedValues * CommandContext) =
 case (cmd, args) of
  (*
   | ("cd",         [])          -> showCurrentDirectory ctxt
   | ("cd",         [Name dir]   -> connectToDirectory   (dir, ctxt)
   | ("ls",         [])          -> listFileInDirectory  ("",  false, ctxt)
   | ("ls",         [Name dir])  -> listFileInDirectory  (dir, false, ctxt)
   | ("dir",        [])          -> listFileInDirectory  ("",  false, ctxt)
   | ("dir",        [Name dir])  -> listFileInDirectory  (dir, false, ctxt)
   | ("dirr"        [])          -> listFileInDirectory  ("",  true,  ctxt)
   | ("dirr",       [Name dir])  -> listFileInDirectory  (dir, true,  ctxt)

   | ("cinit",      [])          -> cinit ()
   | ("ctext",      [])          -> ctext ()
   | ("e",          [Name name]) -> eval_1 (name)
   | ("e",          [])          -> eval_0 ()
   | ("eval",       [Name name]) -> eval_1 (name)
   | ("eval"        [])          -> eval_0 ()

   | "eval-lisp"                 -> eval_lisp ()
   | "el"                        -> eval_lisp ()

   | "help"                      -> help  ()
   | "path  "                    -> (cl-user::swpath argstr))
   | "p"                         -> (cl-user::sw     argstr) 
   | "proc "                     -> (cl-user::sw     argstr) 
   | "pwd"                       -> (princ (Specware::current-directory)) 
   | "reproc"                    -> (let ((cl-user::*force-reprocess-of-unit* t)) (cl-user::sw     argstr)) 
   | "rp"                        -> (let ((cl-user::*force-reprocess-of-unit* t)) (cl-user::sw     argstr)) 
   | "show  "                    -> (cl-user::show     argstr) 
   | "showx "                    -> (cl-user::showx    argstr) 
   | "showdeps"                  -> (cl-user::showdeps argstr) 
   | "showimports"               -> (cl-user::showimports argstr) 
   | "showdata"                  -> (cl-user::showdata argstr) 
   | "showdatav"                 -> (cl-user::showdatav argstr) 
   | "checkspec"                 -> (cl-user::checkspec argstr) 

   | "gen-acl2"                  -> gen_acl2 ()

   | "gen-coq"                   -> gen_coq ()

   | "gen-c"                     -> (cl-user::swc    argstr) 
   | "gen-c-thin"                -> (cl-user::gen-c-thin    argstr) 

   | "gen-java"                  -> (cl-user::swj    argstr) 

   | "gen-haskell"               -> gen_haskell     ()
   | "gen-h"                     -> gen_haskell     ()
   | "gen-haskell-top"           -> gen_haskell_top ()
   | "gen-ht"                    -> gen_haskell_top ()

   | "gen-lisp"                  -> (cl-user::swl argstr)
   | "gen-l"                     -> (cl-user::swl argstr)
   | "gen-lisp-top"              -> (let ((cl-user::*slicing-lisp?* t)) (cl-user::swl argstr))
   | "gen-lt"                    -> (let ((cl-user::*slicing-lisp?* t)) (cl-user::swl argstr))
   | "lgen-lisp"                 -> (cl-user::swll   argstr)

   | "make"                      -> (if (null argstr) (cl-user::make) (cl-user::make argstr)))

   | "oblig"                     -> obligs ()
   | "obligations"               -> obligs ()
   | "obligs"                    -> obligs ()
  
   | "gen-obligations"           -> gen-obligs ()
   | "gen-oblig"                 -> gen-obligs ()
   | "gen-obligs"                -> gen-obligs ()

   | "gen-obligations-no-simp"   -> gen-obligs_no_simp ()
   | "gen-oblig-no-simp"         -> gen-obligs_no_simp ()
   | "gen-obligs-no-simp"        -> gen-obligs_no_simp ()

   | "pc"                        -> (cl-user::swpc argstr)
   | "proofcheck"                -> (cl-user::swpc argstr)

   | "prove"                     -> (cl-user::sw (concatenate 'string "prove " argstr)) 
   | "prwb"                      -> (if argstr (cl-user::swprb argstr) (cl-user::swprb)))

   | "punits"                    -> (cl-user::swpf   argstr))
   | "lpunits"                   -> (cl-user::lswpf  argstr)) ; No local version yet

   | "transform"                 -> transform () 

   | "trace-eval"                -> (setq MSInterpreter::traceEval? t)   (format t "Tracing of eval turned on.")        
   | "untrace-eval"              -> (setq MSInterpreter::traceEval? nil) (format t "Tracing of eval turned off.")       

   | "uses"                      -> uses ()

   %% Non-user commands

   | "cf"                        -> (cl-user::cf argstr))

   | "cl"                        -> (with-break-possibility (cl-user::cl argstr)))

   | "com"                       -> com ()

   | "dev"                       -> (princ (if argstr   (setq *developer?* (not (member argstr '("nil" "NIL" "off") :test 'string=)))  *developer?* ))

   | "lisp"                      -> lisp ()
   | "l"                         -> lisp ()

   | "f-b"                       -> (when (fboundp 'cl-user::f-b)   (funcall 'cl-user::f-b argstr)))
   | "f-unb"                     -> (when (fboundp 'cl-user::f-unb) (funcall 'cl-user::f-unb (or argstr ""))))

   | "ld"                        -> (with-break-possibility (cl-user::ld argstr)))

   | "pa"                        -> (cl-user::pa argstr))

   | "set-base"                  -> (cl-user::set-base argstr))

   | "show-base-unit-id"         -> (cl-user::show-base-unit-id))

   | "swdbg"                     -> (if argstr (cl-user::swdbg argstr) (cl-user::swdbg)))

   | "tr"                        -> (cl-user::tr argstr))
   | "untr"                      -> (cl-user::untr))

   | "trace-rewrites"            -> trace_rewrites   ()
   | "trr"                       -> trace_rewrites   ()
   | "untrace-rewrites"          -> untrace_rewrites ()
   | "untrr"                     -> untrace_rewrites ()

   | "wiz"                       -> (if argstr (cl-user::wiz   argstr) (cl-user::wiz)))

   | _ ->
     if constantp? cmd && args = [] then
       cmd
     else
       let _ = writeLine ("Unknown command `" ^ anyToString cmd ^ "'. Type `help' to see available commands.") in
       cmd
   *)
   | _ ->
     NotYetImplemented
     

op oldProcessSpecwareShellCommand (cmd : String, args_str : String) : TypedValues % implemented in handwritten lisp code

%% This will supplant old-process-sw-shell-command (defined in Handwritten/Lisp/sw-shell.lisp)
%% as the new top-level specware shell command processor

op processSpecwareShellCommand (cmd : String, args_str : String) : TypedValues =
 let old_ctxt = getCommandContext () in
 case parseCommandArgs args_str of
   | Good args ->
     (case dispatch (cmd, args, old_ctxt) of
        | Good (typed_values, new_ctxt) -> 
          let _ = setCommandContext new_ctxt in
          typed_values

        | NotYetImplemented ->
          oldProcessSpecwareShellCommand (cmd, args_str)

        | Error msg ->
          let _ = writeLine ("problem processing shell command using new processor, reverting to old one: " ^ msg) in
          oldProcessSpecwareShellCommand (cmd, args_str) )

   | Error msg ->
     let _ = writeLine ("could not parse args, reverting to old shell processor: " ^ msg) in
     oldProcessSpecwareShellCommand (cmd, args_str) 

#translate lisp
-verbatim
(defun SpecwareShell::getCommandContext-0 ()
  (let ((current_dir  (Specware::current-directory))
        (current_path (or (Specware::getenv "SWPATH") "")))
    (SpecwareShell::mkCommandContext-2 current_dir current_path)))

(defun SpecwareShell::setCommandContext (ctxt)
  (let ((current_dir  (SpecwareShell::currentDir  ctxt))
        (current_path (SpecwareShell::currentPath ctxt)))
    (Specware::cd              current_dir)
    (SpecwareShell::setswpath  current_path)
    (SpecwareShell::getCommandContext-0)))

(defun SpecwareShell::setswpath (str)
  (setq str (strip-extraneous str))
  (let ((newpath (if (or (null str) (equal str ""))
		     (or (Specware::getenv "SWPATH") "")
		   (let ((str (normalize-path (string str) nil)))
		     (if (SpecCalc::checkSpecPathsExistence str)
			 (progn (Specware::setenv "SWPATH" (string str))
				(setq cl-user::*saved-swpath* nil)
				(string str))
		       (progn (format t "Keeping old path:~%")
			      (Specware::getenv "SWPATH")))))))
   (princ (normalize-path newpath t))
   (values)))

-end
#end


end-spec

