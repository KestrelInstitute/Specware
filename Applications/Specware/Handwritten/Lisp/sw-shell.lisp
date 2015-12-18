(defpackage :Utilities)
(defpackage :TypeObligations)
(defpackage :Prover)
(defpackage :Simplify)
(defpackage :IsaTermPrinter)
(defpackage :CoqTermPrinter)
(defpackage :Refs)
(defpackage :Haskell)
(defpackage :SpecwareShell) ; new 
(defpackage :SWShell)       ; deprecated
(in-package :SWShell)

(defparameter *prompt* "* ")
(defparameter eofs-before-quit 2)
(defvar *in-specware-shell?* nil)
(defvar *last-eval-expr* nil)
(defvar *developer?* nil)
;(defparameter *specware-shell-readtable* (make-readtable))

(defparameter *sw-shell-help-strings*
  '(("help"      . "[command] Prints help information for command, or, with no argument, all commands.")
    ("cd"        . "[dir] Connect to directory. With no argument, displays the current directory.")
    ("dir"       . "List .sw files in current directory.")
    ("dirr"      . "List .sw files in current directory and recursively in subdirectories.")
    ("path"      . "[dirseq] Sets the current Specware path.
                        With no argument, displays the current Specware path.")
    ("proc"      . "[unit-term] Processes the unit.
                        With no argument, processes the last processed unit.")
    ("p"         . "[unit-term] Abbreviation for proc.")
    ("cinit"     . "Clears Spec unit cache.")
    ("show"      . "[unit-term] [qids] Displays the value of the processed unit-term. \nIf qids are given just displays ops/types/theorems with those qids.")
    ("showx"     . "[unit-term] Like `show' but shows all types and ops including imports.")
    ("showdeps"  . "[unit-identifier] Print dependencies in unit.  With no argument, uses last processed unit.")
    ("showimports"  . "[unit-identifier] Generate a graph of the imports in unit.  With no argument, uses last processed unit.")
    ("showdata"  . "[unit-identifier] Show the spec data structures in unit.  With no argument, uses last processed unit.")
    ("showdatav"  . "[unit-identifier] Like showdata but verbose (shows imported specs in full).")
    ("checkspec"  . "[unit-identifier] Test spec for well-formedness.  With no argument, uses last processed unit.")
    ("obligations" . "[unit-term] Abbreviation for show obligations ...")
    ("oblig"     . "[unit-term] Abbreviation for show obligations ...")
    ("gen-obligations" . "[unit-term] Generate Isabelle/HOL obligation theory for unit.")
    ("gen-obligs" . "[unit-term] Generate Isabelle/HOL obligation theory for unit.")
    ("gen-coq"   . "Generates Coq obligations for unit.")
    ("gen-acl2"   . "Generates ACL2 code for unit.")
    ("gen-haskell" . "[unit-term] Generate Haskell code for unit.")
    ("gen-h" . "[unit-term] Generate Haskell code theory for unit.")
    ("gen-haskell-top" . "[unit-term] Generate Haskell code for unit slicing imports.")
    ("gen-ht" . "[unit-term] Generate Haskell code theory for unit slicing imports.")

    ("prove"     . "[proof arguments] Abbreviation for proc prove ...")
    ("punits"    . "[unit-identifier [filename]] Generates proof unit definitions for all conjectures in the unit and puts
                        them into filename.")
    ("lpunits"   . "[unit-identifier [filename]] Like `punits' but only for local conjectures.")
    ("transform" . "[unit-identifier] Enter transform shell for spec.")
    ("ctext"     . "[spec-term] Sets the current context for eval commands.
                        \"None\" resets it to Base spec.
                        With no arguments displays context.")
    ("eval"      . "[expression] Evaluates expression with respect to current context.")
    ("e"         . "[expression] Abbreviation for eval.")
    ("trace-eval" . "Turn on tracing of eval.")
    ("untrace-eval" . "Turns off tracing of eval.")
    ("eval-lisp" . "[expression] Like `eval' except the expression is translated to Lisp and evaluated in Lisp.")
    ("gen-lisp"  . "[spec-term [filename]] Generates Lisp code for unit in filename.
                        With no argument uses last processed unit.")
    ("gen-lisp-top"  . "[spec-term [filename]] Generates Lisp code for unit in filename slicing away defs not need by unit.
                        With no argument uses last processed unit.")
    ("gen-lt"    . "[spec-term [filename]] Generates Lisp code for unit in filename slicing away defs not need by unit.
                        With no argument uses last processed unit.")
    ("lgen-lisp" . "[spec-term [filename]] Like `gen-lisp' but only generates Lisp for local definitions of spec.")
    ("gen-java"  . "[spec-term [option-spec]] Generates Java code for unit in filename.
                        With no argument uses last processed unit.")
    ("gen-c"     . "[spec-term [filename]] Generates C code for unit in filename.
                        With no argument uses last processed unit.")
    ("gen-c-thin" . "[unit-identifier [filename]] Generates C code for unit.  Writes to filename.
                        With no argument uses last processed unit.")
    ("make"      . "[spec-term] Generate C code with makefile and call make on it.")
    ("ld"        . "[filename] Load Lisp file filename.")
    ("cf"        . "[filename] Compile Lisp file filename.")
    ("cl"        . "[filename] Compile and load Lisp file filename.")
    ("pa"        . "[pkgname] Sets the default lisp package.")
;;    ("bash"      . "[fn [args]] Applies fn to args in bash shell.
;;                  No spaces allowed in args.
;;                  With no argument, starts subordinate bash shell.")
    ("exit"      . "Exits shell and Lisp.")
    ("quit"      . "Alias for exit.")
    ))

(defparameter *sw-shell-dev-help-strings* ; common to all shells
  '(("set-base" . "[unit-id] Sets base spec to unit-id")
    ("lisp"     . "[lisp expr] Evaluate lisp expression.")
    ("l"        . "[lisp expr] Abbreviation for lisp.")
    ("tr"       . "[lisp function names] Trace functions.")
    ("untr"     . "Untrace all traced functions.")
    ("f-b"      . "[lisp function names] Break functions.")
    ("f-unb"    . "[lisp function names] Unreak functions. No argument means all broken functions")
    ("pa"       . "[package name] Set package for lisp forms.")
    ("proofcheck". "[unit-identifier] Abbreviation for proc prove WELLFORMED [unit-identifier] with Checker ..")
    ("pc"        . "[unit-identifier] Abbreviation for proc prove WELLFORMED [unit-identifier] with Checker ..")
    ("prwb"      . "[on] Include the base hypothesis when invoking Snark.") ;TODO: deprecate this command
    ("dev"      . "[on] Set *developer?*. No argument gives current setting.")
    ("wiz"      . "[on] Set SpecCalc::specwareWizard?. No argument gives current setting.")
    ("swdbg"    . "[on] Set System-Spec::specwareDebug?. No argument gives current setting.")))

(defun print-shell-prompt ()
  (princ *prompt* *standard-output*)
  (finish-output))

(defvar *emacs-eval-form-after-prompt* nil)

(defun set-specware-shell (val)
  (setq *in-specware-shell?* val))

(defun in-specware-shell? ()
  *in-specware-shell?*)

(setq *debugger-hook* #'(lambda (ignore1 ignore2)
                          (declare (ignore ignore1 ignore2))
                          (set-specware-shell nil)))

(defun specware-shell0 ()
  (specware-shell t))

(defvar *sw-shell-print-level* 8)
(defvar *sw-shell-print-length* 16)
(defvar *current-command-processor* (if (fboundp 'SpecwareShell::processSpecwareShellCommand-2)
                                        'SpecwareShell::newProcessSpecwareShellCommand
                                        'old-process-sw-shell-command))
(defvar *raw-command*)

(defun aux-specware-shell (exiting-lisp?
                           *current-command-processor* ;; special binding -- some commands may change this
                           &optional
                             (banner        "Specware Shell~%")
                             (abort-message "Return to Specware Shell top level.")
                             (exit-message  "Exiting Specware Shell. :sw-shell to reenter."))
  (let  ((magic-eof-cookie (cons :eof nil))
         (number-of-eofs 0)
         (cl:*package* cl:*package*)
         (sw-shell-pkg (find-package :SWShell))
         (*print-level* *sw-shell-print-level*)
         (*print-length* *sw-shell-print-length*)
         (start-up t)
         * ** ***
         / // ///
         ch)
    (Emacs::eval-in-emacs "(set-comint-prompt)")
    (setq *emacs-eval-form-after-prompt* nil)
    (format t banner)
    (unwind-protect
         (loop
            (set-specware-shell t)
            (fresh-line *standard-output*)
            (print-shell-prompt)
            (when *emacs-eval-form-after-prompt*
              (Emacs::eval-in-emacs *emacs-eval-form-after-prompt*)
              (setq *emacs-eval-form-after-prompt* nil))
            (catch ':top-level-reset  ; Used by allegro :reset command
              (with-simple-restart (abort abort-message)
                                        ;(set-specware-shell t)
                (loop while (member (setq ch (read-char *standard-input* nil nil)) '(#\Newline #\Space #\Tab))
                   do ;; If user types a newline give a new prompt
                     (when (and (eq ch #\Newline) (not start-up))
                       (print-shell-prompt)))
                (setq start-up nil)
                (when ch
                  (unread-char ch))
                (catch #+allegro          'tpl::top-level-break-loop
                       #+mcl              :toplevel
                       #-(or allegro mcl) nil
                       (let ((form (command-read magic-eof-cookie)))
                         (if (symbolp form)
                             (let ((*raw-command* (intern (symbol-name form) sw-shell-pkg)))
                               (when (symbolp form)
                                 (setq form (intern (Specware::fixCase (symbol-name form)) sw-shell-pkg)))
                               (cond ((member form '(quit exit))
                                      (setq exiting-lisp? t)
                                      (Specware::exit))
                                     ((member form '(OK |ok|))
                                      (return))
                                     ((not (eq form magic-eof-cookie))
                                      (let* ( ;(*raw-command* )
                                             (results
                                              (multiple-value-list
                                               ;; note: some commands change the value of *current-command-processor*,
                                               ;;       so this is not neccessarily the value we entered with
                                               (sw-shell-command *current-command-processor* form))))
                                        (dolist (result results)
                                          (fresh-line)
                                          (prin1 result)))
                                      (setf number-of-eofs 0))
                                     ((eql (incf number-of-eofs) 1)
                                      (let ((stream (make-synonym-stream '*terminal-io*)))
                                        (setf *standard-input* stream)
                                        (setf *standard-output* stream)
                                        (format t "~&Received EOF on *standard-input*, switching to *terminal-io*.~%")))
                                     ((> number-of-eofs eofs-before-quit)
                                      (format t "~&Received more than ~D EOFs; Aborting.~%"
                                              eofs-before-quit)
                                      (Specware::exit))
                                     (t
                                      (format t "~&Received EOF.~%"))))
                             (let ((results (multiple-value-list (eval form))))
                               (dolist (result results)
                                 (fresh-line)
                                 (prin1 result)))))))))
      ;; unwind-protect undo:
      (set-specware-shell nil)
      (unless exiting-lisp?
        (format t "~%~A~%" exit-message)))))

(defvar *command-read-table* (copy-readtable))

(setf (readtable-case *command-read-table*) :preserve)

(defun command-read (magic-eof-cookie)
  (let ((next-ch (peek-char t *standard-input* nil magic-eof-cookie)))
    (if (alpha-char-p next-ch)
        (let ((*readtable* *command-read-table*))
          (read *standard-input* nil magic-eof-cookie))
        (read *standard-input* nil magic-eof-cookie))))

(defun sw-shell-command (sw-shell-command-processor command)
  (let ((ch (read-char-no-hang *standard-input* nil nil)))
    (when (and ch (not (eq ch #\Newline)))
      (unread-char ch))
   (funcall sw-shell-command-processor
            command
            (if (or (null ch)          ; interactive, end of command
                    (eq ch #\Newline)) ; batch, first char after whitespace is newline
                nil
              (read-line)))))

(defmacro with-break-possibility (&rest fms)
  `(progn (set-specware-shell nil)
          ,@fms))

(defun lisp-value (val)
  (when val
    (setq *** **
         ** *
         * (car val)
         /// //
         // /
         / val))
  (values-list val))

#|| Didn't pan out
(defvar original-error #'error)

(defun just-print-error-message
    (s &rest all-args &key format-control format-arguments &allow-other-keys)
  (if (eq s 'file-error)
      (apply original-error s all-args)
    (progn
      (when (typep s 'condition)
       (unless format-control
         (setq format-control (simple-condition-format-control s)))
       (unless format-arguments
         (setq format-arguments (simple-condition-format-arguments s))))
      (if format-control
               (apply #'format t format-control format-arguments)
        (format t "Error ~a" s))
      (throw ':top-level-reset nil))))

(defun sw-shell-0 ()
  (Specware::initializeSpecware-0)
  (setq Emacs::*use-emacs-interface?* nil)
  (#+allegro excl:without-package-locks #-allegro progn
   (setf (symbol-function 'error) #'just-print-error-message))
  (Specware::change-directory (Specware::getenv "SPECWARE4"))
  #+allegro
  (setq cl-user::*restart-actions* nil)
  #+allegro
  (when (functionp excl:*restart-init-function*)
    (funcall excl:*restart-init-function*)
    (setq excl:*restart-init-function* nil))
  (SWShell::specware-shell nil)
  #+allegro
  (excl:without-package-locks #-allegro progn
   (setf (symbol-function 'error) original-error))
  t)
||#

;;; ================================================================================
;;; Replicate and revise this portion for other shells (prism, accord, etc.)
;;; ================================================================================

(setq cl-user::*sw-help-strings*
  (append cl-user::*sw-help-strings*
         '((":sw-shell" . "Run Specware Shell"))))

#+allegro
(top-level:alias ("sw-shell") () (specware-shell nil))

;;; Add commands for entering shell from Lisp shell
(defun cl-user::sw-shell ()
  (specware-shell nil))

(defun specware-shell (exiting-lisp?)
  (aux-specware-shell exiting-lisp? *current-command-processor*))
  
(defvar *sw-shell-pkg* (find-package :SWShell))

(defvar *commands-in-process* 0)

;;; ================================================================================
;;; TWO TOP LEVEL ENTRIES: one for unix command line and one for slime interface
;;; ================================================================================

;;; TOP LEVEL ENTRY when running bin/specware-shell
(defun specware-shell-no-emacs ()
  (progn (setq Emacs::*use-emacs-interface?* nil) 
         (format t "Welcome to Specware version ~a!~%" cl-user::*Specware-Version*)
         (Specware::initializeSpecware-0)
         (SWShell::specware-shell t)
         (sb-sys:os-exit 0)))

;;; TOP LEVEL ENTRY when using slime
;;; From slime.el:  (defvar sw:*shell-command-function* "SWShell::process-raw-command")
(defun process-raw-command (command argstr)
  ;; Note: 
  ;;  Swank intercepts some commands before ever coming here, including those
  ;;  that start with a parenthesis, symbols such as quit or exit, and "".
  ;;  It also parses '(1 2 3) as command |'(1| and argstr "2 3)".
  ;; 
  (incf *commands-in-process*)
  (let* ((*raw-command* (intern (symbol-name command) *sw-shell-pkg*))
         (command (intern (Specware::fixCase (symbol-name command)) *sw-shell-pkg*))
         (results (multiple-value-list
                   (funcall *current-command-processor*
                            (if (symbolp command)
                                (intern (symbol-name command) *sw-shell-pkg*)
                                command)
                            argstr))))
    (decf *commands-in-process*)
    (if (null results)
        (swank::repl-suppress-output)
        (values-list results))))

;;; ================================================================================

;; Specware uses this for *current-command-processor*
;; Other systems (e.g. prism or accord) may use related functions...

;; fallback interface from processSpecwareShellCommand defined in SpecwareShell.sw
;; as that handles more cases directly, this will be called less often until it
;; is finally eliminated

(defun SpecwareShell::oldProcessSpecwareShellCommand-2 (command argstr)
  (let ((arg (if (equal argstr "") nil argstr))) ; backwards compatiblity, until each dispatch fn can hanble ""
    (let* ((lisp_values (multiple-value-list (swshell::old-process-sw-shell-command command arg)))
           (sw_values   (SpecwareShell::type_values lisp_values)))
      sw_values)))

(defun SpecwareShell::newProcessSpecwareShellCommand (command argstr)
  (let* ((argstr      (or argstr "")) ; argument to processSpecwareShellCommand must be a string
         (sw_values   (SpecwareShell::processSpecwareShellCommand-2 command argstr))
         ;; each typed value is something like (:string "..."), (:integer 33), etc.
         (lisp_values (SpecwareShell::untype_values sw_values)))
    (values-list lisp_values)))

;; previous shell command, being superseded by processSpecwareShellCommand in SpecwareShell.sw
(defun old-process-sw-shell-command (command argstr)
  (cond ((and (consp command) (null argstr))
         (lisp-value (multiple-value-list (eval command))))
        ((symbolp command)
         (case command
           (transform (let* ((spec-uid (cl-user::norm-unitid-str argstr))
                             (val (cdr (Specware::evaluateUnitId (or spec-uid cl-user::*last-unit-Id-_loaded*)))))
                        (if (or (null val) (not (eq (car val) ':|Spec|)))
                            (format t "Not a spec!")
                            (let ((spc (cdr val)))
                              (when spec-uid (setq cl-user::*last-unit-Id-_loaded* spec-uid))
                              (initialize-transform-session spc)
                              (setq *current-command-processor* 'process-transform-shell-command)
                              (format t "Entering Transformation Construction Shell")))
                        (values)))
           (help      (let ((cl-user::*sw-help-strings*
                             (append *sw-shell-help-strings*
                                     (if *developer?*
                                         *sw-shell-dev-help-strings*
                                         '()))))
                        (cl-user::sw-help argstr) ; refers to cl-user::*sw-help-strings*
                        ))
           (cd        (if (null argstr)
                          (princ (Specware::current-directory))
                          (Specware::cd argstr))
                      (values))
           (pwd       (princ (Specware::current-directory)) (values))
           ((dir ls)  (swshell::ls     (or argstr "")))
           (dirr      (swshell::dirr   (or argstr "")))
           (path      (cl-user::swpath argstr))
           ((proc p)  (cl-user::sw     argstr) (values))
           ((reproc rp)  (let ((cl-user::*force-reprocess-of-unit* t)) (cl-user::sw     argstr)) (values))
           (show      (cl-user::show     argstr) (values))
           (showx     (cl-user::showx    argstr) (values))
           (showdeps  (cl-user::showdeps argstr) (values))
           (showimports  (cl-user::showimports argstr) (values))
           (showdata  (cl-user::showdata argstr) (values))
           (showdatav  (cl-user::showdatav argstr) (values))
           (checkspec  (cl-user::checkspec argstr) (values))
           (cinit     (cl-user::sw-init))
           ((gen-lisp gen-l) (cl-user::swl argstr) (values))
           ((gen-lisp-top gen-lt)  (let ((cl-user::*slicing-lisp?* t)) (cl-user::swl argstr)) (values))
           (lgen-lisp (cl-user::swll   argstr) (values))
           (gen-c     (cl-user::swc    argstr) (values))
           (gen-c-thin (cl-user::gen-c-thin    argstr) (values))
           (make      (if (null argstr) (cl-user::make) (cl-user::make argstr)))
           (gen-java  (cl-user::swj    argstr) (values))
           ((obligations oblig obligs)
            (cl-user::show (concatenate 'string "\"obligations "
                                        (if (null argstr)
                                            cl-user::*last-unit-Id-_loaded*
                                          (cl-user::norm-unitid-str argstr))
                                        "\""))
            (values))
           ((gen-obligations gen-oblig gen-obligs)
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
                (IsaTermPrinter::printUIDtoThyFile-3 uid t t)))) ; do simplify
           ((gen-obligations-no-simp gen-oblig-no-simp gen-obligs-no-simp)
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
           (gen-coq
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
                (CoqTermPrinter::printUIDToCoqFile uid))))
           (gen-acl2 
            (let ((TypeObligations::generateTerminationConditions? nil)
                  (TypeObligations::generateExhaustivityConditions? t)
                  (Simplify::simplifyUsingSubtypes? t)
                  (Prover::treatNatSpecially? nil)
                  (Utilities::namedTypesRaised? t))
              (cl-user::gen-acl2 argstr) (values)))
           ((gen-haskell gen-h)
            (let ((uid (if (not (null argstr))
                           argstr
                           (if (not (null cl-user::*last-unit-Id-_loaded*))
                               cl-user::*last-unit-Id-_loaded*
                               (progn (format t "No previous unit processed~%")
                                      nil)))))
              (unless (null uid)
                (setq cl-user::*last-unit-Id-_loaded* uid)
                (Haskell::printUIDtoHaskellFile-3 uid nil t))))
           ((gen-haskell-top gen-ht)
            (let ((uid (if (not (null argstr))
                           argstr
                           (if (not (null cl-user::*last-unit-Id-_loaded*))
                               cl-user::*last-unit-Id-_loaded*
                               (progn (format t "No previous unit processed~%")
                                      nil)))))
              (unless (null uid)
                (setq cl-user::*last-unit-Id-_loaded* uid)
                (Haskell::printUIDtoHaskellFile-3 uid t t))))
           (prove     (cl-user::sw (concatenate 'string "prove " argstr)) (values))
           (proofcheck (cl-user::swpc argstr))
           (pc        (cl-user::swpc argstr))
           (prwb      (if argstr (cl-user::swprb argstr) (cl-user::swprb)))
           (punits    (cl-user::swpf   argstr))
           (lpunits   (cl-user::lswpf  argstr)) ; No local version yet
           (ctext     (if (null argstr)
                          (progn (if cl-user::*current-swe-spec*
                                     (format t "~&Current context: ~a" cl-user::*current-swe-spec*)
                                     (format t "~&Current context: Base Spec"))
                                 (values))
                          (if (string-equal argstr "none")
                              (progn (setq cl-user::*current-swe-spec* nil)
                                     (format t "~&Subsequent evaluation commands will import just the base spec.~%"))
                              (cl-user::swe-spec argstr))))
           ((eval e)  (let ((cl-user::*swe-use-interpreter?* t)
                            (argstr (or argstr *last-eval-expr*))
                            (cl-user::*expr-begin-offset* (if (eq command 'e) -12 -9)))
                        (if (null argstr)
                            (warn "No previous eval command.")
                            (progn (setq *last-eval-expr* argstr)
                                   (cl-user::swe argstr)
                                   (values)))))
           (trace-eval (setq MSInterpreter::traceEval? t)
                       (format t "Tracing of eval turned on.")
                       (values))
           (untrace-eval (setq MSInterpreter::traceEval? nil)
                         (format t "Tracing of eval turned off.")
                         (values))
           ((eval-lisp el)
            (let ((cl-user::*swe-use-interpreter?* nil)
                  (argstr (or argstr *last-eval-expr*))
                  (cl-user::*expr-begin-offset* (if (eq command 'el) -11 -4)))
              (if (null argstr)
                  (warn "No previous eval command.")
                  (progn (setq *last-eval-expr* argstr)
                         (cl-user::swe argstr)
                         (values)))))
           (uses      (if (null argstr)
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
                            (values))))
           ;; Non-user commands
           (set-base          (cl-user::set-base argstr))
           (show-base-unit-id (cl-user::show-base-unit-id))

           ((lisp l)  (if (null argstr)
                          (format t "Error: ~a requires an argument" *raw-command*)
                          (with-break-possibility (lisp-value (multiple-value-list (eval (read-from-string argstr)))))))
           (cl        (with-break-possibility (cl-user::cl argstr)))
           (ld        (with-break-possibility (cl-user::ld argstr)))
           (cf        (cl-user::cf argstr))
           (tr        (cl-user::tr argstr))
           (untr      (cl-user::untr))
           (f-b       (when (fboundp 'cl-user::f-b)
                        (funcall 'cl-user::f-b argstr)))
           (f-unb     (when (fboundp 'cl-user::f-unb)
                        (funcall 'cl-user::f-unb (or argstr ""))))
           (pa        (cl-user::pa argstr))
           (dev       (princ (if argstr
                                 (setq *developer?* (not (member argstr '("nil" "NIL" "off") :test 'string=)))
                                 *developer?*))
                      (values))
           (wiz       (if argstr (cl-user::wiz   argstr) (cl-user::wiz)))
           (swdbg     (if argstr (cl-user::swdbg argstr) (cl-user::swdbg)))
           (com       (let ((cl:*package* (find-package "CL-USER")))
                        (multiple-value-bind (command pos)
                            (read-from-string argstr)
                          (if (fboundp command)
                              (let ((com-argstr (subseq argstr pos)))
                                (if (string= com-argstr "")
                                    (funcall command)
                                    (funcall command com-argstr)))
                              (format t "Unknown command: ~a." command)))))
           ((trace-rewrites trr)
            (setq MetaSlangRewriter::traceRewriting 2)
            (format t "Rewrite tracing turned on.")
            (when (and (not (null argstr))
                       (string= "t" (cl-user::strip-extraneous argstr)))
              (setq MetaSlangRewriter::debugApplyRewrites? t))
            (values))
           ((untrace-rewrites untrr) (setq MetaSlangRewriter::traceRewriting 0)
            (format t "Rewrite tracing turned off.")
            (setq MetaSlangRewriter::traceRewriting 0)
            (setq MetaSlangRewriter::debugApplyRewrites? nil)
            (HigherOrderMatching::turnOffHOMatchTracing-0)
            (values))
           ;;      (bash      (cl-user::bash argstr))
           ;;
           (t
            (format t "Unknown command `~a'. Type `help' to see available commands."
                    *raw-command*)
            (values))))
        ((and (constantp command) (null argstr))
         (values command))
        (t
         (format t "Unknown command `~S'. Type `help' to see available commands."
                 command))))

;; This is currently a top-level entry point (called from Applications/Specware/bin/unix/specware-batch.sh):
;; Process a sequence of Specware commends in batch mode.  Commands come in separated by newlines.
;; Maybe this function, in its current form, isn't really needed (you
;; can just pipe a bunch of commands into Specware? but I may have
;; seen that fail in some cases?). However, I'd like to augment this to
;; catch and report errors better (and stop processing commands at the
;; first error).

(defun process-batch-commands ()
  (progn 
    (format t "Processing batch Specware commands:~%")
    (let ((magic-eof-cookie (cons :eof nil)))
      (loop while (not (equal magic-eof-cookie (peek-char t *standard-input* nil magic-eof-cookie)))
         do
           (let* ((line-string (read-line)))
             (progn
               (format t "Processing command: ~s~%" line-string)
               (multiple-value-bind
                     (command argstartposition)
                   (read-from-string line-string)
                 (let* ( ;;command may be a Specware shell command (like proc) or a Lisp form to be sumitted directly to Lisp
                        ;;is this needed?
                        (command (if (symbolp command) (intern (Specware::fixCase (symbol-name command)) (find-package :SWShell)) command))
                        (*raw-command* command) ;why?
                        (argstring (subseq line-string argstartposition)))
                   (progn 
                     ;(format t "Command: ~a~%" command)
                     ;(format t "Arg String: ~s~%" argstring)
                     (when (member command '(quit exit ok)) (return))                         
                     (funcall *current-command-processor* command argstring))))))))))

#|
(defun parse-and-execute-MSTerm-string (input_str)
  (let* ((Emacs::*goto-file-position-store?* t)
	 (Emacs::*goto-file-position-stored* nil)
         (Specware::stringErrorByte (cons ':|Ref| -1))
	 (parser-type-check-output nil)
         (o_term '(:|None|))
         parsed_input)
    (setq parser-type-check-output
          (with-output-to-string (*standard-output*)
            (let ((*error-output* *standard-output*)
                  (SpecCalc::numberOfTypeErrorsToPrint 2))
              (setq parsed_input (parser4::parseSpecwareString input_str
                                                               :start-rule-name :EXPRESSION))
              (when (Option::some? parsed_input)
                (setq o_term (Specware::elaboratePosTerm_fromLisp-2 (cdr parsed_input) *transform-spec*))))))
    (if (Option::some? o_term)
        (SpecCalc::evaluatePrintMSTerm (cdr o_term))
        (let ((error-byte (or (if (not (null Emacs::*goto-file-position-stored*))
                                  (third Emacs::*goto-file-position-stored*)
                                  (if (>= (cdr Specware::stringErrorByte) 0)
                                      (- (cdr Specware::stringErrorByte) 1)
                                      nil)))))
          (if error-byte
            (let ((emacs-command (format nil "(show-error-on-new-input ~a nil)" error-byte)))
              (princ (cl-user::trim-error-output parser-type-check-output))
              (force-output)
              (Emacs::eval-in-emacs emacs-command))
            (format t "~%Error not specified"))))))
|#
