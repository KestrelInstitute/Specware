(defpackage :TypeObligations)
(defpackage :Prover)
(defpackage :IsaTermPrinter)
(defpackage :Refs)
(defpackage :SWShell)
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
    ("show"      . "[unit-term] Like `proc' but in addition displays the value of the processed unit-term.")
    ("showx"     . "[unit-term] Like `show' but shows all types and ops including imports.")
    ("obligations" . "[unit term] Abbreviation for show obligations ...")
    ("oblig"     . "[unit term] Abbreviation for show obligations ...")
    ("gen-obligations" . "[unit term] Generate Isabelle/HOL obligation theory for unit.")
    ("gen-obligs" . "[unit term] Generate Isabelle/HOL obligation theory for unit.")

    ("prove"     . "[proof arguments] Abbreviation for proc prove ...")
    ("punits"    . "[unit-identifier [filename]] Generates proof unit definitions for all conjectures in the unit and puts
                  them into filename.")
    ("lpunits"   . "[unit-identifier [filename]] Like `punits' but only for local conjectures.")
    ("transform" . "[unit-identifier] Enter transform shell for spec.")
    ("ctext"     . "[spec-term] Sets the current context for eval commands.
                  With no arguments displays context.")
    ("eval"      . "[expression] Evaluates expression with respect to current context.")
    ("e"         . "[expression] Abbreviation for eval.")
    ("eval-lisp" . "[expression] Like `eval' except the expression is translated to Lisp and evaluated in Lisp.")
    ("gen-lisp"  . "[spec-term [filename]] Generates Lisp code for unit in filename.
                  With no argument uses last processed unit.")
    ("lgen-lisp" . "[spec-term [filename]] Like `gen-lisp' but only generates Lisp for local definitions of spec.")
    ("gen-java"  . "[spec-term [option-spec]] Generates Java code for unit in filename.
                  With no argument uses last processed unit.")
    ("gen-c"     . "[spec-term [filename]] Generates C code for unit in filename.
                  With no argument uses last processed unit.")
    ("make"      . "[spec-term] Generate C code with makefile and call make on it.")
    ("ld"        . "[filename] Load Lisp file filename.")
    ("cf"        . "[filename] Compile Lisp file filename.")
    ("cl"        . "[filename] Compile and load Lisp file filename.")
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
    ("prwb"      . "[on] Include the base hypothesis when invokig Snark.")
    ("dev"      . "[on] Set *developer?*. No argument gives current setting.")
    ("wiz"      . "[on] Set SpecCalc::specwareWizard?. No argument gives current setting.")
    ("swdbg"    . "[on] Set System-spec::specwareDebug?. No argument gives current setting.")))

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
(defvar *current-command-processor* 'process-sw-shell-command)

(defvar *current-command-processor* 'process-sw-shell-command)

(defun aux-specware-shell (exiting-lisp?
			   *current-command-processor* 
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
    (emacs::eval-in-emacs "(set-comint-prompt)")
    (setq *emacs-eval-form-after-prompt* nil)
    (format t banner)
    (unwind-protect
	(loop
	  (set-specware-shell t)
	  (fresh-line *standard-output*)
	  (print-shell-prompt)
	  (when *emacs-eval-form-after-prompt*
	    (emacs::eval-in-emacs *emacs-eval-form-after-prompt*)
	    (setq *emacs-eval-form-after-prompt* nil))
	  (catch ':top-level-reset	; Used by allegro :reset command
	    (with-simple-restart (abort abort-message)
					;(set-specware-shell t)
				 (loop while (member (setq ch (read-char *standard-input* nil nil)) '(#\Newline #\Space #\Tab))
				   do;; If user types a newline give a new prompt
				   (when (and (eq ch #\Newline) (not start-up))
				     (print-shell-prompt)))
				 (setq start-up nil)
				 (when ch
				   (unread-char ch))
				 (catch #+allegro 'tpl::top-level-break-loop
					#+mcl :toplevel 
					#-(or allegro mcl) nil
					(let ((form (read *standard-input* nil magic-eof-cookie)))
					  (when (symbolp form)
					    (setq form (intern (symbol-name form) sw-shell-pkg)))
					  (cond ((member form '(quit exit))
						 (setq exiting-lisp? t)
						 (specware::exit))
						((eq form 'ok)
						 (return))
						((not (eq form magic-eof-cookie))
						 (let ((results
							(multiple-value-list 
							 (sw-shell-command *current-command-processor*
									   form))))
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
						 (specware::exit))
						(t
						 (format t "~&Received EOF.~%"))))))))
      
      (set-specware-shell nil)
      (unless exiting-lisp?
	(format t "~%~A~%" exit-message)))))

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
  (setq emacs::*use-emacs-interface?* nil)
  (#+allegro excl:without-package-locks #-allegro progn
   (setf (symbol-function 'error) #'just-print-error-message))
  (specware::change-directory (specware::getenv "SPECWARE4"))
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
  (aux-specware-shell exiting-lisp? #'process-sw-shell-command))

(defvar *sw-shell-pkg* (find-package :SWShell))

(defvar *commands-in-process* 0)

;;; Used by slime-based interface
;;; From slime.el:  (defvar sw:*shell-command-function* "SWShell::process-raw-command")
(defun process-raw-command (command argstr)
  ;; Note: swank will barf on command lines such as 
  ;; '(33 33 33) 
  ;; before it ever reaches here, parsing it as  
  ;;  '(33   "33 33)"
  ;; But we can at least deal gracefully with whatever does reach here.
  (incf *commands-in-process*)
  (let ((val (multiple-value-list
	      (funcall *current-command-processor*
		       (if (symbolp command)
			   (intern (symbol-name command) *sw-shell-pkg*) 
			   command)
					argstr))))
    (decf *commands-in-process*)
    (if (null val)
	(swank::repl-suppress-output)
	(values-list val))))

;; Specware uses this for *current-command-processor*
;; Other systems (e.g. prism or accord) may use related functions...
(defun process-sw-shell-command (command argstr)
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
			  (princ (namestring (specware::current-directory)))
			  (specware::cd argstr))
		      (values))
	   (pwd       (princ (namestring (specware::current-directory))) (values))
	   ((dir ls)       (cl-user::ls     (or argstr "")))
	   (dirr      (cl-user::dirr   (or argstr "")))
	   (path      (cl-user::swpath argstr))
	   ((proc p)  (cl-user::sw     argstr) (values))
	   ((reproc rp)  (let ((cl-user::*force-reprocess-of-unit* t)) (cl-user::sw     argstr)) (values))
	   (show      (cl-user::show   argstr) (values))
	   (showx     (cl-user::showx  argstr) (values))
	   (cinit     (cl-user::sw-init))
	   (gen-lisp  (cl-user::swl    argstr) (values))
	   (lgen-lisp (cl-user::swll   argstr) (values))
	   (gen-c     (cl-user::swc    argstr) (values))
	   (make      (if (null argstr) (cl-user::make) (cl-user::make argstr)))
	   (gen-java  (cl-user::swj    argstr) (values))
	   ((obligations oblig obligs)
	    (cl-user::show   (concatenate 'string "obligations "
                                          (if (null argstr)
                                              cl-user::*last-unit-Id-_loaded*
                                              (cl-user::norm-unitid-str argstr))))
	    (values))
	   ((gen-obligations gen-oblig gen-obligs)
	    (let ((TypeObligations::generateTerminationConditions? nil)
		  (TypeObligations::generateExhaustivityConditions? nil)
                  (TypeObligations::omitDefSubtypeConstrs? t)
		  (Prover::treatNatSpecially? nil)
		  (uid (if (not (null argstr))
			   argstr
			   (if (not (null cl-user::*last-unit-Id-_loaded*))
			       cl-user::*last-unit-Id-_loaded*
			       (progn (format t "No previous unit processed~%")
				      nil)))))
	      (unless (null uid)
		(setq cl-user::*last-unit-Id-_loaded* uid)
		(IsaTermPrinter::printUIDtoThyFile-2 uid t))))
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
			  (if (string= argstr "None")
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

	   ((lisp l)  (with-break-possibility (lisp-value (multiple-value-list (eval (read-from-string argstr))))))
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
	   ((trace-rewrites trr) (setq MetaSlangRewriter::traceRewriting 2)
	                         (format t "Rewrite tracing turned on.")
	                         (values))
	   ((untrace-rewrites untrr) (setq MetaSlangRewriter::traceRewriting 0)
	                             (format t "Rewrite tracing turned off.")
	                             (values))
;;      (bash      (cl-user::bash argstr))
	   ;;
	   (t 
	    (format t "Unknown command `~a'. Type `help' to see available commands."
		    (string-downcase command))
	    (values))))
	((and (constantp command) (null argstr))
	 (values command))
	(t
	 (format t "Unknown command `~S'. Type `help' to see available commands."
		 command))))

