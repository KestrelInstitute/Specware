(defpackage :SWShell)
(in-package :SWShell)

(defparameter *prompt* "* ")
(defparameter eofs-before-quit 2)
(defvar *in-specware-shell?* nil)
(defvar *last-eval-expr* nil)
(defvar *developer?* nil)
;(defparameter *specware-shell-readtable* (make-readtable))

(defparameter *sw-shell-help-strings*
  '(("help" . "[command] Prints help information for command, or, with no argument, all commands.")
    ("cd" . "[dir] Connect to directory. With no argument, displays the current directory.")
    ("dir" . "List .sw files in current directory.")
    ("dirr" . "List .sw files in current directory and recursively in subdirectories.")
    ("path" . "[dirseq] Sets the current Specware path.
                  With no argument, displays the current Specware path.")
    ("proc" . "[unit-term] Processes the unit. 
                  With no argument, processes the last processed unit.")
    ("p" . "[unit-term] Abbreviation for proc.")
    ("show" . "[unit-term] Like `proc' but in addition displays the value of the processed unit-term.")
    ("showx" . "[unit-term] Like `show' but shows all types and ops including imports.")
    ("cinit" . "Clears Spec unit cache.")    
    ("punits" . "[unit-term [filename]] Generates proof unit definitions for all conjectures in the unit and puts
                  them into filename.")
    ("lpunits" . "[unit-term [filename]] Like `punits' but only for local conjectures.")
    ("ctext" . "[spec-term] Sets the current context for eval commands.
                  With no arguments displays context.")
    ("eval" . "[expression] Evaluates expression with respect to current context.")
    ("e" . "[expression] Abbreviation for eval.")
    ("eval-lisp" . "[expression] Like `eval' except the expression is translated to Lisp and evaluated in Lisp.")
    ("gen-lisp" . "[spec-term [filename]] Generates Lisp code for unit in filename.
                  With no argument uses last processed unit.")
    ("lgen-lisp" . "[spec-term [filename]] Like `gen-lisp' but only generates lisp for local definitions of spec.")
    ("gen-c" . "[spec-term [filename]] Generates C code for unit in filename.
                  With no argument uses last processed unit.")
    ("make" . "[spec-term] Generate C code with makefile and call make on it.")
    ("gen-java" . "[spec-term [filename]] Generates Java code for unit in filename.
                  With no argument uses last processed unit.")
; obsolete
;    ("j-config" . "Show configuration parameters for Java generation.")
;    ("j-config-dir" . "[dir] Set base directory to be used by gen-java.")
;    ("j-config-make-public" . "[names] Set public names to be used by gen-java.")
;    ("j-config-pkg" . "[pkg] Set package name to be used by gen-java.")
;    ("j-config-reset" . "Restore default configuration parameters for Java generation.")
    ("cf" . "[filename] Compile lisp file filename.")
    ("ld" . "[filename] Load lisp file filename.")
    ("cl" . "[filename] Compile and load lisp file filename.")
    ("exit" . "Exits shell and Lisp.")
    ("quit" . "Alias for exit.")
    ("ok"   . "Exits shell.")
    ))

(defparameter *sw-shell-dev-help-strings*
  '(("set-base" . "[unit-id] Sets base spec to unit-id")
    ("lisp" . "[lisp expr] Evaluate lisp expression.")
    ("l" . "[lisp expr] Abbreviation for lisp.")
    ("tr" . "[lisp function names] Trace functions.")
    ("untr" . "Untrace all traced functions.")
    ("f-b" . "[lisp function names] Break functions.")
    ("f-unb" . "[lisp function names] Unreak functions. No argument means all broken functions")
    ("dev" . "[on] Set *developer?*. No argument gives current setting.")
    ("wiz" . "[on] Set SpecCalc::specwareWizard?. No argument gives current setting.")
    ("swdbg" . "[on] Set System-spec::specwareDebug?. No argument gives current setting.")))

(defun print-shell-prompt () (princ *prompt* *standard-output*))

(defvar *emacs-eval-form-after-prompt* nil)

(defun set-specware-shell (val)
  (setq *in-specware-shell?* val))

(defun in-specware-shell? ()
  *in-specware-shell?*)

(defun specware-shell0 ()
  (specware-shell t))

(defun specware-shell (exiting-lisp?)
  (let  ((magic-eof-cookie (cons :eof nil))
	 (number-of-eofs 0)
	 (cl:*package* (find-package :SWShell))
	 ch)
    (emacs::eval-in-emacs "(set-comint-prompt)")
    (format t "Specware Shell~%")
    (unwind-protect
	(loop
	  (set-specware-shell t)
	  (fresh-line *standard-output*)
	  (print-shell-prompt)
	  (when *emacs-eval-form-after-prompt*
	    (emacs::eval-in-emacs *emacs-eval-form-after-prompt*)
	    (setq *emacs-eval-form-after-prompt* nil))
	  (catch ':top-level-reset	; Only useful for allegro
	    (with-simple-restart (abort "Return to Specware Shell top level.")
					;(set-specware-shell t)
	      (loop while (member (setq ch (read-char *standard-input* nil nil)) '(#\Newline #\Space #\Tab))
		    do (when (eq ch #\Newline)  ; If user types a newline give a new prompt
			 (print-shell-prompt)))
	      (when ch
		(unread-char ch))
	      (catch #+allegro 'tpl::top-level-break-loop
		     #-allegro nil
		(let ((form (read *standard-input* nil magic-eof-cookie)))
		  (cond ((member form '(quit exit))
			 (setq exiting-lisp? t)
			 (cl-user::exit))
			((eq form 'ok)
			 (return))
			((not (eq form magic-eof-cookie))
			 (let ((results
				(multiple-value-list (sw-shell-command form))))
			   (dolist (result results)
			     (fresh-line)
			     (prin1 result)))
			 (setf number-of-eofs 0))
			((eql (incf number-of-eofs) 1)
			 (let ((stream (make-synonym-stream '*terminal-io*)))
			   (setf *standard-input* stream)
			   (setf *standard-output* stream)
			   (format t "~&Received EOF on *standard-input*, ~
				  switching to *terminal-io*.~%")))
			((> number-of-eofs eofs-before-quit)
			 (format t "~&Received more than ~D EOFs; Aborting.~%"
				 eofs-before-quit)
			 (cl-user::exit))
			(t
			 (format t "~&Received EOF.~%"))))))))
      
      (set-specware-shell nil)
      (unless exiting-lisp?
	(format t "~%Exiting Specware Shell. :sw-shell to reenter.")))))

(defun sw-shell-command (command)
  (let ((ch (read-char-no-hang *standard-input* nil nil)))
    (when ch
      (unread-char ch))
    (if (or (null ch)          ; interactive, end of command
	    (eq ch #\Newline)) ; batch, first char after whitespace is newline      
	(process-sw-shell-command command nil)
      (process-sw-shell-command command (read-line)))))

(defmacro with-break-possibility (&rest fms)
  `(progn (set-specware-shell nil)
	  ,@fms))

(defun process-sw-shell-command (command argstr)
  (if (and (consp command) (null argstr))
      (progn (eval command))
    (case command
      (help (let ((cl-user::*sw-help-strings*
		   (if *developer?*
		       (concatenate 'list *sw-shell-help-strings* *sw-shell-dev-help-strings*)
		     *sw-shell-help-strings*)))
	      (cl-user::sw-help argstr)))
      (cd (if (null argstr)
	      (princ (namestring (specware::current-directory)))
	    (cl-user::cd argstr))
	  (values))
      (dir (cl-user::ls (or argstr "")))
      (dirr (cl-user::dirr (or argstr "")))
      (path (cl-user::swpath argstr))
      ((proc p) (cl-user::sw argstr) (values))
      (show (cl-user::show argstr) (values))
      (showx (cl-user::showx argstr) (values))
      (cinit (cl-user::sw-init))
      (gen-lisp (cl-user::swl argstr) (values))
      (lgen-lisp (cl-user::swll argstr) (values))
      (gen-c (cl-user::swc argstr) (values))
      (make (cl-user::make argstr))
      (gen-java (cl-user::swj argstr) (values))
; obsolete
;      (j-config (cl-user::swj-config))
;      (j-config-dir (cl-user::swj-config-dir argstr))
;      (j-config-make-public (cl-user::swj-config-make-public argstr))
;      (j-config-pkg (cl-user::swj-config-pkg argstr))
;      (j-config-reset (cl-user::swj-config-reset))
      (punits (cl-user::swpf argstr))
      (lpunits (cl-user::lswpf argstr))	; No local version yet
      (ctext (if (null argstr)
		 (progn (if cl-user::*current-swe-spec*
			    (format t "~&Current context: ~a" cl-user::*current-swe-spec*)
			  (format t "~&Current context: Base Spec"))
			(values))
	       (if (string= argstr "None")
		   (progn (setq cl-user::*current-swe-spec* nil)
			  (format t "~&Subsequent evaluation commands will import just the base spec.~%"))
		 (cl-user::swe-spec argstr))))
      ((eval e) (let ((cl-user::*swe-use-interpreter?* t)
		      (argstr (or argstr *last-eval-expr*))
		      (cl-user::*expr-begin-offset* (if (eq command 'e) -12 -9)))
		  (if (null argstr)
		      (warn "No previous eval command.")
		    (progn (setq *last-eval-expr* argstr)
			   (cl-user::swe argstr)
			   (values)))))
      ((eval-lisp el) (let ((cl-user::*swe-use-interpreter?* nil)
			    (argstr (or argstr *last-eval-expr*))
			    (cl-user::*expr-begin-offset* (if (eq command 'el) -11 -4)))
			(if (null argstr)
			    (warn "No previous eval command.")
			  (progn (setq *last-eval-expr* argstr)
				 (cl-user::swe argstr)
				 (values)))))
      ;; Non-user commands
      (set-base (cl-user::set-base argstr))
      (show-base-unit-id (cl-user::show-base-unit-id))
      ((lisp l) (let ((cl:*package* (find-package "CL-USER")))
		  (with-break-possibility (eval (read-from-string argstr)))))
      (cl (with-break-possibility (cl-user::cl argstr)))
      (ld (with-break-possibility (cl-user::ld argstr)))
      (cf (cl-user::cf argstr))
      (tr (cl-user::tr argstr))
      (untr (cl-user::untr))
      (f-b (when (fboundp 'cl-user::f-b)
	     (cl-user::f-b argstr)))
      (f-unb (when (fboundp 'cl-user::f-unb)
	       (cl-user::f-unb (or argstr ""))))
      (dev (if argstr
	       (princ (setq *developer?* (if (member argstr '("nil" "NIL" "off") :test 'string=)
					     nil t)))
	     (princ *developer?*))
	   (values))
      (wiz (if argstr (cl-user::wiz argstr) (cl-user::wiz)))
      (swdbg (if argstr (cl-user::swdbg argstr) (cl-user::swdbg)))
      (com (let ((cl:*package* (find-package "CL-USER")))
	     (multiple-value-bind (command pos)
		 (read-from-string argstr)
	       (if (fboundp command)
		   (let ((com-argstr (subseq argstr pos)))
		     (if (string= com-argstr "")
			 (funcall command)
		       (funcall command com-argstr)))
		 (format t "Unknown command: ~a." command)))))
      (t (format t "Unknown command ~a. Type `help' to see available commands." command)
	 (values)))))

;;; Add commands for entering shell from Lisp shell
(defun cl-user::sw-shell ()
  (specware-shell nil))

#+allegro
(top-level:alias ("sw-shell") () (specware-shell nil))

(setq cl-user::*sw-help-strings*
  (concatenate 'list cl-user::*sw-help-strings*
	       '((":sw-shell" . "Run Specware Shell"))))
