(defpackage :SWShell)
(in-package :SWShell)

(defparameter *prompt* "* ")
(defparameter eofs-before-quit 2)
(defvar *in-specware-shell?* nil)
(defvar *last-eval-expr* nil)
;(defparameter *specware-shell-readtable* (make-readtable))

(defun specware-shell ()
  (let  ((magic-eof-cookie (cons :eof nil))
	 (number-of-eofs 0)
	 (cl:*package* (find-package :SWShell)))
    (setq *in-specware-shell?* t)
    (emacs::eval-in-emacs "(set-comint-prompt t)")
    (format t "Specware Shell~%")
    (unwind-protect
	(loop
	  (fresh-line)
	  (princ *prompt*)
	  (force-output)
	  (with-simple-restart (abort "Return to Specware Shell top level.")
	    (let ((form (read *standard-input* nil magic-eof-cookie)))
	      (cond ((member form '(quit exit ok))
		     (if (equal (read-line *standard-input* nil magic-eof-cookie) "l")
			 (cl-user::exit)
		       (return)))
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
		     (format t "~&Received EOF.~%"))))))
      
      (setq *in-specware-shell?* nil)
      (emacs::eval-in-emacs "(set-comint-prompt nil)")
      (format t "~%Exiting Specware Shell. :sw-shell to reenter."))))

(defun sw-shell-command (command)
  (let ((ch (read-char-no-hang)))
    (when ch
      (unread-char ch))
    (if (or (null ch)          ; interactive, end of command
	    (eq ch #\Newline)) ; batch, first char after whitespace is newline      
	(process-sw-shell-command command nil)
      (process-sw-shell-command command (read-line)))))

(defun process-sw-shell-command (command argstr)
  (case command
    (help (let ((cl-user::*sw-help-strings* *sw-shell-help-strings*))
	    (cl-user::sw-help argstr)))
    (cd (if (null argstr)
	    (princ (namestring (specware::current-directory)))
	  (cl-user::cd argstr))
	(values))
    (dir (cl-user::ls (or argstr "*.sw")))
    (dirr (cl-user::dirr (or argstr "*.sw")))
    (path (cl-user::swpath argstr))
    ((proc p) (cl-user::sw argstr) (values))
    (show (cl-user::show argstr) (values))
    (cinit (cl-user::sw-init))
    (gen-lisp (cl-user::swl argstr) (values))
    (lgen-lisp (cl-user::swll argstr) (values))
    (punits (cl-user::swpf argstr))
    (lpunits (cl-user::swpf argstr))	; No local version yet
    (ctext (if (null argstr)
	       (progn (if cl-user::*current-swe-spec*
			  (format t "~&Current context: ~a" cl-user::*current-swe-spec*)
			(format t "~&Current context: Base Spec"))
		      (values))
	     (cl-user::swe-spec argstr)))
    ((eval e) (let ((cl-user::*swe-use-interpreter?* t)
		    (argstr (or argstr *last-eval-expr*))
		    (cl-user::*expr-begin-offset* -12))
		(if (null argstr)
		    (warn "No previous eval command.")
		  (progn (setq *last-eval-expr* argstr)
			 (cl-user::swe argstr)
			 (values)))))
    (eval-lisp (let ((cl-user::*swe-use-interpreter?* nil)
		     (argstr (or argstr *last-eval-expr*)))
		 (if (null argstr)
		     (warn "No previous eval command.")
		   (progn (setq *last-eval-expr* argstr)
			  (cl-user::swe argstr)
			  (values)))))
    ((lisp l) (let ((cl:*package* (find-package "CL-USER")))
		(eval (read-from-string argstr))))
    (cl (cl-user::cl argstr))
    (ld (cl-user::ld argstr))
    (com (multiple-value-bind (command pos)
	     (let ((cl:*package* (find-package "CL-USER")))
		(read-from-string argstr))
	   (if (fboundp command)
	       (funcall command (subseq argstr pos))
	     (format t "Unknown command."))))
    (t (format t "Unknown command. Type `help' to see available commands.")
       (values))))

(defparameter *sw-shell-help-strings*
  '(("help" . "[command] Prints help information for command, or, with no argument, all commands.")
    ("cd" . "[dir] Connect to directory. With no argument, displays the current directory.")
    ("dir" . "List .sw files in current directory.")
    ("dirr" . "List .sw files in current directory and recursively in subdirectories.")
    ("path" . "[dirseq] Sets the current Specware path.
                  With no argument, displays the current Specware path.")
    ("proc" . "[unit-term] Processes the unit. 
                  With no argument, processes the last processed unit.")
    ("show" . "[unit-term] Like `proc' but in addition displays the value of the processed unit-term.")
    ("cinit" . "Clears Spec unit cache.")
    ("gen-lisp" . "[spec-term [filename]] Generates Lisp code for unit in filename.
                  With no argument uses last processed unit.")
    ("lgen-lisp" . "[spec-term [filename]] Like `gen-lisp' but only generates lisp for local definitions of spec..")
    ("punits" . "[unit-term [filename]] Generates proof unit definitions for all conjectures in the unit and puts
                  them into filename.")
    ("lpunits" . "[unit-term [filename]] Like `punits' but only for local conjectures.")
    ("ctext" . "[spec-term] Sets the current context for eval commands.
                  With no arguments displays context.")
    ("eval" . "[expression] Evaluates expression with respect to current context.")
    ("eval-lisp" . "[expression] Like `eval' except the expression is translated to Lisp and evaluated in Lisp.")
    ("exit" . "Exits shell.")
    ))

;;; Add commands for entering shell from Lisp shell
(defun cl-user::sw-shell ()
  (specware-shell))

#+allegro
(top-level:alias ("sw-shell") () (specware-shell))

(setq cl-user::*sw-help-strings*
  (concatenate 'list cl-user::*sw-help-strings*
	       '((":sw-shell" . "Run Specware Shell"))))