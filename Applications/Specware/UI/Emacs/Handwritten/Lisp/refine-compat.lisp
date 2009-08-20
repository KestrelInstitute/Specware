;; Emacs-lisp interaction in terms of re::
;; for continuous compatibility.

;;----------------------------

(defpackage :emacs)
(in-package :emacs)

(defun re::emacs-eval (string)
  #+allegro(lep::eval-in-emacs string)
  #+Lispworks(eval string))

(defvar Emacs::*procs* 0)

#-mcl
(defun Emacs::make-process (sym)
  ;; *terminal-io* is already a background stream
  (let* 
      ((procNum Emacs::*procs*)
       (procName (format nil "Specware process : ~S" procNum)) 
       (proc #+allegro
	     (mp:process-run-function procName 
				      #'tpl:start-interactive-top-level
				      excl::*initial-terminal-io*
				      #'my-eval
				      (list sym))
	     #+Lispworks
	     (mp:process-run-function procName nil
				      #'my-eval
				      (list sym)))
       )
    (declare (ignore proc))
    (setq Emacs::*procs* (1+ procNum))
    procName))

       
(defun my-eval (x)
  (let ((*standard-input* *terminal-io*)
	(*standard-output* *terminal-io*))
    (eval x)))

(defun Emacs::kill-process (procName)
  (mp::process-kill (mp::process-name-to-process procName)))


(defvar Emacs::*browser-bin* "netscape ")

;;; sjw: 3/15/01 Use -remote instead of starting a new netscape image
(defun Specware::call-netscape-with-url (url)
  (run-shell-command
   (format nil "~A -remote \"openURL(~A)\"" Emacs::*browser-bin* url)
   ;(concatenate 'string Emacs::*browser-bin* "  " url)
   :wait nil)
  )
