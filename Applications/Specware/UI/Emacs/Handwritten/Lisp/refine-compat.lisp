;; Emacs-lisp interaction in terms of re::
;; for continuous compatibility.

(defpackage :re)
(defpackage :sp)

(in-package "RE")

(defun re::emacs-eval (string)
  #+allegro(lep::eval-in-emacs string)
  #+Lispworks(eval string))

;;----------------------------

(defpackage :emacs)
(defvar emacs::*procs* 0)

(defun emacs::make-process (sym)
  ;; *terminal-io* is already a background stream
  (let* 
      ((procNum emacs::*procs*)
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
    (setq emacs::*procs* (1+ procNum))
    procName))

       
(defun my-eval (x)
  (let ((*standard-input* *terminal-io*)
	(*standard-output* *terminal-io*))
    (eval x)))

(defun emacs::kill-process (procName)
  (mp::process-kill (mp::process-name-to-process procName)))


(defvar emacs::*browser-bin* "netscape ")

;;; sjw: 3/15/01 Use -remote instead of starting a new netscape image
(defun sp::call-netscape-with-url (url)
  (run-shell-command
   (format nil "~A -remote \"openURL(~A)\"" emacs::*browser-bin* url)
   ;(concatenate 'string emacs::*browser-bin* "  " url)
   :wait nil)
  )
