(defvar lisp-emacs-interface-type 'franz)
(defvar sw:common-lisp-buffer-name "*common-lisp*")

(when (or (eq lisp-emacs-interface-type 'franz))
  (defun sw:common-lisp (common-lisp-buffer-name
			 common-lisp-directory
			 &optional
			 common-lisp-image-name
			 common-lisp-image-arguments
			 common-lisp-host
			 common-lisp-image-file)
    (setq sw:common-lisp-buffer-name common-lisp-buffer-name)
    (setq fi:common-lisp-buffer-name common-lisp-buffer-name)
    (setq fi:common-lisp-directory common-lisp-directory)
    (setq fi:common-lisp-image-name common-lisp-image-name)
    (setq fi:common-lisp-image-arguments common-lisp-image-arguments)
    (setq fi:common-lisp-host common-lisp-host)
    (setq fi:common-lisp-image-file common-lisp-image-file)
    (fi:common-lisp common-lisp-buffer-name
		    common-lisp-directory
		    common-lisp-image-name
		    common-lisp-image-arguments
		    common-lisp-host
		    common-lisp-image-file))
  (define-function 'sw:exit-lisp 'fi:exit-lisp)
  (define-function 'sw:switch-to-lisp 'fi:toggle-to-lisp)
  (define-function 'extract-sexp 'fi:extract-list)
  (define-function 'sw:eval-in-lisp 'fi:eval-in-lisp)
  (define-function 'inferior-lisp-newline 'fi:inferior-lisp-newline)
  (define-function 'inferior-lisp-running-p 'fi::lep-open-connection-p)
  (define-function 'sw:find-unbalanced-parenthesis 'fi:find-unbalanced-parenthesis)
  (defvar *specware-buffer-name* fi:common-lisp-buffer-name)
  (when (and (boundp 'fi:lisp-mode-syntax-table)
	     fi:lisp-mode-syntax-table)
    (modify-syntax-entry ?. "." fi:lisp-mode-syntax-table)))

(when (eq lisp-emacs-interface-type 'ilisp)
  (setq ilisp-*directory*
	(concat (getenv "SPECWARE4") "/Library/IO/Emacs/ilisp/"))
  (defvar ilisp-*use-fsf-compliant-keybindings* t) ; Use c-c as command prefix (not c-z)
  (unless (fboundp 'run-ilisp)
    (load "ilisp/ilisp"))
  (setq allegro-program (getenv "LISP_EXECUTABLE"))
  (setq expand-symlinks-rfs-exists t)	; ?
  (defun sw:common-lisp (common-lisp-buffer-name
			 common-lisp-directory
			 &optional
			 common-lisp-image-name
			 common-lisp-image-arguments
			 common-lisp-host
			 common-lisp-image-file)
    (setq sw:common-lisp-buffer-name common-lisp-buffer-name)
    (allegro common-lisp-buffer-name
	     (concat common-lisp-image-name " "
		     (if common-lisp-image-arguments
			 common-lisp-image-arguments "")
		     (if common-lisp-image-file
			 (concat " -I " common-lisp-image-file) ""))))
  (defun extract-sexp ()
    "Delete the S-expression containing the S-expression that starts at point
     and replace it with the S-expression that starts at the point."
    (interactive)
    (let ((start (point))
	  (end nil)
	  (mine nil))
      (forward-sexp 1)
      (setq end (point))
      (setq mine (buffer-substring start end))
      (up-list -1)
      (setq start (point))
      (forward-sexp 1)
      (delete-region start (point))
      (insert mine)
      (backward-sexp)))
  (defun sw:exit-lisp ()
    )
  (defun sw:switch-to-lisp (&optional EOB-P)
    (switch-to-lisp EOB-P))
  (defun sw:eval-in-lisp (&rest args)
    (car (read-from-string (ilisp-send (apply 'format args)))))
  (define-function 'inferior-lisp-newline 'return-ilisp)
  (defun sw:find-unbalanced-parenthesis ()
    (find-unbalanced-region-lisp (point-min) (point-max)))
  (defvar *specware-buffer-name* "common-lisp")
  (push 'specware-mode ilisp-modes)
  (defun inferior-lisp-running-p ()
    (with-current-buffer *specware-buffer-name*
      (not (equal comint-status " :exit")))))

