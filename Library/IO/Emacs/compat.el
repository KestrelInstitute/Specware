(defvar lisp-emacs-interface-type 'franz)
(defvar sw:common-lisp-buffer-name "*specware*")

(pushnew ".fasl" completion-ignored-extensions)
(pushnew ".x86f" completion-ignored-extensions)	; cmulisp
(pushnew ".dfsl" completion-ignored-extensions)	; mcl

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
  (defvar *specware-lisp* 'allegro)
  (defvar *lisp-image-extension* "dxl")
  (define-function 'sw:exit-lisp 'fi:exit-lisp)
  (define-function 'sw:switch-to-lisp 'fi:toggle-to-lisp)
  (define-function 'extract-sexp 'fi:extract-list)
  (define-function 'sw:eval-in-lisp 'fi:eval-in-lisp)
  (defun sw:eval-in-lisp-no-value (str &rest args)
    (apply 'fi:eval-in-lisp str args)
    t)
  (defun sw:eval-in-lisp-dispatch (str &rest args)
    (apply 'fi:eval-in-lisp-asynchronous str args)
    t)
  (define-function 'inferior-lisp-newline 'fi:inferior-lisp-newline)
  (define-function 'inferior-lisp-running-p 'fi::lep-open-connection-p)
  (define-function 'sw:find-unbalanced-parenthesis 'fi:find-unbalanced-parenthesis)
  (defvar *specware-buffer-name* sw:common-lisp-buffer-name)
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
  (defvar *specware-lisp* 'cmulisp)
  (defvar *lisp-image-extension* "cmuimage")
  (defun sw:common-lisp (common-lisp-buffer-name
			 common-lisp-directory
			 &optional
			 common-lisp-image-name
			 common-lisp-image-arguments
			 common-lisp-host
			 common-lisp-image-file)
    (setq sw:common-lisp-buffer-name common-lisp-buffer-name)
    ;; cmulisp adds the *'s back
    (funcall *specware-lisp*
	     (subseq common-lisp-buffer-name
		     1 (- (length common-lisp-buffer-name) 1))
	     (if common-lisp-image-file
		 (case *specware-lisp*
		   (cmulisp
		     (concat common-lisp-image-name
			     " -core " common-lisp-image-file))
		   (otherwise
		     (concat common-lisp-image-name " "
			     common-lisp-image-file)))
	       common-lisp-image-name)
;	     (concat common-lisp-image-name " "
;                     (if common-lisp-image-arguments
;                         common-lisp-image-arguments "")
;                     (if common-lisp-image-file
;                         (concat " -I " common-lisp-image-file) ""))
	     )
    (install-bridge-for-emacsEval))
  ;; Handling emacs-eval emacsEval  (could be more robust!)
  (defun emacs-eval-handler (process output)
    (when output
     (eval (car (read-from-string output)))))

  (defun install-bridge-for-emacsEval ()
    (require 'bridge)
    (set-buffer *specware-buffer-name*)
    (install-bridge)
    (setq bridge-source-insert nil)
    (setq bridge-handlers '(("(" . emacs-eval-handler))))

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
    (interactive)
    (simulate-input-expression ":quit")
    )

  (defun sw:switch-to-lisp (&optional eob-p)
    (interactive "P")
    (if (equal (buffer-name (current-buffer))
	       *specware-buffer-name*)
	(lisp-pop-to-buffer ilisp-last-buffer nil t)
      (progn (setq ilisp-last-buffer (current-buffer))
	     (lisp-pop-to-buffer *specware-buffer-name* nil t)))
    (when eob-p
      (goto-char (point-max))))

  (defun sw:eval-in-lisp (str &rest args)
    (car (read-from-string (ilisp-send (apply 'format str args)))))

  (defun sw:eval-in-lisp-no-value (str &rest args)
    (ilisp-send (apply 'format str args))
    t)

  (defun sw:eval-in-lisp-dispatch (str &rest args)
    (ilisp-send (apply 'format str args) nil nil t)
    t)

  (define-function 'inferior-lisp-newline 'return-ilisp)

  (defun sw:find-unbalanced-parenthesis ()
    (interactive)
    (find-unbalanced-region-lisp (point-min) (point-max)))

  (defvar *specware-buffer-name* "*specware*")

  ;(push 'specware-mode ilisp-modes)

  (defun inferior-lisp-running-p ()
    (and (get-buffer-process *specware-buffer-name*)
	 (buffer-live-p (get-buffer *specware-buffer-name*))
	 (with-current-buffer *specware-buffer-name*
	   (not (equal comint-status " :exit")))))
  
  (defun add-specware-listener-key-bindings (m)
    (define-key m "\e." 'sw:meta-point)
    (easy-menu-define specware-interaction-buffer-menu
		      m
		      "Menu used in Specware buffer."
		      specware-interaction-menu)
    (easy-menu-add specware-interaction-buffer-menu m))

  (defun specware-listener-mode-hook ()
    (and ilisp-mode-map
	 (add-specware-listener-key-bindings ilisp-mode-map)))
  (add-hook 'ilisp-mode-hook 'specware-listener-mode-hook t)
)

