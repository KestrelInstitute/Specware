;;; various stuff specific to ilisp, retained here for archival reasons

;;; --------------------------------------------------------------------------------
;;; from compat.el
;;; --------------------------------------------------------------------------------

(defvar ilisp-*directory*)
(defvar ilisp-last-buffer)
(defvar ilisp-last-buffer)
(defvar ilisp-modes)
(defvar comint-status)

(when (eq lisp-emacs-interface-type 'ilisp)
  (setq ilisp-*directory*
	(concat (getenv "SPECWARE4") "/Library/IO/Emacs/ilisp/"))
  (defvar ilisp-*use-fsf-compliant-keybindings* t) ; Use c-c as command prefix (not c-z)
  (unless (fboundp 'run-ilisp)
    (load "ilisp/ilisp"))
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
	     (cl-subseq common-lisp-buffer-name
                        1 (- (length common-lisp-buffer-name) 1))
	     (if common-lisp-image-file
		 (cl-case *specware-lisp*
		   ((cmulisp sbcl)
		     (if common-lisp-image-file
			 (concat common-lisp-image-name " -core " common-lisp-image-file)
		       common-lisp-image-name))
		   (allegro (concat common-lisp-image-name
				    " "
				    (apply #'concat common-lisp-image-arguments)
				    " -I "
				    common-lisp-image-file
				    (if *windows-system-p*
					" -e \"(setf (eol-convention *standard-output*) :unix)\""
				      "")))
		   (gcl common-lisp-image-file)	; Don't use common-lisp-image-name
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
    (install-bridge-for-emacsEval)
    (set-default-directory common-lisp-directory))
  (defun set-default-directory (dir)
    (with-current-buffer (get-buffer *specware-buffer-name*)
      (setq default-directory dir)
      (setq lisp-prev-l/c-dir/file (cons default-directory nil))))
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
  
  (defun previous-input-line ()
    (comint-previous-matching-input-from-input 1))

  (defun sw:exit-lisp ()
    (interactive)
    (eval-in-lisp-in-order "(cl-user::exit)"))

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
    (ensure-specware-running)
    (car (read-from-string (ilisp-send (ensure-list (apply 'format str args))))))

  (defun sw:eval-in-lisp-no-value (str &rest args)
    (ensure-specware-running)
    (ilisp-send (ensure-list (apply 'format str args)))
    t)

  (defun sw:eval-in-lisp-dispatch (str &rest args)
    (ensure-specware-running)
    (ilisp-send (ensure-list (apply 'format str args)) nil nil t)
    t)

  (fset 'inferior-lisp-newline 'return-ilisp)

  (defun sw:find-unbalanced-parenthesis ()
    (interactive)
    (find-unbalanced-region-lisp (point-min) (point-max)))

  (defvar *specware-buffer-name* "*Specware Shell*")
  
  ;(push 'specware-mode ilisp-modes)

  (defun inferior-lisp-running-p ()
    (and (get-buffer-process *specware-buffer-name*)
	 (buffer-live-p (get-buffer *specware-buffer-name*))
	 (with-current-buffer *specware-buffer-name*
	   (not (equal comint-status " :exit")))))
  
  (defun add-specware-listener-key-bindings (m)
    (define-key m '(tab) 'comint-dynamic-complete)
    (define-key m "\e." 'sw:meta-point)
    (define-key m "\C-c\C-d" 'ild-abort)
    (easy-menu-define specware-interaction-buffer-menu
		      m
		      "Menu used in Specware buffer."
		      specware-interaction-menu)
    (easy-menu-add specware-interaction-buffer-menu m))

  (defun specware-listener-mode-hook ()
    (setq comint-input-ring-size 100)
    (and (boundp 'ilisp-mode-map)
	 ilisp-mode-map
	 (add-specware-listener-key-bindings ilisp-mode-map))
;    (when sw:use-x-symbol
;      (x-symbol-mode 1)
;      (setq comint-input-sender 'x-symbol-comint-send))
    (push 'specware-listener-mode ilisp-modes))
  (add-hook 'ilisp-mode-hook 'specware-listener-mode-hook t)
)

