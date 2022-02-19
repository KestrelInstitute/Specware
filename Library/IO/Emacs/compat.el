(require 'sw-init)
(require 'specware-mode)

(defvar lisp-emacs-interface-type 'franz)
(defvar sw:common-lisp-buffer-name "*Specware Shell*")
(defvar sw:common-lisp-image-arguments nil)

(cl-pushnew ".fasl" completion-ignored-extensions)
(cl-pushnew ".x86f" completion-ignored-extensions)	; cmulisp
(cl-pushnew ".dfsl" completion-ignored-extensions)	; openmcl
(cl-pushnew ".sfsl" completion-ignored-extensions)	; sbcl
(cl-pushnew ".fas"  completion-ignored-extensions)	; clisp

(defvar *lisp-prompt-regexp*)
(defvar lisp-prev-l/c-dir/file)

(defvar lisp-program (or (getenv "LISP_EXECUTABLE") (getenv "LISP") "/usr/local/bin/sbcl"))

(defvar expand-symlinks-rfs-exists t)

(defvar *specware-lisp* (if (or (cl-search "alisp" lisp-program)
				(cl-search "build" lisp-program) ; ??
				;; for now, we use allegro on windows...
			        ;(featurep 'mswindows)
			        ;(featurep 'windows-nt)
                                )
			    'allegro
			  (if (cl-search "dppccl" lisp-program)
			      'openmcl
			    (if (cl-search "sbcl" lisp-program)
				'sbcl
				(if (cl-search "gcl" lisp-program)
				    'gcl
				  'sbcl)))))
(defvar *lisp-executable-extension*
  (if *windows-system-p*
      "exe"
    (cl-case *specware-lisp*
      (openmcl "mclexe")
      (cmulisp "cmuexe")
      (sbcl    "sbclexe")
      (allegro "aclexe")
      (gcl     "gclexe"))))

(defvar *lisp-image-extension*
  (cl-case *specware-lisp*
    (openmcl "openmcl-image")
    (cmulisp "cmuimage")
    (sbcl    "sbclimage")
    (allegro "dxl")
    (gcl     "gclimage")))

(defvar *fasl-extension*
  (cl-case *specware-lisp*
    (allegro "fasl")
    (mcl     "dfsl")
    (cmu     "x86f")
    (sbcl    "sfsl")
    (gcl     "o")))

(defvar *macos-p* (= (shell-command "ls /mach_kernel") 0))  ; or any other test that tells us we're on a Mac

(defvar *sbcl-size*
  (let ((given (getenv "SBCL_SIZE")))
    (if (null given)
        (if *windows-system-p* 1000 (if *macos-p* 4000 2400))
      (read given)))
  "Size of --dynamic-space-size for sbcl")

(defvar *sbcl-stack-size*
  (let ((given (getenv "SBCL_STACK_SIZE")))
    (if (null given) 4 (read given))) ; Default is 2 (megabytes)
  "Size of --control-stack-size for sbcl")

(defun ensure-list (fm-str)
  (if (equal (elt fm-str 0) (elt "(" 0))
      fm-str
    (format "(progn %s)" fm-str)))

(when (eq lisp-emacs-interface-type 'slime)
  (defvar slime-*directory*)
  (setq slime-*directory*
	(concat (getenv "SPECWARE4") "/Library/IO/Emacs/slime/"))
  (defvar slime-*use-fsf-compliant-keybindings* t) ; Use c-c as command prefix (not c-z)
  (require 'slime)
  (setq inferior-lisp-program lisp-program)
  (setq expand-symlinks-rfs-exists t)
  (defvar slime-multiprocessing
    (cl-case *specware-lisp*
      (allegro   t)
      (openmcl   t)
      (cmu       t)
      (sbcl      t)
      (gcl       nil)
      (otherwise nil)))
  (defvar specware-listener-p nil)
  (defun sw:common-lisp (common-lisp-buffer-name
			 common-lisp-directory
			 &optional
			 common-lisp-image-name
			 common-lisp-image-arguments
			 common-lisp-host
			 common-lisp-image-file)
    (setq sw:common-lisp-buffer-name common-lisp-buffer-name)
    (setq specware-listener-p t)
    (let ((specware-listener-p t))
      (slime-start ;:buffer sw:common-lisp-buffer-name
                   :program common-lisp-image-name
		   :program-args
		   (cl-case *specware-lisp*
		     ((cmulisp sbcl)
		      (if common-lisp-image-file
			  (list "-core" common-lisp-image-file)
                        (list "--dynamic-space-size" (format "%s" *sbcl-size*)           ; %s prints strings without quotes
                              "--control-stack-size" (format "%s" *sbcl-stack-size*))))  ; %s prints strings without quotes
		     (allegro (concat common-lisp-image-arguments
				      (if common-lisp-image-file
					  (list "-I" common-lisp-image-file)
					())
				      (if *windows-system-p*
					  '("-e" "'(setf (eol-convention *standard-output*) :unix)'")
					())))
		     (gcl common-lisp-image-file) ; Don't use common-lisp-image-name
		     (otherwise (if (null common-lisp-image-file)
				    ()
				  (list common-lisp-image-file))))
		   ))
    ;(install-bridge-for-emacsEval)
    ;(set-default-directory common-lisp-directory)
    )
  (defun set-default-directory (dir)
    (with-current-buffer (get-buffer sw:common-lisp-buffer-name)
      (setq default-directory dir)
      (setq lisp-prev-l/c-dir/file (cons default-directory nil))))
  ;; Handling emacs-eval emacsEval  (could be more robust!)
  (defun emacs-eval-handler (process output)
    (when output
     (eval (car (read-from-string output)))))

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
    (slime-repl-previous-input))

  (defun sw:exit-lisp ()
    (interactive)
    (lisp-or-specware-command-quiet ":quit" "quit"))

  (defvar slime-last-buffer nil)

  (defun sw:switch-to-lisp (&optional eob-p)
    (interactive "P")
    (if (equal (buffer-name (current-buffer))
	       sw:common-lisp-buffer-name)
	(pop-to-buffer slime-last-buffer nil)
      (progn (setq slime-last-buffer (current-buffer))
	     (pop-to-buffer sw:common-lisp-buffer-name nil)))
    (when eob-p
      (goto-char (point-max))))

  (defun sw:eval-in-lisp (str &rest args)
    (ensure-specware-running)
    (let ((fm (read-from-string (ensure-list (apply 'format str args)))))
      (if (null fm)
	  (warn "Can't read form to be evaluated")
	(slime-eval (car fm)))))

  (defun sw:eval-in-lisp-no-value (str &rest args)
    (ensure-specware-running)
    (let ((fm (read-from-string (ensure-list (apply 'format str args)))))
      (if (null fm)
	  (warn "Can't read form to be evaluated")
	(slime-eval-async (car fm))))
    t)

  (defun sw:eval-in-lisp-dispatch (str &rest args)
    (ensure-specware-running)
    (let ((fm (read-from-string (ensure-list (apply 'format str args)))))
      (if (null fm)
	  (warn "Can't read form to be evaluated")
	(slime-eval-async (car fm))))
    t)

  (fset 'inferior-lisp-newline 'sw-return)

  (defun sw:find-unbalanced-parenthesis ()
    (interactive)
    (check-parens))

  (defvar *specware-buffer-name* "*Specware Shell*")

  ;(setq slime-find-buffer-package-function 'slime-lisp-package)
  (setq slime-enable-evaluate-in-emacs t)

  ;(push 'specware-mode slime-modes)

  (defun inferior-lisp-running-p ()
    (let ((conn (slime-current-connection)))
      (and conn
	   (eq (process-status conn) 'open))))

)
  ;(add-hook 'slime-repl-mode-hook 'specware-listener-mode-hook t)

(defun replace-all (str1 str2)
  (goto-char (point-min))
  (while (search-forward str1 nil t)
    (replace-match str2 nil t)))

(defun in-comment-or-string-p ()
  (let ((face (or (get-char-property (point) 'read-face-name)
                  (get-char-property (point) 'face))))
    (member face '(font-lock-comment-face font-lock-string-face))))
