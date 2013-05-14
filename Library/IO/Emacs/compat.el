(defvar lisp-emacs-interface-type 'franz)
(defvar sw:common-lisp-buffer-name "*Specware Shell*")
(defvar sw:common-lisp-image-arguments nil)

(pushnew ".fasl" completion-ignored-extensions)
(pushnew ".x86f" completion-ignored-extensions)	; cmulisp
(pushnew ".dfsl" completion-ignored-extensions)	; openmcl
(pushnew ".sfsl" completion-ignored-extensions)	; sbcl
(pushnew ".fas"  completion-ignored-extensions)	; clisp

(defvar lisp-program (or (getenv "LISP_EXECUTABLE") (getenv "LISP") "/usr/local/bin/sbcl"))
(setq expand-symlinks-rfs-exists t)
(defvar *specware-lisp* (if (or (search "alisp" lisp-program)
				(search "build" lisp-program) ; ??
				;; for now, we use allegro on windows...
			        ;(featurep 'mswindows)
			        ;(featurep 'windows-nt)
                                )
			    'allegro
			  (if (search "dppccl" lisp-program)
			      'openmcl
			    (if (search "sbcl" lisp-program)
				'sbcl
				(if (search "gcl" lisp-program)
				    'gcl
				  'sbcl)))))
(defvar *lisp-executable-extension*
  (if *windows-system-p*
      "exe"
    (case *specware-lisp*
      (openmcl "mclexe")
      (cmulisp "cmuexe")
      (sbcl    "sbclexe")
      (allegro "aclexe")
      (gcl     "gclexe"))))

(defvar *lisp-image-extension*
  (case *specware-lisp*
    (openmcl "openmcl-image")
    (cmulisp "cmuimage")
    (sbcl    "sbclimage")
    (allegro "dxl")
    (gcl     "gclimage")))

(defvar *fasl-extension*
  (case *specware-lisp*
    (allegro "fasl")
    (mcl     "dfsl")
    (cmu     "x86f")
    (sbcl    "sfsl")
    (gcl     "o")))

(defvar *macos-p* (= (shell-command "ls /mach_kernel") 0))  ; or any other test that tells us we're on a Mac
(defvar *sbcl-size* (if *windows-system-p* 1200 (if *macos-p* 4000 2400)) "Size of --dynamic-space-size for sbcl")
(defvar *sbcl-stack-size* 4 "Size of --control-stack-size for sbcl") ; Default 2 (megabytes)

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
  (defun set-default-directory (dir)
    (setq default-directory dir))
  (setq *lisp-prompt-regexp* *allegro-prompt-regexp*)
  (defvar *specware-lisp* 'allegro)
  (defvar *lisp-image-extension* "dxl")
  (fset 'sw:exit-lisp 'fi:exit-lisp)
  (defun sw:switch-to-lisp (&optional eob-p)
    (interactive "P")
    (unless fi::toggle-to-lisp-last-lisp-buffer
      (setq fi::toggle-to-lisp-last-lisp-buffer (current-buffer)))
    (fi:toggle-to-lisp)
    (when eob-p
      (goto-char (point-max))))
  ;(fset 'sw:switch-to-lisp 'fi:toggle-to-lisp)
  (fset 'extract-sexp 'fi:extract-list)
  (defun sw:eval-in-lisp (str &rest args)
    (ensure-specware-running)
    (apply 'fi:eval-in-lisp str args))
  (defun sw:eval-in-lisp-no-value (str &rest args)
    (ensure-specware-running)
    (apply 'fi:eval-in-lisp str args)
    t)
  (defun sw:eval-in-lisp-dispatch (str &rest args)
    (ensure-specware-running)
    (apply 'fi:eval-in-lisp-asynchronous str args)
    t)
  (fset 'inferior-lisp-newline 'fi:inferior-lisp-newline)
  (fset 'inferior-lisp-running-p 'fi::lep-open-connection-p)
  (fset 'sw:find-unbalanced-parenthesis 'fi:find-unbalanced-parenthesis)
  (defvar *specware-buffer-name* sw:common-lisp-buffer-name)
  (defun previous-input-line ()
    (fi:pop-input))
  (defun specware-listener-mode-hook ()
    (when sw:use-x-symbol
      (x-symbol-mode 1)))
  (add-hook 'fi:lisp-listener-mode-hook 'specware-listener-mode-hook t)
  (when (and (boundp 'fi:lisp-mode-syntax-table)
	     fi:lisp-mode-syntax-table)
    (modify-syntax-entry ?. "." fi:lisp-mode-syntax-table)))

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
	     (subseq common-lisp-buffer-name
		     1 (- (length common-lisp-buffer-name) 1))
	     (if common-lisp-image-file
		 (case *specware-lisp*
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


(when (eq lisp-emacs-interface-type 'slime)
  (setq slime-*directory*
	(concat (getenv "SPECWARE4") "/Library/IO/Emacs/slime/"))
  (defvar slime-*use-fsf-compliant-keybindings* t) ; Use c-c as command prefix (not c-z)
  (require 'slime)
  (setq inferior-lisp-program lisp-program)
  (setq expand-symlinks-rfs-exists t)
  (defvar slime-multiprocessing
    (case *specware-lisp*
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
		   (case *specware-lisp*
		     ((cmulisp sbcl)
		      (if common-lisp-image-file
			  (list "-core" common-lisp-image-file)
			(list "--dynamic-space-size" (format "%S" *sbcl-size*)
                              "--control-stack-size" (format "%S" *sbcl-stack-size*))))
		     (allegro (concatenate 'list
					   common-lisp-image-arguments
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
    (lisp-or-specware-command ":quit" "quit"))

  (defvar slime-last-buffer nil)

  (defun sw:switch-to-lisp (&optional eob-p)
    (interactive "P")
    (if (equal (buffer-name (current-buffer))
	       sw:common-lisp-buffer-name)
	(slime-pop-to-buffer slime-last-buffer nil)
      (progn (setq slime-last-buffer (current-buffer))
	     (slime-pop-to-buffer sw:common-lisp-buffer-name nil)))
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
  
  (setq slime-find-buffer-package-function 'slime-lisp-package)
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

(defun convert-transforms ()
  (interactive)
 ; (goto-char (point-min))
  (save-excursion (replace-all "trace on," "trace on;"))
  (while (sw:re-search-forward "[ {]at[ (]")
    (unless (in-comment-or-string-p)
      (forward-char -1)
      (when (save-excursion (condition-case nil
                                (progn (up-list -1)
                                       (looking-at "{"))
                              (error nil)))
        ;; convert preceding , to ;
        (save-excursion (forward-sexp -1)
                        (skip-syntax-backward " >")
                        (forward-char -1)
                        (when (looking-at ",")
                          (delete-char 1)
                          (insert ";")))
        (forward-sexp 1)
        (sw:re-search-forward ",")
        (delete-backward-char 1)        ; delete , after at qids
        (insert " ")
        ;; Convert body of at
        (skip-syntax-forward " >")      ; (char-syntax ?\n)
        (insert " {")
        (while (condition-case nil
                   (progn (skip-syntax-forward " >")
                          (if (or (looking-at "at[ (]")
                                  (looking-at "finalizeCoType[ (]"))
                              nil
                            (progn (forward-sexp 1) t)))
                 (error nil))
          (skip-syntax-forward " >")
          (when (looking-at ",")
            (delete-char 1)
            (insert ";")))
        (skip-syntax-backward " >")
        (forward-char -1)
        (unless (looking-at ";")        ; before a new at
          (forward-char 1))
        (insert "}")
        (save-excursion (forward-sexp -1)
                        (sw:indent-line)
                        (sw:indent-sexp 1)
                        ;; Remove {}s if only only one symbol
                        (forward-char 1)
                        (forward-sexp 1)
                        (when (looking-at "}")
                          (insert-braces -1)))))))

