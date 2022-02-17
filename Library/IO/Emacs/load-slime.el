
;; Load everything and use slime interface to lisp instead of Franz's

(defvar lisp-emacs-interface-type 'slime)

(defconst *specware* (or (getenv "SPECWARE4") (concat (getenv "HOME") "/Specware")))
(defconst *specware-home-directory* *specware*)

(defvar cygwin?
  (let ((test1 (eq system-type 'cygwin32))
        (test2 (string= "/cygdrive/" (substring *specware* 0 10))))
    ;; following messages commented out by default...
    '(cond ((and test1 (not test2))
            ;; We normally come through this case,
            ;;  since setting *specware* to "/cygdrive/c/specware" seems to cause problems elsewhere. (sigh)
            (message "Will assume cygwin32 environment, since system-type is 'cgywin32, but ...")
            (sit-for 2)
            (message "*specware* doesn't start with \"/cygdrive/\": %s" *specware*)
            (sit-for 2))
           ((and test2 (not test1))
            (message "Will assume cygwin32 environment, since *specware* starts with \"/cygdrive/\": %s, but ..."
                     *specware*)
            (sit-for 2)
            (message "system-type is not 'cgywin: %s" system-type)))
    (or test1 test2)))

(when cygwin?
  (setq system-type 'windows-nt))

(defconst *specware-emacs* (concat *specware* "/Library/IO/Emacs/"))

(defvar *windows-system-p* (memq system-type '(ms-dos windows-nt windows-95
					       ms-windows)))

;(loop for x in '(mule mule-autoloads mule-base-autoloads) do (setq features (remove x features)))

(push *specware-emacs* load-path)

(push (concat *specware-emacs* "slime/")
      load-path)
(require 'slime-autoloads)

(push (concat *specware-emacs* "haskell-mode/")
      load-path)

;; (unless (fboundp 'haskell-mode)
;;  (load (concat *specware-emacs* "haskell-mode/haskell-site-file")))

;; Need in XEmacs version 21.5 for x-symbol
(when (and (featurep 'mule) (fboundp 'define-specifier-tag))
  (define-specifier-tag 'mule-fonts))

(push (concat *specware-emacs* "x-symbol/")
      load-path)
;(push "/usr/local/ProofGeneral/x-symbol/lisp/"
;      load-path)
;(setq x-symbol-data-directory "/usr/local/ProofGeneral/x-symbol/etc/")

(defun sw:load-specware-emacs-file (name)
  (let ((el-file   (concat *specware-emacs* name ".el"))
	(elc-file  (concat *specware-emacs* name ".elc")))
    (unless (and (file-exists-p elc-file)
		 (file-newer-than-file-p elc-file el-file))
      (byte-compile-file el-file))
    (load elc-file)))

(custom-set-variables ;'(slime-repl-enable-presentations t)
                      '(indent-tabs-mode nil))

;;; prep for loading slime.el...
(eval-and-compile
  (if (require 'cl-lib nil 'noerror)
      ()
    (require 'cl))
  (unless (fboundp 'define-minor-mode)
    (require 'easy-mmode)
    (unless (fboundp 'define-minor-mode)
      ;; Do this only if easy-mmode hasn't already done it...
      (defalias 'define-minor-mode 'easy-mmode-define-minor-mode)
      )))
(require 'advice)  ; for defadvice
(require 'edmacro) ; for read-kbd-macro (i.e., backqoute)
(require 'regexp-opt) ; for regexp-opt

(setq slime-contribs '(slime-repl slime-fuzzy ; slime-presentations
                                  bridge))

(require 'slime)
;; something about recursive (eval-when (comile) ...) causes error "reading from killed buffer"
;; so moved following out from under eval-when compile in slime --
;(require 'compile)

(let* ((libfile (locate-library "slime")))
  ;; Is it byte-compiled?
  (when (or (not (eq (elt (locate-library "slime")
			  (- (length (locate-library "slime")) 1))
		     ?c))
	    (slime-bytecode-stale-p))
  (slime-recompile-bytecode)
  (load-library "slime")))


(slime-setup)

;; This defvar just eliminates a compilation warning message.
(defvar sw:specware-emacs-files) ; see defconst in files.el

(sw:load-specware-emacs-file "files")

(mapc 'sw:load-specware-emacs-file sw:specware-emacs-files)

(sw:load-specware-emacs-file "sw-slime")

(setq auto-mode-alist
  (list* ;'("\\.sl$" . specware-mode)
	 ;'("\\.spec$" . specware-mode)
	 '("\\.sw$" . specware-mode)
	 auto-mode-alist))


(defvar *load-mode-motion+* (featurep 'xemacs))

(when *load-mode-motion+*
  (defvar mode-motion+-religion 'highlight)
  (require 'mode-motion+)
  (defun mode-motion+-highlight (event)
    "Highlight the thing under the mouse using a mode-specific motion handler.
See list-motion-handlers for more details."
    (mode-motion-clear-last-extent)
    (and (event-buffer event)
	 ;; sjw: added save-window-excursion
	 (save-window-excursion
	   (cond ((and mouse-grabbed-buffer
		       ;; first try to do minibuffer specific highlighting
		       (find-motion-handler 'minibuffer)
		       (let ((mode-motion-highlight-lines-when-behind nil))
			 (and (event-point event)
			      (or (extent-at (event-point event)
					     (event-buffer event) 'highlight)
				  (mode-motion-highlight-with-handler
				   (find-motion-handler 'minibuffer) event))))))
		 (t (mode-motion-highlight-with-handler
		     (get-current-motion-handler) event)))))
    ;; Return nil since now this is used as a hook, and we want to let
    ;; any other hook run after us.
    nil)
  (byte-compile 'mode-motion+-highlight)
  (set-mode-motion-handler 'dired-mode 'highlight-vline)
  (global-set-key '(control shift button2) 'mode-motion-copy))

;; a hack to simplify writing scripts (e.g. for testing)
;; that run lisp under emacs and then exit
(defun sw:kill-emacs-and-then-lisp ()
  (simulate-input-expression "(Emacs::kill-emacs-and-then-lisp)"))
