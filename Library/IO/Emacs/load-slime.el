
;; Load everything and use slime interface to lisp instead of Franz's

(defvar lisp-emacs-interface-type 'slime)

(defconst *specware* (getenv "SPECWARE4"))
(defconst *specware-home-directory* *specware*)

(defconst *specware-emacs* (concat *specware* "/Library/IO/Emacs/"))

(defvar *windows-system-p* (memq system-type '(ms-dos windows-nt windows-95
					       ms-windows)))

(load (concat *specware-emacs* "augment-load-path.el"))

(push (concat *specware-emacs* "slime/")
      load-path)

(push (concat *specware-emacs* "x-symbol/")
      load-path)
;(push "/usr/local/ProofGeneral/x-symbol/lisp/"
;      load-path)
;(setq x-symbol-data-directory "/usr/local/ProofGeneral/x-symbol/etc/")

;; for compatibility with xemacs and gnu emacs
(unless (featurep 'xemacs)
  (require 'byte-opt)
  (remprop 'featurep 'byte-optimizer))

(defun sw:load-specware-emacs-file (name)
  (let ((el-file   (concatenate 'string *specware-emacs* name ".el"))
	(elc-file  (concatenate 'string *specware-emacs* name ".elc")))
    (unless (and (file-exists-p elc-file)
		 (file-newer-than-file-p elc-file el-file))
      (byte-compile-file el-file))
    (load elc-file)))

(custom-set-variables '(slime-repl-enable-presentations nil))

;;; prep for loading slime.el...
(eval-and-compile
  (require 'cl)
  (unless (fboundp 'define-minor-mode)
    (require 'easy-mmode)
    (unless (fboundp 'define-minor-mode)
      ;; Do this only if easy-mmode hasn't already done it...
      (defalias 'define-minor-mode 'easy-mmode-define-minor-mode)
      )))
(require 'advice)  ; for defadvice
(require 'edmacro) ; for read-kbd-macro (i.e., backqoute)

(require 'slime)

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
  (simulate-input-expression "(emacs::kill-emacs-and-then-lisp)"))
