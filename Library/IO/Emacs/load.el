;(require 'cl)

;; Load everything
(cl-pushnew (concat (getenv "SPECWARE4") "/Library/IO/Emacs/x-symbol/") load-path)

(defconst *specware* (getenv "SPECWARE4"))
(defconst *specware-home-directory* (getenv "SPECWARE4"))

(defconst *specware-emacs* (concat *specware* "/Library/IO/Emacs/"))

(defvar *windows-system-p* (memq system-type '(ms-dos windows-nt windows-95
					       ms-windows)))

(defvar cygwin? (string= "/cygdrive/" (subseq *specware* 0 10)))

;; This sets the emacs to lisp interface to be the one supplied by franz
;; The alternative supported is ilisp which is enabled by setting this
;; variable to 'ilisp
(defvar lisp-emacs-interface-type 'franz)

(defun sw:load-specware-emacs-file (name)
  (let ((el-file   (concat *specware-emacs* name ".el"))
	(elc-file  (concat *specware-emacs* name ".elc")))
    (unless (and (file-exists-p elc-file)
		 (file-newer-than-file-p elc-file el-file))
      (byte-compile-file el-file))
    (load elc-file)))

;; This defvar just eliminates a compilation warning message.
(defvar sw:specware-emacs-files) ; see defconst in files.el

;(defvar sw:common-lisp-buffer-name     nil)
(defvar sw:common-lisp-directory       nil)
(defvar sw:common-lisp-image-name      nil)
(defvar sw:common-lisp-image-arguments nil)
(defvar sw:common-lisp-host            nil)
(defvar sw:common-lisp-image-file      nil)
(defvar sw::lisp-host                  nil)
(defvar comint-status                  nil)

(sw:load-specware-emacs-file "files")

(mapc 'sw:load-specware-emacs-file sw:specware-emacs-files)

(setq auto-mode-alist
  (list* '("\\.sl$" . specware-mode)
	 '("\\.spec$" . specware-mode)
	 '("\\.sw$" . specware-mode)
	 auto-mode-alist))

(defvar *load-mode-motion+* t)

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

(autoload 'grep "igrep"
   "*Run `grep` PROGRAM to match EXPRESSION in FILES..." t)
(autoload 'egrep "igrep"
   "*Run `egrep`..." t)
(autoload 'fgrep "igrep"
   "*Run `fgrep`..." t)
(autoload 'agrep "igrep"
   "*Run `agrep`..." t)
(autoload 'grep-find "igrep"
   "*Run `grep` via `find`..." t)
(autoload 'egrep-find "igrep"
   "*Run `egrep` via `find`..." t)
(autoload 'fgrep-find "igrep"
   "*Run `fgrep` via `find`..." t)
(autoload 'agrep-find "igrep"
   "*Run `agrep` via `find`..." t)
