
;; Load everything and use ilisp interface to lisp instead of Franz's

(defvar lisp-emacs-interface-type 'ilisp)

(defconst *specware* (getenv "SPECWARE4"))
(defconst *specware-home-directory* (getenv "SPECWARE4"))

(defconst *specware-emacs* (concat *specware* "/Library/IO/Emacs/"))

(push (concat *specware-emacs* "ilisp/")
      load-path)

(defvar ilisp-*use-fsf-compliant-keybindings* t)
;(defvar ilisp-*use-frame-for-output* nil)
(require 'ilisp)

(defun sw:load-specware-emacs-file (name)
  (let ((el-file   (concatenate 'string *specware-emacs* name ".el"))
	(elc-file  (concatenate 'string *specware-emacs* name ".elc")))
    (unless (and (file-exists-p elc-file)
		 (file-newer-than-file-p elc-file el-file))
      (byte-compile-file el-file))
    (load elc-file)))

;; This defvar just eliminates a compilation warning message.
(defvar sw:specware-emacs-files) ; see defconst in files.el

(sw:load-specware-emacs-file "files")

(mapc 'sw:load-specware-emacs-file sw:specware-emacs-files)

(setq auto-mode-alist
  (list* '("\\.sl$" . specware-mode)
	 '("\\.spec$" . specware-mode)
	 '("\\.sw$" . specware-mode)
	 auto-mode-alist))
