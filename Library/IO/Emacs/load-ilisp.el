
;; Load everything and use ilisp interface to lisp instead of Franz's

(defvar lisp-emacs-interface-type 'ilisp)

(defconst *specware* (getenv "SPECWARE4"))
(defconst *specware-home-directory* (getenv "SPECWARE4"))

(defconst *specware-emacs* (concat *specware* "/Library/IO/Emacs/"))

(push (concat *specware-emacs* "ilisp-20020831/")
      load-path)

(require 'ilisp)

(defun sw:load-specware-emacs-file (name)
  (load (concatenate 'string *specware-emacs* name)))

;; This defvar just eliminates a compilation warning message.
(defvar sw:specware-emacs-files) ; see defconst in files.el

(sw:load-specware-emacs-file "files")

(mapc 'sw:load-specware-emacs-file sw:specware-emacs-files)

(setq auto-mode-alist
  (list* '("\\.sl$" . specware-mode)
	 '("\\.spec$" . specware-mode)
	 '("\\.sw$" . specware-mode)
	 auto-mode-alist))
