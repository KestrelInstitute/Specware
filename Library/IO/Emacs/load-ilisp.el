
;; Load everything and use ilisp interface to lisp instead of Franz's

(defvar lisp-emacs-interface-type 'ilisp)

(defconst *specware* (getenv "SPECWARE4"))
(defconst *specware-home-directory* (getenv "SPECWARE4"))

(defconst *specware-emacs* (concatenate 'string *specware* "/Library/IO/Emacs/"))

;; This sets the emacs to lisp interface to be the one supplied by franz
;; The alternative supported is ilisp which is enabled by setting this
;; variable to 'ilisp
(defvar lisp-emacs-interface-type 'franz)

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
