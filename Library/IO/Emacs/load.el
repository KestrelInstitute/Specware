
;; Load everything

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

(defvar *load-mode-motion+* t)

(when *load-mode-motion+*
  (defvar mode-motion+-religion 'highlight)
  (require 'mode-motion+)
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