
;; Load everything

(defconst *specware* (getenv "SPECWARE2000"))
(defconst *specware-home-directory* (getenv "SPECWARE2000"))

(defconst *specware-emacs* (concatenate 'string *specware* "/emacs/"))

;; This sets the emacs to lisp interface to be the one supplied by franz
;; The alternative supported is ilisp which is enabled by setting this
;; variable to 'ilisp
(defvar lisp-emacs-interface-type 'franz)

;; Can't seem to find this in Emacs Lisp!
;;   That's because it's called mapc.
;;   Deprecate this definition...
(defun sw:foreach (f l)
  (while (not (null l))
    (funcall f (car l))
    (setq l (cdr l))))

(defun sw:load-specware-emacs-file (name)
  (load (concatenate 'string *specware-emacs* name)))

;; This defvar just eliminates a compilation warning message.
(defvar sw:specware-emacs-files) ; see defconst in files.el

(sw:load-specware-emacs-file "files")

(mapc 'sw:load-specware-emacs-file sw:specware-emacs-files)

(setq auto-mode-alist
  (list* '("\\.sl$" . slang-mode)
	 '("\\.spec$" . slang-mode)
	 '("\\.sw$" . slang-mode)
	 auto-mode-alist))
