
;; Compile everything

(defconst *specware* (getenv "SPECWARE4"))
(defconst *specware-home-directory* (getenv "SPECWARE4"))

(defconst *specware-emacs* (concatenate 'string *specware* "/Library/IO/Emacs/"))

;; Can't seem to find this in Emacs Lisp!

(defun sw:foreach (f l)
  (while (not (null l))
    (funcall f (car l))
    (setq l (cdr l))))

(defun sw:load-specware-emacs-file (name)
  (load (concatenate 'string *specware-emacs* name)))

(defun sw:compile-specware-emacs-file (name)
  (byte-compile-file (concatenate 'string *specware-emacs* name ".el")))

(defun sw:compile-and-load-specware-emacs-file (name)
  (sw:compile-specware-emacs-file name)
  (sw:load-specware-emacs-file name))

(sw:load-specware-emacs-file "files")

(sw:foreach 'sw:compile-and-load-specware-emacs-file sw:specware-emacs-files)

