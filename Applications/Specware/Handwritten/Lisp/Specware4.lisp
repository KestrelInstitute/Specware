#+Lispworks
(setq *default-package-use-list* '("CL"))

(defpackage "SPECWARE")
(in-package "SPECWARE")

(terpri) ; purely cosmetic

#+allegro(setq excl:*global-gc-behavior* '(10 10.0))

;;; ---------------
;; The following collection have been adapted from the 2000 load.lisp
;; file. Perhaps they should be factored into a separate file as they
;; are likely to be used for many of the generated lisp applications?

(defun current-directory ()
  #+allegro(excl::current-directory)
  #+Lispworks(hcl:get-working-directory)  ;(current-pathname)
  )

(defun change-directory (directory)
  ;; (lisp::format t "Changing to: ~A~%" directory)
  #+allegro(excl::chdir directory)
  #+Lispworks (hcl:change-directory directory)
  (setq lisp::*default-pathname-defaults* (current-directory)))

#+Lispworks
(defun make-system (new-directory)
  (let ((*default-pathname-defaults*
     (make-pathname :name (concatenate 'string new-directory "/")
            :defaults
            system::*current-working-pathname*))
    (old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

#-Lispworks
(defun make-system (new-directory)
  (let ((old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

(defun compile-and-load-lisp-file (file)
   (#+allegro excl::compile-file-if-needed
    #+Lispworks hcl:compile-file-if-needed
    (make-pathname :defaults file :type "lisp"))
   (load (make-pathname :defaults file :type nil)))

(defun load-lisp-file (file &rest ignore)
  (load (make-pathname :defaults file :type "lisp")))

;; This defines the RE package .. this will go away when the bootstrap
;; is complete.
;(compile-and-load-lisp-file "re-legacy")

;; The following list should be generated automatically!
;; The list is used only in this file.
;;; ---------------
(defvar HandwrittenFiles
  '(
    "Library/Base/Handwritten/Lisp/Boolean.lisp"
    "Library/Base/Handwritten/Lisp/Integer.lisp"
    "Library/Base/Handwritten/Lisp/Nat.lisp"
    "Library/Base/Handwritten/Lisp/Char.lisp"
    "Library/Base/Handwritten/Lisp/List.lisp"
    "Library/Base/Handwritten/Lisp/String.lisp"
    "Library/Base/Handwritten/Lisp/Option.lisp"
    "Library/Base/Handwritten/Lisp/System.lisp"
    "Library/IO/Primitive/Handwritten/Lisp/IO.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/State.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/IO.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/Lisp.lisp"
    "Library/Legacy/DataStructures/Handwritten/Lisp/HashTable.lisp"
  )
)

(defvar Specware4 (sys:getenv "SPECWARE4"))

(compile-and-load-lisp-file "runtime")

(map 'list #'(lambda (file)
  (compile-and-load-lisp-file (concatenate 'string Specware4 "/" file)))
  HandwrittenFiles
)

;; Define functions for saving/restoring the
;; Specware state to/from the lisp environment
(compile-and-load-lisp-file "specware-state")

;; Now load the generated lisp code.  This also initializes the Specware
;; state in the lisp environment. See SpecCalculus/Semantics/Specware.sw.
(compile-and-load-lisp-file "../../lisp/Specware4.lisp")

;; Stephen's toplevel aliases 
(compile-and-load-lisp-file "toplevel")

;; Debugging utilities
(compile-and-load-lisp-file "debug")

(make-system (concatenate 'string
    Specware4 "/../Specware4/Library/Algorithms/Parsing/Chart/Handwritten/Lisp"))
(make-system (concatenate 'string
    Specware4 "/../Specware4/Languages/SpecCalculus/Parser/Handwritten/Lisp"))

(make-system "../../UI/Emacs/Handwritten/Lisp")

(format t "~2%To bootstrap, run (boot)~%")
(format t "~%That will run :sw /Applications/Specware/Specware4~2%")

(defun user::boot ()
  (user::sw "/Applications/Specware/Specware4")
)
