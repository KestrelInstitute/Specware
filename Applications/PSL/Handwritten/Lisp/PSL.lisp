#+Lispworks
(setq *default-package-use-list* '("CL"))

(defpackage "SPECWARE")
(in-package "SPECWARE")

(defpackage "EMACS")   ;; needed by the parser
(defpackage "METASLANG")   ;; needed by the parser

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

;; This defines the RE package .. this will go away when the bootstrap
;; is complete.
;(compile-and-load-lisp-file "re-legacy")

;;; (sw) ;; The following list should be generated automatically!
;;; (sw) ;; The list is used only in this file.
;;; (sw) ;;; ---------------
;;; (sw) (defvar HandwrittenFiles
;;; (sw)   '(
;;; (sw)     "Library/Base/Handwritten/Lisp/Boolean.lisp"
;;; (sw)     "Library/Base/Handwritten/Lisp/Integer.lisp"
;;; (sw)     "Library/Base/Handwritten/Lisp/Nat.lisp"
;;; (sw)     "Library/Base/Handwritten/Lisp/Char.lisp"
;;; (sw)     "Library/Base/Handwritten/Lisp/List.lisp"
;;; (sw)     "Library/Base/Handwritten/Lisp/String.lisp"
;;; (sw)     "Library/Base/Handwritten/Lisp/Option.lisp"
;;; (sw)     "Library/Base/Handwritten/Lisp/System.lisp"
;;; (sw)     "Library/IO/Primitive/Handwritten/Lisp/IO.lisp"
;;; (sw)     "Library/Legacy/Utilities/Handwritten/Lisp/State.lisp"
;;; (sw)     "Library/Legacy/Utilities/Handwritten/Lisp/IO.lisp"
;;; (sw)     "Library/Legacy/Utilities/Handwritten/Lisp/Lisp.lisp"
;;; (sw)     "Library/Legacy/DataStructures/Handwritten/Lisp/HashTable.lisp"
;;; (sw)   )
;;; (sw) )

(defvar Specware4 (sys:getenv "SPECWARE4"))

;;; (sw) (compile-and-load-lisp-file "runtime")
;;; (sw) 
;;; (sw) (map 'list #'(lambda (file)
;;; (sw)   (compile-and-load-lisp-file (concatenate 'string Specware4 "/" file)))
;;; (sw)   HandwrittenFiles
;;; (sw) )
;;; (sw) 
;;; (sw) ;; Define functions for saving/restoring the
;;; (sw) ;; Specware state to/from the lisp environment
;;; (sw) (compile-and-load-lisp-file "specware-state")
;;; (sw) 
;;; (sw) ;; Now load the generated lisp code.  This also initializes the Specware
;;; (sw) ;; state in the lisp environment. See SpecCalculus/Semantics/Specware.sw.
;;; (sw) (compile-and-load-lisp-file "../../lisp/Specware4.lisp")
;;; (sw) 
;;; (sw) ;; Stephen's toplevel aliases 
;;; (sw) (compile-and-load-lisp-file "toplevel")
;;; (sw) 
;;; (sw) ;; Debugging utilities
;;; (sw) (compile-and-load-lisp-file "debug")

(defun METASLANG::mkQualifiedId (qualifier id) 
  (cons :|Qualified| (cons qualifier id)))

(defun METASLANG::mkUnQualifiedId (id) 
  (cons :|Qualified| (cons METASLANG::UnQualified id)))

(defparameter METASLANG::UnQualified "<unqualified>")

(make-system (concatenate 'string
    Specware4 "/../Specware4/Library/Algorithms/Parsing/Chart/Handwritten/Lisp"))
(make-system (concatenate 'string
    Specware4 "/../Specware4/Languages/PSL/Parser/Handwritten/Lisp"))

;;; (sw) (make-system "../../UI/Emacs/Handwritten/Lisp")
;;; (sw) 
;;; (sw) (format t "~2%To bootstrap, run (boot)~%")
;;; (sw) (format t "~%That will run :sw /Applications/Specware/Specware4~2%")
;;; (sw) 
;;; (sw) (defun user::boot ()
;;; (sw)   (user::sw "/Applications/Specware/Specware4")
;;; (sw) )
