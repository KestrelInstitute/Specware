
;; This is here because the parser expects thing from the RE package
;; When the parser migrates to the Specware4 tree there can be
;; a rationalization of package names and this file can go away.

(defpackage "RE")

(defun re::load-lisp-file (file &rest ignore)
  (load (make-pathname :defaults file :type "lisp")))

(defun re::compile-and-load-lisp-file (file)
   (#+allegro excl::compile-file-if-needed
    #+Lispworks hcl:compile-file-if-needed
    (make-pathname :defaults file :type "lisp"))
   (load (make-pathname :defaults file :type nil)))
