;;; Specware interface to opticl

(in-package :CL-USER)

(defun loadOptiCL-0 () 
  (let ((specware4 (SPECWARE::GETENV "SPECWARE4")))
    (load (concatenate 'string specware4 "/Library/QuickLisp/setup.lisp")))
  (funcall (find-symbol "QUICKLOAD" "QL") 'opticl)
  ;; (load (compile-file "OptiCL/sw-opticl"))
  (load (compile-file "Handwritten/Lisp/matrix.lisp"))
  (load (compile-file "Handwritten/Lisp/image.lisp"))
  )

;; (loadOptiCL-0)
