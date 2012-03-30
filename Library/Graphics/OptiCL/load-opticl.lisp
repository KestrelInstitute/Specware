;;; Specware interface to opticl

(in-package :CL-USER)

(defun loadOptiCL-0 () 
  (load "/home/sfitzp/specware/Library/Graphics/OptiCL/QuickLisp/setup.lisp")  
  (funcall (find-symbol "QUICKLOAD" "QL") 'opticl)
  (load "OptiCL/sw-opticl"))

;; (loadOptiCL-0)

