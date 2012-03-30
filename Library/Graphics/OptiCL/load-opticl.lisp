;;; Specware interface to opticl

(defpackage :OptiCL (:use :Common-Lisp))
(in-package :CL-USER)

(defun loadOptiCL-0 () 
  (load "../QuickLisp/setup.lisp")  
  (funcall (find-symbol "QUICKLOAD" "QL") 'opticl)
  (load "OptiCL/sw-opticl"))

;; (loadOptiCL-0)

