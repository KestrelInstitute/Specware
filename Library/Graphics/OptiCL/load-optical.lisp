;;; Specware interface to opticl

(defpackage :OptiCL (:use :Common-Lisp))
(in-package :CL-USER)

(defun loadOptiCL () 
  (load "../quicklisp/setup")  
  (funcall (find-symbol "QUICKLOAD" "QL") 'opticl)
  (load "sw-opticl"))

(loadOptiCL)

