
(defpackage :STATE)
(IN-PACKAGE :STATE)

(defun ref (x) 
  (cons :|ref| x))

(defun |:=| (x y)
  (rplacd x y))

(defun |!!| (x) (cdr x))
