
(defpackage :State)
(in-package :State)

(defun ref (x) 
  (cons :|ref| x))

(defun |:=-2| (x y)
  (rplacd x y))

(defun |!!| (x) (cdr x))
