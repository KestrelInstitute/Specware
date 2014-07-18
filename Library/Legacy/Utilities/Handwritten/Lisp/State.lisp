(defpackage :State)
(in-package :State)

(defun ref (x) 
  (cons :|Ref| x))

(defun mkRef (x) 
  (cons :|Ref| x))

(defun |:=-2| (x y)
  (rplacd x y))

;; (define-compiler-macro  |:=-2| (x y)
;;   `(rplacd ,x ,y))

(defun |!!| (x) (cdr x))
