(defpackage :BOOLEAN-SPEC)
(IN-PACKAGE :BOOLEAN-SPEC)

(defun ~(x) (not x))
(defun <=>-2  (x y) (eq x y))
(defun <=>  (pr) (eq (car pr) (cdr pr)))
;;; Binary versions of following are handled directly by the code generator
(defun & (pr) (and (car pr) (cdr pr)))
(defun |!or|  (pr) (or (car pr) (cdr pr)))
(defun =>  (pr) (or (not (car pr)) (cdr pr)))
