
(defpackage :BOOLEAN-SPEC)
(IN-PACKAGE :BOOLEAN-SPEC)

(defun toString (x)
  (format nil (if x "true" "false")))

(defun & (x y)
  (and x y))
(defun &-1 (x) (& (car x) (cdr x)))

(defun ~ (x)
  (not x))

(defun <=> (a b)
  (or (and a b)
      (and (not a) (not b))))
(defun <=>-1 (x) (<=> (car x) (cdr x)))

(defun => (x y)
  (or (not x) y))
(defun =>-1 (x) (=> (car x) (cdr x)))

(defun |!or| (x y)
  (lisp::or x y))
(defun |!or|-1 (x) (|!or| (car x) (cdr x)))

(defun compare (s1 s2) 
  (if s1
      (if s2 '(:|Equal|) '(:|Greater|))
    (if s2 '(:|Less|) '(:|Equal|))))
(defun compare-1 (x) (compare (car x) (cdr x)))
