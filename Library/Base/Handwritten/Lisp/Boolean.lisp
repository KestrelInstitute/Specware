
(defpackage :BOOLEAN-SPEC)
(IN-PACKAGE :BOOLEAN-SPEC)


;;; The functions commented out acquire definitions from the compilation of Specware4.sw
;;;  before they are used.

(defun toString (x)
  (if x "true" "false"))

(define-compiler-macro ~ (x)
  `(not ,x))

;;;  (defun & (x y)
;;;    (and x y))
;;;  (defun &-1 (x) (& (car x) (cdr x)))
;;;  
;;;  (defun ~ (x)
;;;    (not x))
;;;  
;;;  (defun <=> (a b)
;;;    (or (and a b)
;;;        (and (not a) (not b))))
;;;  (defun <=>-1 (x) (<=> (car x) (cdr x)))
;;;  
;;;  (defun => (x y)
;;;    (or (not x) y))
;;;  (defun =>-1 (x) (=> (car x) (cdr x)))
;;;  
;;;  (defun |!or| (x y)
;;;    (lisp::or x y))
;;;  (defun |!or|-1 (x) (|!or| (car x) (cdr x)))
;;;  
;;;  (defun compare (s1 s2) 
;;;    (if s1
;;;        (if s2 '(:|Equal|) '(:|Greater|))
;;;      (if s2 '(:|Less|) '(:|Equal|))))
;;;  (defun compare-1 (x) (compare (car x) (cdr x)))
