(defpackage :NAT-SPEC)
(IN-PACKAGE :NAT-SPEC)

(defun |!+| (x y)
  (+ x y))
(defun |!+-1| (x)
  (+ (car x) (cdr x)))

(defun |!*| (x y)
  (* x y))
(defun |!*-1| (x)
  (* (car x) (cdr x)))

(defun |!-| (x y)
  (- x y))
(defun |!--1| (x)
  (- (car x) (cdr x)))

(defun toString (x)
  (princ-to-string x))

(defun natToString (x)
  (princ-to-string x))

;; Is this ugly or what?

;(defun stringToNat (s)
;  (multiple-value-bind
;      (n ignore) (read-from-string s)
;    n))

(defun stringToNat (s)
  ;; lisp automatically returns the first value as a normal value
  (read-from-string s))

(defun |!<| (x y)
  (< x y))
(defun |!<-1| (x)
  (< (car x) (cdr x)))

(defun |!>| (x y) 
  (> x y))
(defun |!>|-1 (x) (|!>| (car x) (cdr x)))

(defun |!<=| (x y)
  (<= x y))
(defun |!<=-1| (x)
  (<= (car x) (cdr x)))

(defun |!>=| (x y)
  (>= x y))
(defun |!>=|-1 (x) (|!>=| (car x) (cdr x)))


(defun succ (x)
  (+ 1 x))
(defun pred (x)
  (- x 1))

(defun |!rem| (x y)
  (rem x y))
(defun |!rem-1| (x)
  (rem (car x) (cdr x)))

(defun div (x y)
  ;; (floor (/ x y))
  (truncate x y))
(defun div-1 (x)
  (truncate (car x) (cdr x)))


;; This is not correct for negative values???... FIXME...
;; Is truncate what you want here?  E.g.,  (truncate -7 3) => -2

(defun compare (i1 i2) 
    (if (< i1 i2)
	'(:|Less|)
	(if (= i1 i2)
	'(:|Equal|)
	'(:|Greater|))))
(defun compare-1 (x) (compare (car x) (cdr x)))

(defun |!min| (n1 n2)
  (min n1 n2))
(defun |!min|-1 (x) (|!min| (car x) (cdr x)))

(defun |!max| (n1 n2)
  (max n1 n2))
(defun |!max|-1 (x) (|!max| (car x) (cdr x)))

(defun fromNat (x)
  x
)

(defun INTEGER-SPEC::fromNat (x)
  x
)
