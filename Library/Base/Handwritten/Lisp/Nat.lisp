(defpackage :NAT-SPEC)
(IN-PACKAGE :NAT-SPEC)

;;; Added various declarations to quiet down cmucl.

;;; The functions commented out acquire definitions from the compilation of Specware4.sw
;;;  before they are used.

;;; (defun |!+| (x y)
;;;   (+ x y))
;;; (defun |!+-1| (x)
;;;   (+ (car x) (cdr x)))
;;; 
;;; (defun |!*| (x y)
;;;   (* x y))
;;; (defun |!*-1| (x)
;;;   (* (car x) (cdr x)))
;;; 
;;; (defun |!-| (x y)
;;;   (- x y))
;;; (defun |!--1| (x)
;;;   (- (car x) (cdr x)))

(defun toString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun natToString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun stringToNat (s)
  (declare (type string s))
  ;; lisp automatically returns the first value as a normal value
  (the integer (read-from-string s)))

;;; (defun |!<| (x y)
;;;   (< x y))
;;; (defun |!<-1| (x)
;;;   (< (car x) (cdr x)))
;;; 
;;; (defun |!>| (x y) 
;;;   (> x y))
;;; (defun |!>|-1 (x) (|!>| (car x) (cdr x)))
;;; 
;;; (defun |!<=| (x y)
;;;   (<= x y))
;;; (defun |!<=-1| (x)
;;;   (<= (car x) (cdr x)))
;;; 
;;; (defun |!>=| (x y)
;;;   (>= x y))
;;; (defun |!>=|-1 (x) (|!>=| (car x) (cdr x)))
;;; 
;;; 
;;; (defun succ (x)
;;;   (+ 1 x))
;;; (defun pred (x)
;;;   (- x 1))

(defun rem-2 (x y)
  (declare (integer x y))
  (the integer (cl:rem x y)))

(define-compiler-macro rem-2 (x y)
  `(cl:rem ,(integer-spec::the-int x) ,(integer-spec::the-int y)))

(defun |!rem| (x)
  (rem (car x) (cdr x)))
 

(defun div-2 (x y)
  (declare (integer x y))
  (the integer (cl:truncate x y)))

(define-compiler-macro div-2 (x y)
  `(cl:truncate ,(integer-spec::the-int x) ,(integer-spec::the-int y)))

(defun div (x)
  (cl:truncate (car x) (cdr x)))
;;; 
;;; 
;;; ;; This is not correct for negative values???... FIXME...
;;; ;; Is truncate what you want here?  E.g.,  (truncate -7 3) => -2
;;; 
;;; (defun compare (i1 i2) 
;;;     (if (< i1 i2)
;;; 	'(:|Less|)
;;; 	(if (= i1 i2)
;;; 	'(:|Equal|)
;;; 	'(:|Greater|))))
;;; (defun compare-1 (x) (compare (car x) (cdr x)))
;;; 
;;; (defun |!min| (n1 n2)
;;;   (min n1 n2))
;;; (defun |!min|-1 (x) (|!min| (car x) (cdr x)))
;;; 
;;; (defun |!max| (n1 n2)
;;;   (max n1 n2))
;;; (defun |!max|-1 (x) (|!max| (car x) (cdr x)))
;;; 
;;; (defun fromNat (x) x)
;;; 
;;; (defun INTEGER-SPEC::fromNat (x) x)
;;; 
;;; (defun toNat (x)
;;;    (if (< x 0)
;;;       (error "Nat.toNat: argument < 0")
;;;       x))
;;; 