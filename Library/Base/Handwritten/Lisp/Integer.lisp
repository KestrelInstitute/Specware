(defpackage :INTEGER-SPEC)
(IN-PACKAGE :INTEGER-SPEC)

;;; The functions commented out acquire definitions from the compilation of Specware4.sw
;;;  before they are used.

;;; Added various declarations to quiet down cmucl.

(defparameter specware::*use-fixnum-arithmetic?* nil)

(defun the-int (n)
  (if specware::*use-fixnum-arithmetic?*
      `(the fixnum ,n)
    `(the integer ,n)))

(defun +-2 (x y)
  (declare (integer x y))
  (the integer (+ x y)))

(define-compiler-macro +-2 (x y)
  `(+ ,(the-int x) ,(the-int y)))

(defun |!+| (x)
   (+ (car x) (cdr x)))

(defun *-2 (x y)
  (declare (integer x y))
  (the integer (* x y)))

(define-compiler-macro *-2 (x y)
  `(* ,(the-int x) ,(the-int y)))

(defun |!*| (x)
   (* (car x) (cdr x)))

(defun --2 (x y)
  (declare (integer x y))
  (the integer (- x y)))

(define-compiler-macro --2 (x y)
  `(- ,(the-int x) ,(the-int y)))

(defun |!-| (x)
   (- (car x)(cdr x)))

(defun toString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun intToString (x)
   (princ-to-string x))

(defun stringToInt (s)
  ;; lisp automatically returns the first value as a normal value
  (read-from-string s))

(defun <-2 (x y)
  (declare (integer x y))
  (the boolean (< x y)))

(define-compiler-macro <-2 (x y)
  `(< ,(the-int x) ,(the-int y)))

(defun |!<| (x)
  (< (car x) (cdr x)))

;;; (defun |!>| (x y) 
;;;  (> x y))

;;; (defun |!>-1| (x) 
;;;;  (> (car x) (cdr x)))

(defun <=-2 (x y)
  (declare (integer x y))
  (the boolean (<= x y)))

(define-compiler-macro <=-2 (x y)
  `(<= ,(the-int x) ,(the-int y)))

(defun |!<=| (x)
  (<= (car x) (cdr x)))

(define-compiler-macro >=-2 (x y)
  `(>= ,(the-int x) ,(the-int y)))

(define-compiler-macro >-2 (x y)
  `(> ,(the-int x) ,(the-int y)))
;;; 
;;; (defun |!>=| (x y)
;;;   (>= x y))
;;; (defun |!>=-1| (x)
;;;   (>= (car x) (cdr x)))

(defun ~ (x) 
  (declare (integer x))
  (the integer (- 0 x)))

(define-compiler-macro ~ (x)
  `(- 0 ,(the-int x)))

;;; (defun compare (i1 i2) 
;;;     (if (< i1 i2)
;;; 	'(:|Less|)
;;; 	(if (= i1 i2)
;;; 	'(:|Equal|)
;;; 	'(:|Greater|))))
;;; 
;;; (defun compare-1 (x) (compare (car x) (cdr x)))
;;;                                              
;;; (defun |!max| (x y) (if (|!<=| x y) y x))
;;;                                          
;;; (defun |!max|-1 (x) (|!max| (car x) (cdr x)))
;;;                                              
;;; (defun |!min| (x y) (if (|!<=| x y) x y))
;;;                                          
;;; (defun |!min|-1 (x) (|!min| (car x) (cdr x)))
;;;                                              

(define-compiler-macro min-2 (x y)
  `(min ,(the-int x) ,(the-int y)))

(define-compiler-macro max-2 (x y)
  `(max ,(the-int x) ,(the-int y)))

