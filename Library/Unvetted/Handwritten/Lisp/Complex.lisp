(defpackage :Complex-Spec)
(defpackage :Complex_)
(in-package :Complex-Spec)


;;; For each binary op in the spec Complex without a def, there are two Lisp
;;; functions. One takes two arguments, the other takes one argument that is a
;;; pair. In MetaSlang, there is no such distinction: all ops are really
;;; unary, from a domain sort D to a codomain sort C, where D can be a
;;; product, e.g. A * B, in which case the op can be "viewed" as being
;;; binary. These double variants match Specware's Lisp code generator, which
;;; generates two variants for ops whose domain is a product: one that takes
;;; one argument for each factor, and the other that takes just one argument
;;; that is a tuple. The naming convention is that the variant that takes just
;;; one argument has the name directly derived from the op name from which it
;;; is generated, while the variant that takes n arguments (n > 1) has that
;;; name with a "-n" suffix.

;;; The define-compiler-macro definitions are necessary to get efficient
;;; arithmetic.


;; There is no need to be so complicated unless we expect to declare 
;; *complex-impl* to something other than '(complex double-float) 
;; before loading this file.
;;
;;; mechanism for allowing the user to declare global restrictions on doubles:
;;  (eval-when (compile load)
;;    ;; (defvar specware::*complex-impl* '(complex double-float)))
;;    (defvar specware::*complex-impl* '(complex rational)))
;;  
;;  (defmacro the-complex (x)
;;    `(the ,specware::*complex-impl* ,x))

(defmacro the-complex (x)
  `(the (complex double-float) ,x))

(defmacro the-complex-int (x)
  `(the (complex integer) ,x))

(defun Complex_::|!-| (x)
  (declare (type (complex double-float) x))
  (the-complex (- 0 x)))

(defun +-2 (x y)
  (declare (type (complex double-float) x y))
  (the-complex (+ x y)))

(define-compiler-macro +-2 (x y)
  `(the-complex (+ (the-complex ,x) (the-complex ,y))))

(defun Integer-Spec::|!complex| (xy)
  (declare (cons xy))
  (the (complex integer)
    (complex (Integer-Spec::the-int (car xy)) 
	     (Integer-Spec::the-int (cdr xy)))))

(defun Double::|!complex| (xy)
  (declare (cons xy))
  (the-complex (complex (Double::the-double (car xy)) 
			(Double::the-double (cdr xy)))))

(defun Double::complex-2 (x y)
  (declare (double-float x y))
  (the-complex (complex x y)))

(defun Integer-Spec::complex-2 (x y)
  (declare (integer x y))
  (the-complex-int (complex x y)))

(defun |!+| (xy)
  (declare (cons xy))
  (the-complex (+ (the-complex (car xy)) (the-complex (cdr xy)))))

(defun --2 (x y)
  (declare (type (complex double-float) x y))
  (the-complex (- x y)))

(define-compiler-macro --2 (x y)
  `(the-complex (- (the-complex ,x) (the-complex ,y))))

(defun |!-| (xy)
  (declare (cons xy))
  (the-complex (- (the-complex (car xy)) (the-complex (cdr xy)))))

(defun *-2 (x y)
  (declare (type (complex double-float) x y))
  (the-complex (* x y)))

(define-compiler-macro *-2 (x y)
  `(the-complex (* (the-complex ,x)
		   (the-complex ,y))))

(defun |!*| (xy)
  (declare (cons xy))
  (the-complex (* (the-complex (car xy))
		  (the-complex (cdr xy)))))

;; Truncation/remainder don't make sense for complex numbers
;; (at least within common lisp).
;; Ordinary division (/) would be reasonable.
;; 
;; (defun div-2 (x y)
;;   (declare (type (complex double-float) x y))
;;   (the-complex (cl::truncate x y)))
;; 
;; (define-compiler-macro div-2 (x y)
;;   `(the-complex (cl:truncate (the-complex ,x) (the-complex ,y))))
;; 
;; (defun div (xy)
;;   (declare (cons xy))
;;   (the-complex (cl:truncate (the-complex (car xy)) (the-complex (cdr xy)))))
;;
;; (defun rem-2 (x y)
;;   (declare (the (complex double-float) x y))
;;   (the-complex (cl:rem x y)))
;; 
;; (define-compiler-macro rem-2 (x y)
;;   `(the-complex (cl:rem (the-complex ,x) (the-complex ,y))))
;; 
;; (defun |!rem| (xy)
;;   (declare (cons xy))
;;   (the-complex (cl::rem (the-complex (car xy)) (the-complex (cdr xy)))))


;; Complex numbers are not ordered...
;;
;; (defun <-2 (x y)
;;   (declare (type (complex double-float) x y))
;;   (the boolean (< x y)))
;; 
;; (define-compiler-macro <-2 (x y)
;;   `(< (the-complex ,x) (the-complex ,y)))
;; 
;; (defun |!<| (xy)
;;   (declare (cons xy))
;;   (< (the-complex (car xy)) (the-complex (cdr xy))))
;; 
;; (defun <=-2 (x y)
;;   (declare (type (complex double-float) x y))
;;   (the boolean (<= x y)))
;; 
;; (define-compiler-macro <=-2 (x y)
;;   `(<= (the-complex ,x) (the-complex ,y)))
;; 
;; (defun |!<=| (xy)
;;   (declare (cons xy))
;;   (<= (the-complex (car xy)) (the-complex (cdr xy))))
;; 
;; (define-compiler-macro >-2 (x y)
;;   `(> (the-complex ,x) (the-complex ,y)))
;; 
;; (define-compiler-macro >=-2 (x y)
;;   `(>= (the-complex ,x) (the-complex ,y)))
;; 
;; (define-compiler-macro max-2 (x y)
;;   `(max (the-complex ,x) (the-complex ,y)))
;; 
;; (define-compiler-macro min-2 (x y)
;;   `(min (the-complex ,x) (the-complex ,y)))

(define-compiler-macro |!abs| (x)
  `(the-complex (abs (the-complex ,x))))

(defun String-Spec::toComplex (str)
  (let ((*read-default-float-format* 'double-float))
    (the-complex (read-from-string str))))

(defun Integer-Spec::toComplex (x)
  (declare (integer x))
  (the-complex (coerce x `(complex double-float))))

(defun Double::toComplex (x)
  (declare (double-float x))
  (the-complex (coerce x `(complex double-float))))

(defun toString (x) 
  (format nil "~s" x))

;; (defun |!floor| (x)
;;  (declare (complex double-float x))
;;  (Integer-Spec::the-int (cl::floor x)))
;;
;; (defun |!ceiling| (x)
;;   (declare (complex double-float x))
;;  (Integer-Spec::the-int (cl::ceiling x)))
;; 

(defun |!sin| (x)
  (declare (type (complex double-float) x))
   (the-complex (sin x)))
 
(defun |!cos| (x)
  (declare (type (complex double-float) x))
  (the-complex (cos x)))

(defun |!tan| (x)
  (declare (type (complex double-float) x))
  (the-complex (tan x)))

(defun |!asin| (x)
  (declare (type (complex double-float) x))
  (the-complex (asin x)))

(defun |!acos| (x)
  (declare (type (complex double-float) x))
  (the-complex (acos x)))

(defun |!atan| (x)
  (declare (type (complex double-float) x))
  (the-complex (atan x)))

(defun |!sqrt| (x)
  (declare (type (complex double-float) x))
  (the-complex (sqrt x)))

(defun |!real| (x)
  (declare (type (complex double-float) x))
  (Double::the-double (realpart x)))

(defun |!imag| (x)
  (declare (type (complex double-float) x))
  (Double::the-double (imagpart x)))
