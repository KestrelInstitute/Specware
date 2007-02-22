(defpackage :Specware)
(defpackage :Double)
(defpackage :Double_)
(defpackage :Complex)
(defpackage :String-Spec)
(defpackage :Integer-Spec)


(IN-PACKAGE "DOUBLE")


;;; For each binary op in the spec Double without a def, there are two Lisp
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


;;; mechanism for allowing the user to declare global restrictions on doubles:

;; There is no need to be so complicated unless we expect to declare 
;; *double-impl* to something other than 'double-float before loading this file.
;;
;;(eval-when (compile load)
;;  (defvar specware::*double-impl* 'double-float))
;;
;;(defmacro the-double (x)
;;  `(the ,specware::*double-impl* ,x))

(defmacro the-double (x)
  `(the double-float ,x))

(defun -- (x) ; TODO: deprecate 
  (declare (double-float x))
  (the-double (- 0 x)))

(defun Double_::|!-| (x)
  (declare (double-float x))
  (the-double (- 0 x)))

(defun ~ (x) ; TODO: deprecate
  (declare (double-float x))
  (the-double (- 0 x)))

(defun +-2 (x y)
  (declare (double-float x y))
  (the-double (+ x y)))

(define-compiler-macro +-2 (x y)
  `(the-double (+ (the-double ,x) (the-double ,y))))

(defun |!+| (xy)
  (declare (cons xy))
  (the-double (+ (the-double (car xy)) (the-double (cdr xy)))))

(defun --2 (x y)
  (declare (double-float x y))
  (the-double (- x y)))

(define-compiler-macro --2 (x y)
  `(the-double (- (the-double ,x) (the-double ,y))))

(defun |!-| (xy)
  (declare (cons xy))
  (the-double (- (the-double (car xy)) (the-double (cdr xy)))))

(defun *-2 (x y)
  (declare (double-float x y))
  (the-double (* x y)))

(define-compiler-macro *-2 (x y)
  `(the-double (* (the-double ,x) (the-double ,y))))

(defun |!*| (xy)
  (declare (cons xy))
  (the-double (* (the-double (car xy)) (the-double (cdr xy)))))

;; CL::TRUNCATE returns an integer, making the following definitions 
;; for div-2 and div type-incorrect.
;; Since Double.sw doesn't mention div or rem, there is no guide
;; to know how to correct these.  (Do we expect integer or double float?)
;;
;; (defun div-2 (x y)
;;   (declare (double-float x y))
;;   (the-double (cl::truncate x y)))
;;
;; (define-compiler-macro div-2 (x y)
;;   `(the-double (cl:truncate (the-double ,x) (the-double ,y))))
;; 
;; (defun div (xy)
;;   (declare (cons xy))
;;  (the-double (cl:truncate (the-double (car xy)) (the-double (cdr xy)))))

(defun rem-2 (x y)
  (declare (double-float x y))
  (the-double (cl:rem x y)))

(define-compiler-macro rem-2 (x y)
  `(the-double (cl:rem (the-double ,x) (the-double ,y))))

(defun |!rem| (xy)
  (declare (cons xy))
  (the-double (cl::rem (the-double (car xy)) (the-double (cdr xy)))))

(defun <-2 (x y)
  (declare (double-float x y))
  (the boolean (< x y)))

(define-compiler-macro <-2 (x y)
  `(< (the-double ,x) (the-double ,y)))

(defun |!<| (xy)
  (declare (cons xy))
  (< (the-double (car xy)) (the-double (cdr xy))))

(defun <=-2 (x y)
  (declare (double-float x y))
  (the boolean (<= x y)))

(define-compiler-macro <=-2 (x y)
  `(<= (the-double ,x) (the-double ,y)))

(defun |!<=| (xy)
  (declare (cons xy))
  (<= (the-double (car xy)) (the-double (cdr xy))))

(define-compiler-macro >-2 (x y)
  `(> (the-double ,x) (the-double ,y)))

(define-compiler-macro >=-2 (x y)
  `(>= (the-double ,x) (the-double ,y)))

(define-compiler-macro max-2 (x y)
  `(max (the-double ,x) (the-double ,y)))

(define-compiler-macro min-2 (x y)
  `(min (the-double ,x) (the-double ,y)))

(define-compiler-macro |!abs| (x)
  `(abs (the-double ,x)))

(defun String-Spec::toDouble (str)
  (let ((*read-default-float-format* 'double-float))
    (let ((dbl (read-from-string str)))
      (the-double dbl))))

(defun Integer-Spec::toDouble (x)
  (declare (integer x))
  (the-double (coerce x 'double-float)))

(defun toString (x) 
  (format nil "~s" x))

(defun |!floor| (x)
  (declare (double-float x))
  (let ((quot (cl::floor x) ))
    (Integer-Spec::the-int quot)))

(defun |!ceiling| (x)
  (declare (double-float x))
  (let ((quot (cl::ceiling x)))
    (Integer-Spec::the-int quot)))

(defun |!sin| (x)
  (declare (double-float x))
  (the-double (sin x)))

(defun |!cos| (x)
  (declare (double-float x))
  (the-double (cos x)))

(defun |!tan| (x)
  (declare (double-float x))
  (the-double (tan x)))

(defun |!asin| (x)
  (declare (double-float x))
  (the-double (asin x)))

(defun |!acos| (x)
  (declare (double-float x))
  (the-double (acos x)))

(defun |!atan| (x)
  (declare (double-float x))
  (the-double (atan x)))

(defun |!sqrt| (x)
  (declare (double-float x))
  (the (complex double-float) (sqrt x)))
