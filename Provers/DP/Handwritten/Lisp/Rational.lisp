(defpackage "RATIONAL-SPEC")
(defpackage :Rational_)
(IN-PACKAGE "RATIONAL-SPEC")


;;; For each binary op in the spec Rational without a def, there are two Lisp
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


;;; mechanism for allowing the user to declare global restrictions on rationals:
(eval-when (compile load)
  (defvar specware::*rational-impl* 'rational))

(defconstant zero 0)
(defconstant one 1)

(defmacro the-rat (x)
  `(the ,specware::*rational-impl* ,x))

(defun |!denominator| (x)
  (declare (rational x))
  (the-rat (cl:denominator x)))

(defun |!numerator| (x)
  (declare (rational x))
  (the-rat (cl:numerator x)))

(defun -- (x) ; TODO: deprecate 
  (declare (rational x))
  (the-rat (- 0 x)))

(defun Rational_::|!-| (x)
  (declare (rational x))
  (the-rat (- 0 x)))

(defun ~ (x) ; TODO: deprecate
  (declare (rational x))
  (the-rat (- 0 x)))

(defun +-2 (x y)
  (declare (rational x y))
  (the-rat (+ x y)))

(define-compiler-macro +-2 (x y)
  `(the-rat (+ (the-rat ,x) (the-rat ,y))))

(defun |!+| (xy)
  (declare (cons xy))
  (the-rat (+ (the-rat (car xy)) (the-rat (cdr xy)))))

(defun --2 (x y)
  (declare (rational x y))
  (the-rat (- x y)))

(define-compiler-macro --2 (x y)
  `(the-rat (- (the-rat ,x) (the-rat ,y))))

(defun |!-| (xy)
  (declare (cons xy))
  (the-rat (- (the-rat (car xy)) (the-rat (cdr xy)))))

(defun *-2 (x y)
  (declare (rational x y))
  (the-rat (* x y)))

(define-compiler-macro *-2 (x y)
  `(the-rat (* (the-rat ,x) (the-rat ,y))))

(defun |!*| (xy)
  (declare (cons xy))
  (the-rat (* (the-rat (car xy)) (the-rat (cdr xy)))))

(defun div-2 (x y)
  (declare (rational x y))
  (the-rat (cl::/ x y)))

(define-compiler-macro div-2 (x y)
  `(the-rat (cl:/ (the-rat ,x) (the-rat ,y))))

(defun div (xy)
  (declare (cons xy))
  (the-rat (cl:/ (the-rat (car xy)) (the-rat (cdr xy)))))

(defun rem-2 (x y)
  (declare (rational x y))
  (the-rat (cl:rem x y)))

(define-compiler-macro rem-2 (x y)
  `(the-rat (cl:rem (the-rat ,x) (the-rat ,y))))

(defun |!rem| (xy)
  (declare (cons xy))
  (the-rat (cl::rem (the-rat (car xy)) (the-rat (cdr xy)))))

(defun <-2 (x y)
  (declare (rational x y))
  (the boolean (< x y)))

(define-compiler-macro <-2 (x y)
  `(< (the-rat ,x) (the-rat ,y)))

(defun |!<| (xy)
  (declare (cons xy))
  (< (the-rat (car xy)) (the-rat (cdr xy))))

(defun <=-2 (x y)
  (declare (rational x y))
  (the boolean (<= x y)))

(define-compiler-macro <=-2 (x y)
  `(<= (the-rat ,x) (the-rat ,y)))

(defun |!<=| (xy)
  (declare (cons xy))
  (<= (the-rat (car xy)) (the-rat (cdr xy))))

(define-compiler-macro >-2 (x y)
  `(> (the-rat ,x) (the-rat ,y)))

(define-compiler-macro >=-2 (x y)
  `(>= (the-rat ,x) (the-rat ,y)))

(define-compiler-macro max-2 (x y)
  `(max (the-rat ,x) (the-rat ,y)))

(define-compiler-macro min-2 (x y)
  `(min (the-rat ,x) (the-rat ,y)))

(define-compiler-macro |!abs| (x)
  `(abs (the-rat ,x)))

(defun ratToString (x)
  (declare (type rational x))
  (the string (princ-to-string x)))

(defun intToRat (x)
  (declare (type rational x))
  (the rational x))

(defun ratToInt (x)
  (declare (type integer x))
  (the integer (truncate x)))
