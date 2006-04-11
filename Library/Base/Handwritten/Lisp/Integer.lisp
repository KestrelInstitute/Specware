(defpackage "INTEGER-SPEC")
(defpackage "INTEGER_")
(defpackage :IntegerAux)
(IN-PACKAGE "INTEGER-SPEC")


;;; For each binary op in the spec Integer without a def, there are two Lisp
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


;;; mechanism for allowing the user to declare global restrictions on integers:
(eval-when (compile load)
  (defvar specware::*integer-impl* 'integer))

(defmacro the-int (x)
  `(the ,specware::*integer-impl* ,x))

(defun -- (x) ; TODO: deprecate 
  (declare (integer x))
  (the-int (- 0 x)))

(defun Integer_::|!-| (x)
  (declare (integer x))
  (the-int (- 0 x)))

(defun IntegerAux::|!-| (x)
  (declare (integer x))
  (the-int (- 0 x)))

(defun ~ (x) ; TODO: deprecate
  (declare (integer x))
  (the-int (- 0 x)))

(defun +-2 (x y)
  (declare (integer x y))
  (the-int (+ x y)))

(define-compiler-macro +-2 (x y)
  `(the-int (+ (the-int ,x) (the-int ,y))))

(defun |!+| (xy)
  (declare (cons xy))
  (the-int (+ (the-int (car xy)) (the-int (cdr xy)))))

(defun --2 (x y)
  (declare (integer x y))
  (the-int (- x y)))

(define-compiler-macro --2 (x y)
  `(the-int (- (the-int ,x) (the-int ,y))))

(defun |!-| (xy)
  (declare (cons xy))
  (the-int (- (the-int (car xy)) (the-int (cdr xy)))))

(defun *-2 (x y)
  (declare (integer x y))
  (the-int (* x y)))

(define-compiler-macro *-2 (x y)
  `(the-int (* (the-int ,x) (the-int ,y))))

(defun |!*| (xy)
  (declare (cons xy))
  (the-int (* (the-int (car xy)) (the-int (cdr xy)))))

(defun div-2 (x y)
  (declare (integer x y))
  (the-int (cl::truncate x y)))

(define-compiler-macro div-2 (x y)
  `(the-int (cl:truncate (the-int ,x) (the-int ,y))))

(defun div (xy)
  (declare (cons xy))
  (the-int (cl:truncate (the-int (car xy)) (the-int (cdr xy)))))

(defun rem-2 (x y)
  (declare (integer x y))
  (the-int (cl:rem x y)))

(define-compiler-macro rem-2 (x y)
  `(the-int (cl:rem (the-int ,x) (the-int ,y))))

(defun |!rem| (xy)
  (declare (cons xy))
  (the-int (cl::rem (the-int (car xy)) (the-int (cdr xy)))))

(defun <-2 (x y)
  (declare (integer x y))
  (the boolean (< x y)))

(define-compiler-macro <-2 (x y)
  `(< (the-int ,x) (the-int ,y)))

(defun |!<| (xy)
  (declare (cons xy))
  (< (the-int (car xy)) (the-int (cdr xy))))

(defun <=-2 (x y)
  (declare (integer x y))
  (the boolean (<= x y)))

(define-compiler-macro <=-2 (x y)
  `(<= (the-int ,x) (the-int ,y)))

(defun |!<=| (xy)
  (declare (cons xy))
  (<= (the-int (car xy)) (the-int (cdr xy))))

(define-compiler-macro >-2 (x y)
  `(> (the-int ,x) (the-int ,y)))

(define-compiler-macro >=-2 (x y)
  `(>= (the-int ,x) (the-int ,y)))

(define-compiler-macro max-2 (x y)
  `(max (the-int ,x) (the-int ,y)))

(define-compiler-macro min-2 (x y)
  `(min (the-int ,x) (the-int ,y)))

(define-compiler-macro |!abs| (x)
  `(abs (the-int ,x)))

(defun gcd-2 (x y)
  (declare (integer x y))
  (the-int (cl:gcd x y)))

(define-compiler-macro gcd-2 (x y)
  `(cl:gcd (the-int ,x) (the-int ,y)))

(defun |!gcd| (xy)
  (declare (cons xy))
  (cl:gcd (the-int (car xy)) (the-int (cdr xy))))

(defun lcm-2 (x y)
  (declare (integer x y))
  (the-int (cl:lcm x y)))

(define-compiler-macro lcm-2 (x y)
  `(cl:lcm (the-int ,x) (the-int ,y)))

(defun |!lcm| (xy)
  (declare (cons xy))
  (cl:lcm (the-int (car xy)) (the-int (cdr xy))))
