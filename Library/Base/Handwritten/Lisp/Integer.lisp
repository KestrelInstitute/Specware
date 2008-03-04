(defpackage :SpecToLisp)
(defpackage :Integer-Spec)
(defpackage :Integer_)
(defpackage :IntegerAux)
(in-package :Integer-Spec)

(defvar SpecToLisp::SuppressGeneratedDefuns nil) ; note: defvar does not redefine if var already has a value

(setq SpecToLisp::SuppressGeneratedDefuns
  (append '("INTEGER-SPEC::pred"
	    "INTEGER-SPEC::positive?"
	    "INTEGERAUX::|!-|"
	    "INTEGER-SPEC::+-2"
	    "INTEGER-SPEC::|!+|"
	    "INTEGER-SPEC::--2"
	    "INTEGER-SPEC::|!-|"
	    "INTEGER-SPEC::*-2"
	    "INTEGER-SPEC::|!*|"
	    "INTEGER-SPEC::<-2"
	    "INTEGER-SPEC::|!<|"
	    "INTEGER-SPEC::<=-2"
	    "INTEGER-SPEC::|!<=|"
	    "INTEGER-SPEC::div-2"
	    "INTEGER-SPEC::div"
	    "INTEGER-SPEC::rem-2"
	    "INTEGER-SPEC::|!rem|"
	    "INTEGER-SPEC::divides-2"
	    "INTEGER-SPEC::divides"
	    "INTEGER-SPEC::multipleOf-2"
	    "INTEGER-SPEC::multipleOf"
	    "INTEGER-SPEC::gcd-2"
	    "INTEGER-SPEC::|!gcd|"
	    "INTEGER-SPEC::lcm-2"
	    "INTEGER-SPEC::|!lcm|"

            "Integer-Spec::pred"
	    "Integer-Spec::positive?"
	    "IntegerAux::|!-|"
	    "Integer-Spec::+-2"
	    "Integer-Spec::|!+|"
	    "Integer-Spec::--2"
	    "Integer-Spec::|!-|"
	    "Integer-Spec::*-2"
	    "Integer-Spec::|!*|"
	    "Integer-Spec::<-2"
	    "Integer-Spec::|!<|"
	    "Integer-Spec::<=-2"
	    "Integer-Spec::|!<=|"
	    "Integer-Spec::div-2"
	    "Integer-Spec::div"
	    "Integer-Spec::rem-2"
	    "Integer-Spec::|!rem|"
	    "Integer-Spec::divides-2"
	    "Integer-Spec::divides"
	    "Integer-Spec::multipleOf-2"
	    "Integer-Spec::multipleOf"
	    "Integer-Spec::gcd-2"
	    "Integer-Spec::|!gcd|"
	    "Integer-Spec::lcm-2"
	    "Integer-Spec::|!lcm|"
)
	   SpecToLisp::SuppressGeneratedDefuns))


(defvar SpecToLisp::SuppressGeneratedDefuns nil) ; note: defvar does not redefine if var already has a value

(setq SpecToLisp::SuppressGeneratedDefuns
      (append '("Integer-Spec::pred"
		"Integer-Spec::positive?"
		"Integer-Spec::|!+|"
		"Integer-Spec::|!-|"
		"Integer-Spec::|!*|"
		"Integer-Spec::div"
		"Integer_::|!-|"
		"Integeraux::|!-|")
	      SpecToLisp::SuppressGeneratedDefuns))

;;; For each binary op, there are two Lisp functions. One takes two arguments,
;;; the other takes one argument that is a pair. In MetaSlang, there is no such
;;; distinction: all ops are really unary, from a domain sort D to a codomain
;;; sort C, where D can be a product, e.g. A * B, in which case the op can be
;;; "viewed" as being binary. These double variants match Specware's Lisp code
;;; generator, which generates two variants for ops whose domain is a product:
;;; one that takes one argument for each factor, and the other that takes just
;;; one argument that is a tuple. The naming convention is that the variant that
;;; takes just one argument has the name directly derived from the op name from
;;; which it is generated, while the variant that takes n arguments (n > 1) has
;;; that name with a "-n" suffix.

;;; The define-compiler-macro definitions are necessary to get efficient
;;; arithmetic.


;;; mechanism for allowing the user to declare global restrictions on integers:
(eval-when (compile load)
  (defvar specware::*integer-impl* 'integer))

(defmacro the-int (x)
  `(the ,specware::*integer-impl* ,x))

(defconstant zero 0)

(defun succ (x) (+ x 1))

(defun pred (x) (- x 1))

(defun positive? (x) (> x 0))

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

(defun divides-2 (x y)
  (declare (integer x y))
  (the boolean (or (and (eql x 0) (eql y 0))
                   (and (not (eql x 0)) (eql (rem y x) 0)))))

(defun divides (xy)
  (declare (cons xy))
  (divides-2 (car xy) (cdr xy)))

(defun multipleOf-2 (x y)
  (declare (integer x y))
  (the boolean (divides-2 y x)))

(defun multipleOf (xy)
  (declare (cons xy))
  (multipleOf-2 (car xy) (cdr xy)))

(defun gcd-2 (x y)
  (declare (integer x y))
  (the-int (gcd x y)))

(define-compiler-macro gcd-2 (x y)
  `(the-int (gcd (the-int ,x) (the-int ,y))))

(defun |!gcd| (xy)
  (declare (cons xy))
  (the-int (gcd (the-int (car xy)) (the-int (cdr xy)))))

(defun lcm-2 (x y)
  (declare (integer x y))
  (the-int (lcm x y)))

(define-compiler-macro lcm-2 (x y)
  `(the-int (lcm (the-int ,x) (the-int ,y))))

(defun |!lcm| (xy)
  (declare (cons xy))
  (the-int (lcm (the-int (car xy)) (the-int (cdr xy)))))
