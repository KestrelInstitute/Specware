(defpackage "NAT-SPEC")
(IN-PACKAGE "NAT-SPEC")


;;; For each binary op in the spec Nat without a def, there are two Lisp
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


(defun plus (xy) (+ (car xy) (cdr xy)))

(defun minus (xy) (- (car xy) (cdr xy)))

(defun lteq (xy) (<= (car xy) (cdr xy)))

(defun plus-2 (x y) (+ x y))

(defun minus-2 (x y) (- x y))

(defun lteq-2 (x y) (<= x y))

(defun natural? (x) (>= x 0))

