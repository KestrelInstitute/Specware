(defpackage "INTEGER-SPEC")
(IN-PACKAGE "INTEGER-SPEC")


;;; For each binary op in the spec Integer whose Lisp code is hand-written,
;;; there are two Lisp functions. One takes two arguments, the other takes one
;;; argument that is a pair. In MetaSlang, there is no such distinction: all
;;; ops are really unary, from a domain sort D to a codomain sort C, where D
;;; can be a product, e.g. A * B, in which case the op can be "viewed" as
;;; being binary. These double variants match Specware's Lisp code generator,
;;; which generates two variants for ops whose domain is a product: one that
;;; takes one argument for each factor, and the other that takes just one
;;; argument that is a tuple. The naming convention is that the variant that
;;; takes just one argument has the name directly derived from the op name
;;; from which it is generated, while the variant that takes n arguments
;;; (n > 1) has that name with a "-n" suffix.


(defun ~ (x) 
  (declare (integer x))
  (the integer (- 0 x)))

(defun +-2 (x y)
  (declare (integer x y))
  (the integer (+ x y)))

;; (define-compiler-macro +-2 (x y)
;;   `(+ ,(the-int x) ,(the-int y)))

(defun |!+| (xy)
  (declare (cons xy))
  (the integer (+ (the integer (car xy)) (the integer (cdr xy)))))

(defun --2 (x y)
  (declare (integer x y))
  (the integer (- x y)))

;; (define-compiler-macro --2 (x y)
;;   `(- ,(the-int x) ,(the-int y)))

(defun |!-| (xy)
  (declare (cons xy))
  (the integer (- (the integer (car xy)) (the integer (cdr xy)))))

(defun *-2 (x y)
  (declare (integer x y))
  (the integer (* x y)))

;; (define-compiler-macro *-2 (x y)
;;   `(* ,(the-int x) ,(the-int y)))

(defun |!*| (xy)
  (declare (cons xy))
  (the integer (* (the integer (car xy)) (the integer (cdr xy)))))

(defun div-2 (x y)
  (declare (integer x y))
  (the integer (cl::truncate x y)))

(defun div (xy)
  (declare (cons xy))
  (the integer (cl::truncate (the integer (car xy)) (the integer (cdr xy)))))

(defun rem-2 (x y)
  (declare (integer x y))
  (the integer (cl::rem x y)))

(defun |!rem| (xy)
  (declare (cons xy))
  (the integer (cl::rem (the integer (car xy)) (the integer (cdr xy)))))

(defun <-2 (x y)
  (declare (integer x y))
  (the boolean (< x y)))

(defun |!<| (xy)
  (declare (cons xy))
  (the integer (< (the integer (car xy)) (the integer (cdr xy)))))

(defun <=-2 (x y)
  (declare (integer x y))
  (the boolean (<= x y)))

(defun |!<=| (xy)
  (declare (cons xy))
  (the integer (<= (the integer (car xy)) (the integer (cdr xy)))))
