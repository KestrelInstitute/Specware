;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: sparse-vector-expression.lisp
;;; Copyright (c) 2001-2002 Mark E. Stickel
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a
;;; copy of this software and associated documentation files (the "Software"),
;;; to deal in the Software without restriction, including without limitation
;;; the rights to use, copy, modify, merge, publish, distribute, sublicense,
;;; and/or sell copies of the Software, and to permit persons to whom the
;;; Software is furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included
;;; in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(in-package :mes)
(eval-when (:compile-toplevel :load-toplevel :execute)
  (export '(sparse-vector-expression-p
            map-sparse-vector-expression
            map-sparse-vector-expression-with-indexes
            map-sparse-vector-expression-indexes-only
            optimize-sparse-vector-expression))
  (export '(uniond)))

;;; compute intersection and union of sparse-vectors
;;; <sparse-vector-expression> ::=
;;;   <sparse-vector> |
;;;   (intersection <sparse-vector-expression>+) |
;;;   (union <sparse-vector-expression>+) |
;;;   (uniond <sparse-vector-expression>+)
;;; assumes that default-value for sparse-vectors is nil
;;; elements of unions are not mapped in order

(defun sparse-vector-expression-p (x)
  (cond
   ((atom x)
    (WHEN (SNARK::PATH-INDEX-LEAF-NODE-P X)
      (SETF X (SNARK::PATH-INDEX-LEAF-NODE-ENTRIES X)))
    (and (sparse-vector-p x) (null (sparse-vector-default-value x))))
   (t
    (and (member (pop x) '(intersection union uniond))
         (sparse-vector-expression-p (first x))
         (dolist (arg (rest x) t)
           (unless (sparse-vector-expression-p arg)
             (return nil)))))))

(definline mem-sparse-vector-expression (index expr)
  (if (atom expr) (sparef expr index) (mem-sparse-vector-expression1 index expr)))

(defun mem-sparse-vector-expression1 (index expr)
  (declare (type cons expr))
  (cond
   ((eq 'intersection (first expr))
    (dolist (e (rest expr) t)
      (unless (mem-sparse-vector-expression index e)
        (return nil))))
   (t							;union, uniond
    (dolist (e (rest expr) nil)
      (when (mem-sparse-vector-expression index e)
        (return t))))))

;;; (intersection sve1 sve2 ... sven) is mapped by generating elements of
;;; sve1 and testing them for membership in sve2 ... sven
;;;
;;; (union sve1 sve2 ... sven) is mapped by generating elements of each svei
;;; and testing them for membership in sve1 ... svei-1 to omit duplicates
;;;
;;; (uniond sve1 sve2 ... sven) is mapped by generating elements of each svei;
;;; either the union of sets is assumed to be disjoint or we don't care about duplicates,
;;; so there is no duplicate elimination during mapping for uniond

(defmacro map-sparse-vector-expression-macro (mapexp2 mapexp funcallexp)
  `(cond
    ((atom expr)
     ,mapexp2)
    (t
     (ecase (pop expr)
       (intersection
        (prog->
          (first expr -> e1)
          (rest expr -> l2)
          ,mapexp
          (dolist l2 ,funcallexp ->* e2)
          (unless (mem-sparse-vector-expression k e2)
            (return))))
       (union
        (prog->
          (dolist expr ->* e1)
          ,mapexp
          (dolist expr ->* e2)
          (cond
           ((eq e1 e2)
            ,funcallexp
            (return))
           ((mem-sparse-vector-expression k e2)
            (return)))))
       (uniond
        (prog->
          (dolist expr ->* e1)
          ,mapexp
          (declare (ignorable k))
          ,funcallexp))))))

;;; if it is provided, the predicate 'filter' is applied to elements immediately
;;; when mapped (e.g., before checking membership in rest of intersection)
;;; in order to ignore unwanted elements quickly

(defun map-sparse-vector-expression-with-indexes0 (function expr reverse filter)
  (map-sparse-vector-expression-macro
   (if (null filter)
       (map-sparse-vector-with-indexes function expr :reverse reverse)
       (prog->
         (map-sparse-vector-with-indexes expr :reverse reverse ->* v k)
         (when (funcall filter v k)
           (funcall function v k))))
   (map-sparse-vector-expression-with-indexes0 e1 reverse filter ->* v k)
   (funcall function v k)))

(defun map-sparse-vector-expression-indexes-only0 (function expr reverse filter)
  (map-sparse-vector-expression-macro
   (if (null filter)
       (map-sparse-vector-indexes-only function expr :reverse reverse)
       (prog->
         (map-sparse-vector-indexes-only expr :reverse reverse ->* k)
         (when (funcall filter k)
           (funcall function k))))
   (map-sparse-vector-expression-indexes-only0 e1 reverse filter ->* k)
   (funcall function k)))

(defun map-sparse-vector-expression0 (function expr reverse filter)
  (map-sparse-vector-expression-macro
   (if (null filter)
       (map-sparse-vector function expr :reverse reverse)
       (prog->
         (map-sparse-vector expr :reverse reverse ->* v)
         (when (funcall filter v)
           (funcall function v))))
   (map-sparse-vector-expression-values2 e1 reverse filter ->* v k)
   (funcall function v)))

(defun map-sparse-vector-expression-values2 (function expr reverse filter)
  (map-sparse-vector-expression-macro
   (if (null filter)
       (map-sparse-vector-with-indexes function expr :reverse reverse)
       (prog->
         (map-sparse-vector-with-indexes expr :reverse reverse ->* v k)
         (when (funcall filter v)
           (funcall function v k))))
   (map-sparse-vector-expression-values2 e1 reverse filter ->* v k)
   (funcall function v k)))

(definline map-sparse-vector-expression (function expr &key reverse filter)
  (map-sparse-vector-expression0 function expr reverse filter))

(definline map-sparse-vector-expression-with-indexes (function expr &key reverse filter)
  (map-sparse-vector-expression-with-indexes0 function expr reverse filter))

(definline map-sparse-vector-expression-indexes-only (function expr &key reverse filter)
  (map-sparse-vector-expression-indexes-only0 function expr reverse filter))

(defun sparse-vector-expression-maxcount (expr)
  ;; upper bound on count for expression
  (cond
   ((atom expr)
    (WHEN (SNARK::PATH-INDEX-LEAF-NODE-P EXPR)
      (SETF EXPR (SNARK::PATH-INDEX-LEAF-NODE-ENTRIES EXPR)))
    (sparse-vector-count expr))
   ((eq 'intersection (pop expr))
    (let ((count (sparse-vector-expression-maxcount (first expr))))
      (dolist (e (rest expr) count)
        (setf count (min count (sparse-vector-expression-maxcount e))))))
   (t							;union, uniond
    (let ((count (sparse-vector-expression-maxcount (first expr))))
      (dolist (e (rest expr) count)
        (setf count (+ count (sparse-vector-expression-maxcount e))))))))

(defun sparse-vector-expression-size (expr)
  ;; number of sparse-vectors in expression
  (cond
   ((atom expr)
    1)
   (t
    (setf expr (rest expr))
    (let ((size (sparse-vector-expression-size (first expr))))
      (dolist (e (rest expr) size)
        (setf size (+ size (sparse-vector-expression-size e))))))))

(defun optimize-sparse-vector-expression (expr)
  (cond
   ((atom expr)
    (WHEN (AND (SNARK::TEST-OPTION14?) (SNARK::PATH-INDEX-LEAF-NODE-P EXPR))
      (SETF EXPR (SNARK::PATH-INDEX-LEAF-NODE-ENTRIES EXPR))))
   ((eq 'intersection (first expr))
    (setf expr (optimize-sparse-vector-expression1 expr #'< #'sparse-vector-expression-maxcount)))
   (t							;union, uniond
    (setf expr (optimize-sparse-vector-expression1 expr #'> #'sparse-vector-expression-maxcount))))
  (LET ((N (SNARK::TEST-OPTION21?)))
    (IF (AND N (CONSP EXPR) (EQ 'INTERSECTION (FIRST EXPR)))
        (FIRSTN EXPR (1+ N))				;keep only first n terms of intersection
        EXPR)))

(defun optimize-sparse-vector-expression1 (expr predicate key)
  ;; destructive
  (let ((fn (first expr))
        (args (rest expr)))
;;  (cl:assert args)
    (cond
     ((null (rest args))
      (optimize-sparse-vector-expression (first args)))
     ((progn
        (mapl (lambda (l) (setf (car l) (optimize-sparse-vector-expression (car l)))) args)
        (setf args (delete-duplicates args :test #'equal))
        (null (rest args)))
      (first args))
     ((progn
        ;; apply absorption laws
        ;; (union a (intersection a b) c) -> (union a c)
        ;; (intersection a (union a b) c) -> (intersection a c)
        (setf args (delete-if (lambda (arg)
                                (and (consp arg)
                                     (not (iff (eq 'intersection fn) (eq 'intersection (first arg))))
                                     (dolist (x (rest arg) nil)
                                       (when (member x args :test #'equal)
                                         (return t)))))
                              args))
        (null (rest args)))
      (first args))
     (t
      (let ((v (rest args)))
        (cond
         ((null (rest v))
          (let ((arg1 (first args)) (arg2 (first v)))
            (when (funcall predicate (funcall key arg2) (funcall key arg1))
              (setf (first args) arg2)
              (setf (first v) arg1))))
         (t
          (mapl (lambda (l) (setf (car l) (let ((x (car l))) (cons (funcall key x) x)))) args)
          (setf args (stable-sort args predicate :key #'car))
          (mapl (lambda (l) (setf (car l) (cdar l))) args))))
      (setf (rest expr) args)
      expr))))

(defun sparse-vector-expression-description (expr)
  (cond
   ((atom expr)
    (WHEN (SNARK::PATH-INDEX-LEAF-NODE-P EXPR)
      (SETF EXPR (SNARK::PATH-INDEX-LEAF-NODE-ENTRIES EXPR)))
    (sparse-vector-count expr))
   (t
    (cons (ecase (first expr) (intersection 'i) (union 'u) (uniond 'ud))
          (mapcar #'sparse-vector-expression-description (rest expr))))))

(defun traced-optimize-sparse-vector-expression (expr)
  (let (expr*)
    (setf expr* (optimize-sparse-vector-expression expr))
    (unless (equal expr expr*)
      (format t "~%Optimizing ~A" (sparse-vector-expression-description expr))
      (format t " yields ~A" (sparse-vector-expression-description expr*)))
    expr*))

;;; sparse-vector-expression.lisp EOF
