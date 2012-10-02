;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: ac-rpo.lisp
;;; Copyright (c) 1999-2002 Mark E. Stickel
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

(in-package :snark)

;;; recursive-path-ordering extensions for Rubio's "A fully syntactic AC-RPO"

(defun ac-rpo-compare-compounds (fn xargs yargs subst)
  (or (ac-rpo-cache-lookup fn xargs yargs)
      (ac-rpo-cache-store fn xargs yargs (ac-rpo-compare-compounds* fn xargs yargs subst))))

(defun ac-rpo-compare-compounds* (fn xargs yargs subst)
  (let ((com1 nil) (com2 nil) (com3 nil) (com4 nil)
        (always-> t) (always-< t) 
        big-head-of-x no-small-head-of-x
        big-head-of-y no-small-head-of-y)
    (when (and (eq '= (setq com1 (compare-argument-counts xargs yargs subst)))
               (eq '= (rpo-compare-multisets xargs yargs subst '=)))
      (return-from ac-rpo-compare-compounds* '=))
    (dolist (yargs1 (emb-no-big fn yargs subst))
      (case (ac-rpo-compare-compounds fn xargs yargs1 subst)
        (?
         (setq always-> nil))
        ((< =)
         (return-from ac-rpo-compare-compounds* '<))))
    (when always->
      (multiple-value-setq (big-head-of-x no-small-head-of-x)
        (big-head-and-no-small-head fn xargs subst))
      (multiple-value-setq (big-head-of-y no-small-head-of-y)
        (big-head-and-no-small-head fn yargs subst))
      (when (and (case (setq com4 (compare-no-small-heads
                                   fn no-small-head-of-x no-small-head-of-y subst nil))
                   ((> =)
                    t))
                 (or (eq '> com1)
                     (eq '> (setq com2 (rpo-compare-multisets big-head-of-x big-head-of-y subst nil)))
                     (case com1
                       ((>= =)
                        (cond
                         ((and (eq big-head-of-y yargs) (eq '> com2))
                          t)
                         ((and (eq big-head-of-x xargs) (neq '> com2))
                          nil)
                         ((and (eq big-head-of-x xargs) (eq big-head-of-y yargs))
                          (eq '> com2))
                         (t
                          (eq '> (setq com3 (rpo-compare-multisets xargs yargs subst nil)))))))))
        (return-from ac-rpo-compare-compounds* '>)))
    (dolist (xargs1 (emb-no-big fn xargs subst))
      (case (ac-rpo-compare-compounds fn xargs1 yargs subst)
        (?
         (setq always-< nil))
        ((> =)
         (return-from ac-rpo-compare-compounds* '>))))
    (when always-<
      (unless always->
        (multiple-value-setq (big-head-of-x no-small-head-of-x)
          (big-head-and-no-small-head fn xargs subst))
        (multiple-value-setq (big-head-of-y no-small-head-of-y)
          (big-head-and-no-small-head fn yargs subst)))
      (when (and (case (or com4 (compare-no-small-heads
                                 fn no-small-head-of-x no-small-head-of-y subst nil))
                   ((< =)
                    t))
                 (or (eq '< com1)
                     (eq '< (or com2 (setq com2 (rpo-compare-multisets big-head-of-x big-head-of-y subst nil))))
                     (case com1
                       ((<= =)
                        (cond
                         ((and (eq big-head-of-x xargs) (eq '< com2))
                          t)
                         ((and (eq big-head-of-y yargs) (neq '< com2))
                          nil)
                         ((and (eq big-head-of-x xargs) (eq big-head-of-y yargs))
                          (eq '< com2))
                         (t
                          (eq '< (or com3 (rpo-compare-multisets xargs yargs subst '<)))))))))
        (return-from ac-rpo-compare-compounds* '<)))
    '?))

(defun emb-no-big (fn args subst)
  ;; defn 12
  (let ((revargs nil) (result nil) result-last)
    (dotails (args args)
      (let ((argi (first args)))
        (when (dereference argi subst :if-compound (neq '> (symbol-ordering-compare (head argi) fn)))
          (dolist (argij (args argi))
            (collect (revappend
                      revargs
                      (dereference
                       argij subst
                       :if-variable (cons argij (rest args))
                       :if-constant (cons argij (rest args))
                       :if-compound (if (eq fn (head argij))
                                        (append (flatargs argij subst) (rest args))
                                        (cons argij (rest args)))))
              result)))
        (push argi revargs)))
    result))

(defun big-head-and-no-small-head (fn args subst)
  ;; defn 2: big-head is multiset of arguments for which (> (top arg) fn)
  ;; defn 7: no-small-head is multiset of arguments for which (not (< (top arg) fn))
  (labels
    ((big-head-and-no-small-head* (args)
       (if (null args)
           (values nil nil)
           (let* ((l (rest args))
                  (arg (first args))
                  (com (dereference
                        arg subst
                        :if-variable '?
                        :if-constant (symbol-ordering-compare arg fn)
                        :if-compound (symbol-ordering-compare (head arg) fn))))
             (mvlet (((:values big-head no-small-head) (big-head-and-no-small-head* l)))
               (values (if (eq '> com)
                           (if (eq big-head l) args (cons arg big-head))
                           big-head)
                       (if (neq '< com)
                           (if (eq no-small-head l) args (cons arg no-small-head))
                           no-small-head)))))))
    (big-head-and-no-small-head* args)))

(defun compare-no-small-heads (fn no-small-head-of-x no-small-head-of-y subst testval)
  ;; defn 11 comparison function adds the following
  ;; conditions to the usual comparison
  ;;  (> compound compound') : (or (> (head compound) fn) (>= (head compound) (head compound'))
  ;;  (> constant compound)  : (or (> constant fn) (> constant (head compound)))
  ;;  (> compound constant)  : (or (> (head compound) fn) (> (head compound) constant))
  ;;  (> compound variable)  : (> (head compound) fn)
  (symbol-ordering-compare-term-multisets
   no-small-head-of-x no-small-head-of-y subst testval
   (lambda (x y subst testval)
     (ecase testval
       (=
        (rpo-compare-compounds x y subst testval))
       (>
        (and (or (eq '> (symbol-ordering-compare (head x) fn))
                 (case (symbol-ordering-compare (head x) (head y))
                   ((> =)
                    t)))
             (rpo-compare-compounds x y subst testval)))
       (<
        (and (or (eq '> (symbol-ordering-compare (head y) fn))
                 (case (symbol-ordering-compare (head y) (head x))
                   ((> =)
                    t)))
             (rpo-compare-compounds x y subst testval)))
       ((nil)
        (ecase (rpo-compare-compounds x y subst testval)
          (>
           (if (or (eq '> (symbol-ordering-compare (head x) fn))
                   (case (symbol-ordering-compare (head x) (head y))
                     ((> =)
                      t)))
               '>
               '?))
          (<
           (if (or (eq '> (symbol-ordering-compare (head y) fn))
                   (case (symbol-ordering-compare (head y) (head x))
                     ((> =)
                      t)))
               '<
               '?))
          (?
           '?)))))
   (lambda (compound constant subst testval)
     (ecase testval
       (>
        (and (or (eq '> (symbol-ordering-compare (head compound) fn))
                 (eq '> (symbol-ordering-compare (head compound) constant)))
             (symbol-ordering-compare-compound*constant compound constant subst testval)))
       (<
        (and (or (eq '> (symbol-ordering-compare constant fn))
                 (eq '> (symbol-ordering-compare constant (head compound))))
             (symbol-ordering-compare-compound*constant compound constant subst testval)))
       ((nil)
        (ecase (symbol-ordering-compare-compound*constant compound constant subst testval)
          (>
           (if (or (eq '> (symbol-ordering-compare (head compound) fn))
                   (eq '> (symbol-ordering-compare (head compound) constant)))
               '>
               '?))
          (<
           (if (or (eq '> (symbol-ordering-compare constant fn))
                   (eq '> (symbol-ordering-compare constant (head compound))))
               '<
               '?))
          (?
           '?)))))
   (lambda (compound variable subst)
     (if (eq '> (symbol-ordering-compare (head compound) fn))
         (symbol-ordering-compare-compound*variable compound variable subst)
         '?))))

(defun compare-argument-counts (xargs yargs subst)
  ;; xargs.subst and yargs.subst are already flattened argument lists
  ;; of the same associative function
  ;; this is the AC-RPO comparison of #(x) and #(y) that returns
  ;; =, >, <, >=, =<, or ?
  (let ((variable-counts nil) (variable-count 0) (nonvariable-count 0))
    (labels
      ((count-arguments (args inc)
         (declare (fixnum inc))
         (let (v)
           (dolist (term args)
             (dereference
              term subst
              :if-variable (cond
                            ((null variable-counts)
                             (setq variable-counts (cons (make-tc term inc) nil)))
                            ((setq v (assoc/eq term variable-counts))
                             (incf (tc-count v) inc))
                            (t
                             (push (make-tc term inc) variable-counts)))
              :if-constant (incf nonvariable-count inc)
              :if-compound (incf nonvariable-count inc))))))
      (count-arguments xargs 1)
      (count-arguments yargs -1)
      (dolist (v variable-counts)
        (let ((c (tc-count v)))
          (cond
           ((plusp c)
            (if (minusp variable-count)
                (return-from compare-argument-counts '?)
                (incf variable-count c)))
           ((minusp c)
            (if (plusp variable-count)
                (return-from compare-argument-counts '?)
                (incf variable-count c))))))
      (cond
       ((plusp variable-count)
        (cond
         ((minusp nonvariable-count)
          (let ((d (+ variable-count nonvariable-count)))
            (cond
             ((eql 0 d)
              '>=)
             ((plusp d)
              '>)
             (t
              '?))))
         (t
          '>)))
       ((minusp variable-count)
        (cond
         ((plusp nonvariable-count)
          (let ((d (+ variable-count nonvariable-count)))
            (cond
             ((eql 0 d)
              '=<)
             ((minusp d)
              '<)
             (t
              '?))))
         (t
          '<)))
       ((eql 0 nonvariable-count)
        '=)
       (t
        (if (plusp nonvariable-count) '> '<))))))

(defun ac-rpo-cache-lookup (fn xargs yargs)
  (dolist (x *ac-rpo-cache* nil)
    (when (and (eq fn (first x))
               (eql-list xargs (first (setq x (rest x))))
               (eql-list yargs (first (setq x (rest x)))))
      (return (first (rest x))))))

(defun ac-rpo-cache-store (fn xargs yargs com)
  (push (list fn xargs yargs com) *ac-rpo-cache*)
  com)

(defun eql-list (l1 l2)
  (loop
    (cond
     ((null l1)
      (return (null l2)))
     ((null l2)
      (return nil))
     ((neql (pop l1) (pop l2))
      (return nil)))))

(defun test-rpo (x y)
  (let* ((v (renumber (input-wff `(dummy ,x ,y))))
         (x (arg1 v))
         (y (arg2 v))
         (com (rpo-compare-terms-top x y)))
    (fresh-line)
    (print-term x)
    (format t "~27T   ")
    (princ com)
    (princ "   ")
    (print-term y)
    com))

(defun ac-rpo-example1 (&optional case)
  (initialize)
  (use-default-ordering nil)
  (declare-constant 'a)
  (declare-constant 'b)
  (declare-function 'g 1)
  (declare-function 'f 2 :associative t :commutative t)
  (declare-function 'h 1)
  (declare-ordering-greaterp 'h 'f 'g 'a 'b)
  (when (implies case (eql 1 case))
    (test-rpo '(f (g (f (h a) a)) a) '(f (h a) a a)))
  (when (implies case (eql 2 case))
    (test-rpo '(f (h a) (g a)) '(f (g (h a)) a)))
  (when (implies case (eql 3 case))
    (test-rpo '(f (g (h a)) b b b) '(f (g (f (h a) a)) a)))
  (when (implies case (eql 4 case))
    (test-rpo '(f (h a) a) '(f (h a) b)))
  nil)

(defun ac-rpo-example2 (&optional case)
  (initialize)
  (use-default-ordering nil)
  (declare-function 'g 1)
  (declare-function 'f 2 :associative t :commutative t)
  (declare-function 'h 1)
  (declare-ordering-greaterp 'h 'f 'g)
  (when (implies case (eql 1 case))
    (test-rpo '(f (g (f (h ?x) ?x)) ?x) '(f (h ?x) ?x ?x)))
  (when (implies case (eql 2 case))
    (test-rpo '(f (h ?x) (g ?x)) '(f (g (h ?x)) ?x)))
  (when (implies case (eql 3 case))
    (test-rpo '(f (g (h ?x)) ?x ?x ?y) '(f (g (f (h ?x) ?y)) ?x)))
  (when (implies case (eql 4 case))
    (test-rpo '(f (g (g ?x)) ?x) '(f (g ?x) (g ?x))))
  nil)

(defun ac-rpo-example3 (&optional case)
  (initialize)
  (use-default-ordering nil)
  (declare-constant '0)
  (declare-function 'i 1)
  (declare-function '+ 2 :associative t :commutative t)
  (declare-function '* 2 :associative t :commutative t)
  (declare-ordering-greaterp '* 'i '+ '0)
  (when (implies case (eql 1 case))
    (test-rpo '(+ ?x 0) '?x))
  (when (implies case (eql 2 case))
    (test-rpo '(+ ?x (i ?x)) '0))
  (when (implies case (eql 3 case))
    (test-rpo '(i 0) '0))
  (when (implies case (eql 4 case))
    (test-rpo '(i (i ?x)) '?x))
  (when (implies case (eql 5 case))
    (test-rpo '(i (+ ?x ?y)) '(+ (i ?x) (i ?y))))
  (when (implies case (eql 6 case))
    (test-rpo '(* ?x (+ ?y ?z)) '(+ (* ?x ?y) (* ?x ?z))))
  (when (implies case (eql 7 case))
    (test-rpo '(* ?x 0) '0))
  (when (implies case (eql 8 case))
    (test-rpo '(* ?x (i ?y)) '(i (* ?x ?y))))
  nil)

(defun ac-rpo-example4 (&optional case)
  (initialize)
  (use-default-ordering nil)
  (declare-constant '0)
  (declare-function 's 1)
  (declare-function '+ 2 :associative t :commutative t)
  (declare-function '* 2 :associative t :commutative t)
  (declare-ordering-greaterp '* '+ 's '0)
  (when (implies case (eql 1 case))
    (test-rpo '(+ ?x 0) '?x))
  (when (implies case (eql 2 case))
    (test-rpo '(+ ?x (s ?y)) '(s (+ ?x ?y))))
  (when (implies case (eql 3 case))
    (test-rpo '(* ?x 0) '0))
  (when (implies case (eql 4 case))
    (test-rpo '(* ?x (s ?y)) '(+ (* ?x ?y) ?x)))
  (when (implies case (eql 5 case))
    (test-rpo '(* ?x (+ ?y ?z)) '(+ (* ?x ?y) (* ?x ?z))))
  nil)

(defun ac-rpo-example5 (&optional case)
  (initialize)
  (use-default-ordering nil)
  (declare-function 'f 2 :associative t :commutative t)
  (declare-function 'g 1)
  (declare-function 'h 1)
  (when (implies case (eql 1 case))
    (test-rpo '(f (g (g ?x)) ?x) '(f (g ?x) (g ?x))))
  (when (implies case (eql 2 case))
    (declare-ordering-greaterp 'g 'h)
    (test-rpo '(f ?x ?x (g ?x)) '(f ?x (h ?x))))
  nil)

(defun ac-rpo-example6 (&optional case)
  (initialize)
  (use-default-ordering nil)
  (declare-function 'l 1)
  (declare-function 't 1)
  (declare-function '+ 2 :associative t :commutative t)
  (declare-ordering-greaterp 'l '+)
  (when (implies case (eql 1 case))
    (test-rpo '(+ 0 ?x) '?x))
  (when (implies case (eql 2 case))
    (test-rpo '(+ ?x ?x) '?x))
  (when (implies case (eql 3 case))
    (test-rpo '(l (t ?x)) '(l ?x)))
  (when (implies case (eql 4 case))
    (test-rpo '(l (+ (t ?y) ?x)) '(+ (l (+ ?x ?y)) (l ?y))))
  (when (implies case (eql 5 case))
    (test-rpo '(t (t ?x)) '(t ?x)))
  (when (implies case (eql 6 case))
    (test-rpo '(+ (t ?x) ?x) '(t ?x)))
  (when (implies case (eql 7 case))
    (test-rpo '(+ (t (+ ?x ?y)) ?x) '(t (+ ?x ?y))))
  (when (implies case (eql 8 case))
    (declare-ordering-greaterp 't '+)
    (test-rpo '(t (+ (t ?y) ?x)) '(+ (t (+ ?x ?y)) (t ?y))))
  nil)

(defun ac-rpo-examples ()
  (ac-rpo-example1)
  (ac-rpo-example2)
  (ac-rpo-example3)
  (ac-rpo-example4)
  (ac-rpo-example5)
  (ac-rpo-example6)
  )

;;; ac-rpo.lisp EOF
