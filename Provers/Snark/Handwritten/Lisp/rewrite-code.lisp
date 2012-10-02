;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: rewrite-code.lisp
;;; The contents of this file are subject to the Mozilla Public License
;;; Version 1.1 (the "License"); you may not use this file except in
;;; compliance with the License. You may obtain a copy of the License at
;;; http://www.mozilla.org/MPL/
;;;
;;; Software distributed under the License is distributed on an "AS IS"
;;; basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See the
;;; License for the specific language governing rights and limitations
;;; under the License.
;;;
;;; The Original Code is SNARK.
;;; The Initial Developer of the Original Code is SRI International.
;;; Portions created by the Initial Developer are Copyright (C) 1981-2002.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :snark)

;;; some other things use-code-for-numbers doesn't do
#+ignore
(progn
  (declare-inequality-rewrites)
  (assert-rewrite '(= (* 0 ?x) 0) :name '0*X=0)
  (assert-rewrite '(= (* 1 ?x) ?x) :name '1*X=X)
  (assert-rewrite '(= (+ 0 ?x) ?x) :name '0+X=X)
  (assert-rewrite '(= (- ?x 0) ?x))
  (assert-rewrite '(= (- 0 ?x) (- ?x)))
  (assert-rewrite '(= (- ?x ?x) 0))
  (assert-rewrite '(= (/ ?x 1) ?x))
  (assert-rewrite '(= (/ 1 ?x) (/ ?x))))

(defun declare-inequality-rewrites ()
  (declare-relation '=  2 :rewrite-code 'equality-rewriter)
  (declare-relation '<  2 :rewrite-code '<-atom-rewriter)
  (declare-relation '>  2 :rewrite-code '>-atom-rewriter)
  (declare-relation '=< 2 :rewrite-code '=<-atom-rewriter)
  (declare-relation '>= 2 :rewrite-code '>=-atom-rewriter)
  (assert '(all (x) (not (< x x))) :name '~X<X)
  (assert '(all (x) (not (> x x))) :name '~X>X)
  (assert '(all (x) (=< x x)) :name 'X=<X)
  (assert '(all (x) (>= x x)) :name 'X>=X)
  nil)

(defun declare-kif-sets ()
  (dolist (x '((setof :any)
	       (union :any)
	       (intersection :any)
	       (difference :any)
	       (complement 1)
	       (generalized-union 1)
	       (generalized-intersection 1)))
    (let ((name (first x))
	  (arity (second x))
	  (rewrite-function (third x)))
      (declare-function name arity :rewrite-code rewrite-function)))
  (dolist (x '((set 1)
	       (bounded 1)
	       (empty 1)
	       (subset 2)
	       (proper-subset 2)
	       (disjoint 2)
	       (pairwise-disjoint :any)
	       (mutually-disjoint :any)
	       (set-partition :any)
	       (set-cover :any)))
    (let ((name (first x))
	  (arity (second x))
	  (rewrite-function (third x)))
      (declare-relation name arity :rewrite-code rewrite-function))))

(defun declare-kif-functions-and-relations ()
  (dolist (x '((value :any)
	       (apply 2)
	       (map 2)
	       (universe 1)))
    (let ((name (first x))
	  (arity (second x))
	  (rewrite-function (third x)))
      (declare-function name arity :rewrite-code rewrite-function)))
  (dolist (x '((relation 1)
	       (function 1)
	       (holds 2)
	       (unary-relation 1)
	       (binary-relation 1)
	       (inverse 1)
	       (composition 2)
	       (one-one 1)
	       (many-one 1)
	       (one-many 1)
	       (many-many 1)
	       (unary-function 1)
	       (binary-function 1)))
    (let ((name (first x))
	  (arity (second x))
	  (rewrite-function (third x)))
      (declare-relation name arity :rewrite-code rewrite-function))))

(declaim (special *using-sorts*))

(defun equality-rewriter (atom subst)
  (mvlet ((*=* (head atom))
          ((:list x y) (args atom)))
    (equality-rewrite* x y subst)))

(defun equality-rewrite* (x y subst)
  (or (and (not (use-code-for-equality?)) none)
      (dereference
       x subst
       :if-variable (dereference
                     y subst
                     :if-variable (cond
                                   ((eq x y)
                                    true)))
       :if-constant (dereference
                     y subst
                     :if-constant (cond
                                   ((eql x y)
                                    true)
                                   ((and (constant-constructor2 x)
                                         (constant-constructor2 y))
                                    false))
                     :if-compound-cons (cond
                                        ((constant-constructor2 x)
                                         false))
                     :if-compound-appl (cond
                                        ((and (constant-constructor2 x)
                                              (function-constructor (heada y)))
                                         false)))
       :if-compound-cons (dereference
                          y subst
                          :if-constant (cond
                                        ((constant-constructor2 y)
                                         false))
                          :if-compound-cons (equality-rewrite*-for-conses x y subst)
                          :if-compound-appl (cond
                                             ((function-constructor (heada y))
                                              false)))
       :if-compound-appl (dereference
                          y subst
                          :if-constant (cond
                                        ((and (function-constructor (heada x))
                                              (constant-constructor2 y))
                                         false))
                          :if-compound-cons (cond
                                             ((function-constructor (heada x))
                                              false))
                          :if-compound-appl (cond
                                             ((equal-p x y subst)
                                              true)
                                             (t
                                              (let ((fn1 (heada x)) (fn2 (heada y)))
                                                (cond
                                                 ((and (function-constructor fn1)
                                                       (function-constructor fn2))
                                                  (cond
                                                   ((neq fn1 fn2)
                                                    false)
                                                   (t
                                                    (equality-rewrite*-for-conses
                                                     (argsa x) (argsa y) subst))))))))))
      (if (and *using-sorts* (not (sort-compatible-p x y subst))) false nil)
      none))

(defun equality-rewrite*-for-conses (x y subst)
  ;; note: returns nil rather than none if no simplification
  (let (a* d*)
    (cond
     ((eq false (setq a* (equality-rewrite* (car x) (car y) subst)))
      false)
     ((eq false (setq d* (equality-rewrite* (cdr x) (cdr y) subst)))
      false)
     ((eq true a*)
      (if (neq none d*) d* (make-compound *=* (cdr x) (cdr y))))
     ((eq true d*)
      (if (neq none a*) a* (make-compound *=* (car x) (car y))))
     ((neq none a*)
      (cond
       ((neq none d*)
        (make-compound *=* (cons (arg1 a*) (arg1 d*)) (cons (arg2 a*) (arg2 d*))))
       (t
        (make-compound *=* (cons (arg1 a*) (cdr x)) (cons (arg2 a*) (cdr y))))))
     ((neq none d*)
      (make-compound *=* (cons (car x) (arg1 d*)) (cons (car y) (arg2 d*)))))))

(defun reflexivity-rewriter (atom subst)
  ;; example: this is called when trying to rewrite (rel a b) after
  ;; doing (declare-relation 'rel 2 :rewrite-code 'reflexivity-rewriter)
  ;; (rel a b) -> true after unifying a and b
  ;; returns new value (true) or none (no rewriting done)
  (let ((args (args atom)))
    (if (equal-p (first args) (second args) subst) true none)))

(defun irreflexivity-rewriter (atom subst)
  ;; example: this is called when trying to rewrite (rel a b) after
  ;; doing (declare-relation 'rel 2 :rewrite-code 'irreflexivity-rewriter)
  ;; (rel a b) -> false after unifying a and b
  ;; returns new value (false) or none (no rewriting done)
  (let ((args (args atom)))
    (if (equal-p (first args) (second args) subst) false none)))

(defun nonvariable-rewriter (atom subst)
  (let ((x (arg1 atom)))
    (dereference
     x subst
     :if-variable none
     :if-constant true
     :if-compound true)))

(defun the-term-rewriter (term subst)
  ;; (the sort value) -> value, if value's sort is a subsort of sort
  (let* ((args (args term))
         (arg1 (first args))
         (arg2 (second args)))
    (if (dereference
         arg1 subst
         :if-constant (and (sort-name-p arg1) (subsort-p (term-sort arg2 subst) (input-sort arg1))))
        arg2
        none)))

(defun and-wff-rewriter (wff subst)
  (let ((wff* (conjoin* (args wff) subst)))
    (if (equal-p wff wff* subst) none wff*)))

(defun or-wff-rewriter (wff subst)
  (let ((wff* (disjoin* (args wff) subst)))
    (if (equal-p wff wff* subst) none wff*)))

(defun implies-wff-rewriter (wff subst)
  (let ((args (args wff)))
    (implies-wff-rewriter1 (first args) (second args) subst)))

(defun implied-by-wff-rewriter (wff subst)
  (let ((args (args wff)))
    (implies-wff-rewriter1 (second args) (first args) subst)))

(defun implies-wff-rewriter1 (x y subst)
    (or (match-term
	  x y subst
	  :if-variable*variable (cond
				  ((eq x y)
				   true))
	  :if-variable*constant (cond
				  ((eq true y)
				   true)
				  ((eq false y)
				   (negate x subst)))
	  :if-constant*variable (cond
				  ((eq true x)
				   y)
				  ((eq false x)
				   true))
	  :if-constant*constant (cond
				  ((eql x y)
				   true)
				  ((eq true x)
				   y)
				  ((eq false x)
				   true)
				  ((eq true y)
				   true)
				  ((eq false y)
				   (negate x subst)))
	  :if-variable*compound (cond
				  ((and (negation-p y) (eq x (arg1 y)))
				   false))
	  :if-compound*variable (cond
				  ((and (negation-p x) (eq (arg1 x) y))
				   false))
	  :if-constant*compound (cond
				  ((eq true x)
				   y)
				  ((eq false x)
				   true)
				  ((and (negation-p y) (eql x (arg1 y)))
				   false))
	  :if-compound*constant (cond
				  ((eq true y)
				   true)
				  ((eq false y)
				   (negate x subst))
				  ((and (negation-p x) (eql (arg1 x) y))
				   false))
	  :if-compound*compound (cond
				  ((equal-p x y subst)
				   true)
				  ((and (negation-p x) (equal-p (arg1 x) y subst))
				   false)
				  ((and (negation-p y) (equal-p x (arg1 y) subst))
				   false)))
	none))

(defun distributive-law1-p (lhs rhs &optional subst)
  ;; checks if LHS=RHS is of form X*(Y+Z)=(X*Y)+(X*Z) for variables X,Y,Z and distinct function symbols *,+
  (let (fn1 fn2 vars sort)
    (and (dereference
	   lhs subst
	   :if-compound (progn (setq fn1 (head lhs)) t))
	 (dereference
	   rhs subst
	   :if-compound (neq (setq fn2 (head rhs)) fn1))
	 (= (length (setq vars (variables rhs subst (variables lhs subst)))) 3)
	 (same-sort-p (setq sort (variable-sort (first vars))) (variable-sort (second vars)))
	 (same-sort-p sort (variable-sort (third vars)))
	 (let ((x (make-variable sort))
	       (y (make-variable sort))
	       (z (make-variable sort)))
	   (variant-p (cons (make-compound fn1 x (make-compound fn2 y z))
			    (make-compound fn2 (make-compound fn1 x y) (make-compound fn1 x z)))
		      (cons lhs rhs)
		      subst)))))

(defun cancel1 (eq fn identity terms1 terms2 subst)
  (prog->
    (count-arguments fn terms2 subst (count-arguments fn terms1 subst) -1 -> terms-and-counts cancel)
    (cond
      ((null cancel)
       none)
      (t
       (quote nil -> args1)
       (quote nil -> args2)
       (progn
	 (dolist terms-and-counts ->* v)
	 (tc-count v -> count)
	 (cond
	   ((> count 0)
	    (setq args1 (consn (tc-term v) args1 count)))
	   ((< count 0)
	    (setq args2 (consn (tc-term v) args2 (- count))))))
       (if (or (and (null args1) args2 (null (cdr args2)) (eql identity (car args2)))
	       (and (null args2) args1 (null (cdr args1)) (eql identity (car args1))))	;don't simplify x+0=x
	   none
	   (make-compound eq
			     (make-a1-compound* fn identity args1)
			     (make-a1-compound* fn identity args2)))))))

(defun make-cancel (eq fn identity)
  (lambda (equality subst)
    (prog->
      (dereference equality subst :if-compound (eq eq (head equality)))
      (args equality -> args)
      (first args -> x)
      (second args -> y)
      (cond
       ((dereference x subst :if-compound (eq fn (head x)))
        (cancel1 eq fn identity (args x) (list y) subst))
       ((dereference y subst :if-compound (eq fn (head y)))
        (cancel1 eq fn identity (list x) (args y) subst))
       (t
        none)))))

(defun declare-cancellation-law (equality-relation-symbol function-symbol identity-symbol)
  (let ((eq (input-symbol equality-relation-symbol))
	(fn (input-symbol function-symbol))
	(id (input-symbol identity-symbol)))
    (declare-relation equality-relation-symbol :any :rewrite-code (make-cancel eq fn id))))

(defun distribute (fn1 fn2 term subst)
  ;; (distribute '+ '* '(* (+ a b) c)) = (+ (a c) (b c))
  ;; assumes fn2 heads term
  (let ((l (distribute1 fn1 (flatargs term subst) subst)))
    (cond
      ((null (cdr l))
       (car l))
      (t
       (make-compound* fn1 (mapcar (lambda (x) (make-compound* fn2 x)) l))))))	;force to binary functions if necessary

(defun distribute1 (fn args subst)
  ;; yields ((a c) (b c)) from ((+ a b) c)
  (cond
    ((null args)
     (list nil))
    (t
     (let* ((arg (first args))
	    (arg* (dereference
		    arg subst
		    :if-variable arg
		    :if-constant arg
		    :if-compound (cond
				   ((eq fn (head arg))
				    (flatargs arg subst))
				   (t
				    arg))))
	    (l (distribute1 fn (rest args) subst)))
       (if (eql arg arg*)
	   (loop for x in l
		 collect (if (eq x (rest args))
			     args
			     (cons arg x)))
	   (loop for x in l
		 nconc (loop for y in arg*
			     collect (cons y x))))))))

(defun declare-distributive-law (fn1 fn2)
  (let ((fn1 (input-symbol fn1))
	(fn2 (input-symbol fn2)))
    (declare-function 
     fn2 (function-arity fn2)
     :rewrite-code (lambda (term subst) (distribute fn1 fn2 term subst)))))

;;; rewrite-code.lisp EOF
