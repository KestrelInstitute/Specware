;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: knuth-bendix-ordering.lisp
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

(defun get-constant-knuth-bendix-ordering-index (x)
  (let ((index (constant-knuth-bendix-ordering-index x)))
    (unless (integerp index)
      (error "Unique integer Knuth-Bendix index should have been declared for symbol ~A." x))
    index))

(defun get-function-knuth-bendix-ordering-index (x)
  (let ((index (function-knuth-bendix-ordering-index x)))
    (unless (integerp index)
      (error "Unique integer Knuth-Bendix index should have been declared for symbol ~A." x))
    index))

(defmacro variable-knuth-bendix-ordering-weight (variable)
  (declare (ignore variable))
  `*knuth-bendix-ordering-minimum-constant-weight*)

(defun knuth-bendix-ordering-minimum-weight-of-term (term subst)
  (dereference 
    term subst
    :if-variable (variable-knuth-bendix-ordering-weight term)
    :if-constant (constant-knuth-bendix-ordering-weight term)
    :if-compound (let ((head (head term))
		       (args (args term))
		       n)
		   (let ((w (function-knuth-bendix-ordering-weight head)))
		     (cond
		       ((consp w)
			(setq n (car w))
			(loop for arg in args
			      as weight in (cdr w)
			      do (incf n (* (knuth-bendix-ordering-minimum-weight-of-term arg subst) weight))))
		       (t
			(setq n w)
			(when (function-associative head)
			  (setq n (* (1- (MAX 2 (length args))) n)))	;DO SOMETHING DIFFERENT FOR ZERO OR ONE ARGS
			(loop for arg in args
			      do (incf n (knuth-bendix-ordering-minimum-weight-of-term arg subst))))))
		   n)))

(defun count-variables (term subst &optional (inc 1) counts)
  (dereference
    term subst
    :if-variable (let ((v (assoc/eq term counts)))
		   (cond
		     ((null v)
		      (acons term inc counts))
		     (t
		      (incf (cdr v) inc)
		      counts)))
    :if-constant counts
    :if-compound (dolist (arg (args term) counts)
		   (setq counts (count-variables arg subst inc counts)))))

(defun kbo-count-variables (term subst &optional (inc 1) counts)
  (dereference
    term subst
    :if-variable (let ((v (assoc term counts)))
		   (cond
		     ((null v)
		      (acons term inc counts))
		     (t
		      (incf (cdr v) inc)
		      counts)))
    :if-constant counts
    :if-compound (let ((w (function-knuth-bendix-ordering-weight (head term))))
		   (cond
		     ((consp w)
		      (loop for arg in (args term)
			    as weight in (cdr w)
			    do (setq counts (kbo-count-variables arg subst (* weight inc) counts))
			    finally (return counts)))
		     (t
		      (dolist (arg (args term) counts)
			(setq counts (kbo-count-variables arg subst inc counts))))))))

(defmacro kbo-compare-variable*compound (x y subst <)
  `(cond
     ((variable-occurs-p ,x ,y ,subst)
      ',<)
     (t
      '?)))

(defmacro kbo-compare-constant*compound (x y subst < >)
  `(let ((m (constant-knuth-bendix-ordering-weight ,x))
	 (n (knuth-bendix-ordering-minimum-weight-of-term ,y ,subst)))
     (cond
       ((< m n)
	',<)
       ((> m n)
	(cond
	  ((ground-p ,y ,subst)
	   ',>)
	  (t
	   '?)))
       ((< (get-constant-knuth-bendix-ordering-index ,x)
	   (get-function-knuth-bendix-ordering-index (head ,y)))
	',<)
       ((ground-p ,y ,subst)
	',>)
       (t
	'?))))

(defun knuth-bendix-ordering-compare-terms (x y subst)
  ;; knuth-bendix ordering is controlled by operator weights (>= 0) and indexes (1...N)
  ;; each nullary operator must have positive weight
  ;; each unary operator must have positive weight, with the possible exception of the highest indexed operator
  ;; total on ground terms
  ;; if x > y then xs > ys for substitution s
  ;; x > y if y is a subterm of x
  ;; (compare requirements for strong simplification ordering, CADE-8 pp. 142-143)
  (match-term
    x y subst
    :if-variable*constant '?
    :if-constant*variable '?
    :if-variable*compound (kbo-compare-variable*compound x y subst <)
    :if-compound*variable (kbo-compare-variable*compound y x subst >)
    :if-constant*compound (kbo-compare-constant*compound x y subst < >)
    :if-compound*constant (kbo-compare-constant*compound y x subst > <)
    :if-variable*variable (cond
			    ((eq x y)
			     '=)
			    (t
			     '?))
    :if-constant*constant (cond
			    ((eql x y)
			     '=)
			    ((numberp x)
			     (cond
			       ((numberp y)
				(let ((m x)
				      (n y))
				  (cond
				    ((= m n)
				     '=)
				    ((< m n)
				     '<)
				    ((> m n)
				     '>)
				    (t
				     '?))))
			       (t
				'<)))
			    ((numberp y)
			     '>)
			    (t
			     (let ((m (constant-knuth-bendix-ordering-weight x))
				   (n (constant-knuth-bendix-ordering-weight y)))
			       (cond
				 ((> m n)
				  '>)
				 ((< m n)
				  '<)
				 ((> (get-constant-knuth-bendix-ordering-index x)
				     (get-constant-knuth-bendix-ordering-index y))
				  '>)
				 (t
				  '<)))))
    :if-compound*compound (let ((m (knuth-bendix-ordering-minimum-weight-of-term x subst))
				(n (knuth-bendix-ordering-minimum-weight-of-term y subst))
				(variable-counts (kbo-count-variables y subst -1 (kbo-count-variables x subst))))
			    (cond
			      ((> m n)
			       (dolist (vc variable-counts '>)
				 (unless (>= (cdr vc) 0)
				   (return '?))))
			      ((< m n)
			       (dolist (vc variable-counts '<)
				 (unless (<= (cdr vc) 0)
				   (return '?))))
			      ((dolist (vc variable-counts nil)
				 (unless (= (cdr vc) 0)
				   (return '?)))
			       )
			      ((eq (head x) (head y))
                               (case (function-arity (head x))
                                 (1
                                  (knuth-bendix-ordering-compare-terms (arg1 x) (arg1 y) subst))
                                 ((:alist :plist)
                                  ;;                                (unimplemented)
                                  '?)
                                 (otherwise
                                  (ecase (or (function-ordering-status (head x))
                                             (knuth-bendix-ordering-status?))
                                    ((:multiset :ac)
                                     ;;				      (unimplemented)
                                     '?)
                                    (:right-to-left
                                     (do ((xargs (REVERSE (args x)) (rest xargs))
                                          (yargs (REVERSE (args y)) (rest yargs)))
                                         ((null xargs) nil)	;assumes fixed arity
                                       (cond
                                        ((equal-p (first xargs) (first yargs) subst)
                                         )
                                        (t
                                         (return (knuth-bendix-ordering-compare-terms
                                                  (first xargs) (first yargs) subst))))))
                                    (:left-to-right
                                     (do ((xargs (args x) (rest xargs))
                                          (yargs (args y) (rest yargs)))
                                         ((null xargs) nil)	;assumes fixed arity
                                       (cond
                                        ((equal-p (first xargs) (first yargs) subst)
                                         )
                                        (t
                                         (return (knuth-bendix-ordering-compare-terms
                                                  (first xargs) (first yargs) subst))))))))))
			      ((> (get-function-knuth-bendix-ordering-index (head x))
				  (get-function-knuth-bendix-ordering-index (head y)))
			       '>)
			      (t
			       '<)))))

;;; special handling for associative functions with zero or one arguments????
;;; incompatible with commutative unification?

;;; knuth-bendix-ordering.lisp EOF
