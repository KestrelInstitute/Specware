;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: subst.lisp
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

;;; a substitution is an alternating list of variables and values
;;; substitutions can be manipulated as SNARK terms if this ever becomes useful

(defun bind-variable-to-term (var term subst)
  (cl:assert (neq var term))
  (when (test-option5?)
    (cl:assert (subsort-p (term-sort term subst) (variable-sort var))))
  (cons var (cons term subst)))

(defun lookup-variable-in-substitution (var subst)
  (loop
    (cond
      ((null subst)
       (return none))
      ((eq var (first subst))
       (return (second subst)))
      (t
       (setf subst (cddr subst))))))

(defun lookup-value-in-substitution (value subst)
  (loop
    (cond
      ((null subst)
       (return none))
      ((eql value (second subst))
       (return (first subst)))
      (t
       (setf subst (cddr subst))))))

(defun lookup-value-in-substitution2 (value subst subst2)
  (loop
    (cond
     ((null subst)
      (return none))
     ((equal-p value (second subst) subst2)
      (return (first subst)))
     (t
      (setf subst (cddr subst))))))

(defun map-substitution (cc subst)
  ;; usage: (prog-> (map-substitution subst ->* var value) ...)
  (loop
    (if (null subst)
        (return nil)
        (funcall cc (pop subst) (pop subst)))))

(defun print-substitution (subst)
  (princ "{ ")
  (prog->
    (quote t -> first)
    (map-substitution subst ->* var value)
    (if first
	(setf first nil)
	(princ " , "))
    (print-term var)
    (princ " -> ")
    (print-term value))
  (princ " }")
  subst)

(defun substitution-shorterp (subst1 subst2)
  (loop
    (cond
     ((null subst1)
      (return (not (null subst2))))
     ((null subst2)
      (return nil))
     (t
      (setf subst1 (cddr subst1))
      (setf subst2 (cddr subst2))))))

(defun make-idempotent-substitution (subst)
  ;; create an idempotent substitution from subst
  ;; by instantiating the variable values
  (cond
    ((null subst)
     nil)
    ((null (cddr subst))
     subst)
    (t
     (setq subst (copy-list subst))
     (loop for l on subst by #'cddr
	   do (setf (second l) (instantiate (second l) subst)))
     subst)))

(defun variables (x &optional subst vars)
  "return a list of all the variables that occur in x"
  (dereference
   x subst
   :if-constant vars
   :if-compound-cons (variables (cdrc x) subst (variables (carc x) subst vars))
   :if-compound-appl (cond
                      (subst
                       (dolist (x1 (compound-appl-vars x) vars)
                         (setf vars (variables x1 subst vars))))
                      (vars
                       (let ((vars* vars))
                         (dolist (x1 (compound-appl-vars x) vars*)
                           (unless (member x1 vars :test #'eq)
                             (push x1 vars*)))))
                      (t
                       (compound-appl-vars x)))
   :if-variable (if (member x vars :test #'eq) vars (cons x vars))))

(defun variablesl (l &optional subst vars)
  (dolist (x l vars)
    (setf vars (variables x subst vars))))

(defun first-nonvariable-term (terms &optional subst)
  (dolist (term terms none)
    (dereference
     term subst
     :if-constant (return term)
     :if-compound (return term))))

(defun first-nonvariable-subterm (terms &optional subst)
  (dolist (term terms none)
    (dereference
     term subst
     :if-compound (let ((v (first-nonvariable-term (args term))))
                    (unless (eq none v)
                      (return v))))))

(defun variable-counts (x &optional subst counts)
  "return a list of all the variables that occur in x with their frequency, in dotted pairs"
  (dereference
   x subst
   :if-constant counts
   :if-compound-cons (variable-counts (cdrc x) subst (variable-counts (carc x) subst counts))
   :if-compound-nonground (dolist (x1 (argsa x) counts)
                            (setf counts (variable-counts x1 subst counts)))
   :if-compound-ground counts
   :if-variable (let ((v (assoc/eq x counts)))
                  (if v (progn (incf (cdrc v)) counts) (cons (cons x 1) counts)))))

(defun new-variables (x &optional subst vars)
  "return a list of all the variables that occur in x but are not in vars"
  ;; ldiff could be done destructively
  (ldiff (variables x subst vars) vars))

(defun instantiate (x n &optional subst)
  "applies substitution to x, optionally first renumbering block-0 variables to block-n"
  (cond
   ((constant-p x)
    x)
   (t
    (when (or (consp n) (numberp subst))	;accept n and subst arguments in either order
      (psetq subst n n subst))
    (if (or (null n) (zerop n))
        (if (null subst)
            x					;nop
            (labels				;just substitute
              ((instantiate* (x)
                 (dereference
                  x subst
                  :if-variable x
                  :if-constant x
                  :if-compound-ground x
                  :if-compound-cons (lcons (instantiate* (car x)) (instantiate* (cdr x)) x)
                  :if-compound-nonground (let* ((args (argsa x)) (args* (instantiatel args)))
		                           (if (eq args args*) x (make-compound* (heada x) args*)))))
               (instantiatel (l)
                 (lcons (instantiate* (first l)) (instantiatel (rest l)) l)))
              (instantiate* x)))
        (let ((incr (variable-block n)))
          (if (null subst)
              (labels				;just renumber
                ((instantiate* (x)
                   (dereference
                    x nil
                    :if-variable (let ((n (variable-number x)))
                                   (if (variable-block-0-p n)
                                       (make-variable (variable-sort x) (+ n incr))
                                       x))
                    :if-constant x
                    :if-compound-ground x
                    :if-compound-cons (lcons (instantiate* (car x)) (instantiate* (cdr x)) x)
                    :if-compound-nonground (let* ((args (argsa x)) (args* (instantiatel args)))
		                             (if (eq args args*) x (make-compound* (heada x) args*)))))
                 (instantiatel (l)
                   (lcons (instantiate* (first l)) (instantiatel (rest l)) l)))
	        (instantiate* x))
              (labels				;renumber and substitute
                ((instantiate* (x)
                   (when (variable-p x)
                     (let ((n (variable-number x)))
                       (when (variable-block-0-p n)
	                 (setq x (make-variable (variable-sort x) (+ n incr))))))
                   (dereference
                    x subst
                    :if-variable x
                    :if-constant x
                    :if-compound-ground x
                    :if-compound-cons (lcons (instantiate* (car x)) (instantiate* (cdr x)) x)
                    :if-compound-nonground (let* ((args (argsa x)) (args* (instantiatel args)))
		                             (if (eq args args*) x (make-compound* (heada x) args*)))))
                 (instantiatel (l)
                   (lcons (instantiate* (first l)) (instantiatel (rest l)) l)))
	        (instantiate* x))))))))

(defun renumber (x &optional subst rsubst)
  "applies substitution to x and renumbers variables (normally to block 0)"
  (dereference
   x subst
   :if-constant (values x rsubst)
   :if-compound-ground (values x rsubst)
   :if-compound-cons (values (let (u v)
                               (multiple-value-setq (u rsubst)
                                 (renumber (carc x) subst rsubst))
                               (multiple-value-setq (v rsubst)
                                 (renumber (cdrc x) subst rsubst))
                               (lcons u v x))
                             rsubst)
   :if-compound-nonground (values (let* ((args (argsa x))
                                         (args* (let (dummy)
                                                  (declare (ignorable dummy))
                                                  (multiple-value-setq (dummy rsubst)
                                                    (renumberl args subst rsubst)))))
                                    (if (eq args args*)
                                        x
                                        (make-compound* (head x) args*)))
                                  rsubst) 
   :if-variable (let ((v (lookup-variable-in-substitution x rsubst)))
                  (cond
                   ((neq none v)
                    (values v rsubst))
                   (t
                    (let ((var (renumberv x rsubst)))
                      (values var (cons x (cons var rsubst)))))))))

(defun renumberl (l subst rsubst)
  (let (dummy)
    (declare (ignorable dummy))
    (values (lcons (multiple-value-setq (dummy rsubst)
		     (renumber (first l) subst rsubst))
		   (multiple-value-setq (dummy rsubst)
		     (renumberl (rest l) subst rsubst))
		   l)
	    rsubst)))

(defvar *renumber-first-number* 0)
(defvar *renumber-by-sort* t)

(defun renumberv (var rsubst)
  (let ((sort (variable-sort var)))
    (if (null *renumber-first-number*)
        (make-variable sort)
        (loop
          (cond
           ((null rsubst)
            (return (make-variable sort *renumber-first-number*)))
           (t
            (let ((v (first (setf rsubst (rest rsubst)))))
              (when (implies *renumber-by-sort* (same-sort-p sort (variable-sort v)))
                (return (make-variable sort (1+ (variable-number v))))))
            (setf rsubst (rest rsubst))))))))

(defun renumber-new (x &optional subst rsubst)
  "applies substitution to x and renumbers variables to all new variables"
  (let ((*renumber-first-number* nil))
    (renumber x subst rsubst)))

(defun linearize (term &optional subst vars)
  (dereference
   term subst
   :if-constant (values term vars)
   :if-compound-ground (values term vars)
   :if-variable (let ((var (if (member term vars :test #'eq)
                               (make-variable (variable-sort term))
                               term)))
                  (values var (cons var vars)))
   :if-compound-cons (values
                      (lcons (mvlet (((:values v vars*) (linearize (carc term) subst vars)))
                               (setf vars vars*)
                               v)
                             (mvlet (((:values v vars*) (linearize (cdrc term) subst vars)))
                               (setf vars vars*)
                               v)
                             term)
                      vars)
   :if-compound-nonground (values
                           (mvlet* ((args (argsa term))
                                    ((:values args* vars*) (linearizel args subst vars)))
                             (setf vars vars*)
                             (if (eq args args*)
                                 term
                                 (make-compound* (heada term) args*)))
                           vars)))

(defun linearizel (terms subst vars)
  (values
   (lcons (mvlet (((:values v vars*) (linearize (first terms) subst vars)))
            (setf vars vars*)
            v)
          (mvlet (((:values v vars*) (linearizel (rest terms) subst vars)))
            (setf vars vars*)
            v)
          terms)
   vars))

(defun ground-p (x &optional subst)
  "return t if x is ground, nil otherwise"
  (dereference
   x subst
   :if-constant t
   :if-compound-cons (and (ground-p (carc x) subst)
                          (ground-p (cdrc x) subst))
   :if-compound-appl (loop for x1 in (compound-appl-vars x)
                           always (ground-p x1 subst))
   :if-variable nil))

(defun frozen-p (x subst)
  "return t if all variables of x are frozen, nil otherwise"
  (dereference
   x subst
   :if-constant t
   :if-compound-cons (and (frozen-p (carc x) subst)
                          (frozen-p (cdrc x) subst))
   :if-compound-appl (loop for x1 in (compound-appl-vars x)
                           always (frozen-p x1 subst))
   :if-variable (variable-frozen-p x)))

(defun all-variables-p (terms &optional subst)
  (dolist (term terms t)
    (dereference
     term subst
     :if-constant (return nil)
     :if-compound (return nil))))

(defun occurs-p (x y subst)
  "return t if x occurs in y, nil otherwise"
  (dereference
    x subst
    :if-constant (if (function-symbol-p x)
		     (function-occurs-p x y subst)
		     (constant-occurs-p x y subst))
    :if-compound (compound-occurs-p x y subst)
    :if-variable (variable-occurs-p x y subst)))

(defun function-occurs-p (x y subst)
  (dereference
    y subst
    :if-compound (or (eq x (head y))
		     (loop for y1 in (args y)
			   thereis (function-occurs-p x y1 subst)))))

(defun constant-occurs-p (x y subst)
  "return t if atom x occurs in y, nil otherwise"
  (dereference
    y subst
    :if-constant (eql x y)
    :if-compound (loop for y1 in (args y)
		       thereis (constant-occurs-p x y1 subst))))

(defun compound-occurs-p (x y subst)
  "return t if compound x occurs in y, nil otherwise"
  (dereference
    y subst
    :if-compound (or (equal-p x y subst)
		     (loop for y1 in (args y)
			   thereis (compound-occurs-p x y1 subst)))))

(defun no-new-variable-occurs-p (x subst vars)
  ;; returns t if every variable in x.subst is a member of vars, nil otherwise
  (labels ((no-new-variable (x)
             (dereference
              x subst
              :if-variable (member x vars)
              :if-constant t
              :if-compound-cons (and (no-new-variable (carc x))
                                     (no-new-variable (cdrc x)))
              :if-compound-appl (dolist (x1 (compound-appl-vars x) t)
                                  (unless (no-new-variable x1)
                                    (return nil))))))
    (not (null (no-new-variable x)))))

(defmacro variable-occurs-p1-macro ()
  `(dereference
    y nil
    :if-compound-cons (or (variable-occurs-p1 x (carc y))
                          (variable-occurs-p1 x (cdrc y)))
    :if-compound-appl (let ((l (compound-appl-vars y)))
                        (and l (variable-occurs-p1l x l)))
    :if-variable (eq x y)))

(defmacro variable-occurs-p2-macro ()
  `(dereference
    y subst
    :if-compound-cons (or (variable-occurs-p2 x (carc y) subst)
                          (variable-occurs-p2 x (cdrc y) subst))
    :if-compound-appl (let ((l (compound-appl-vars y)))
                        (and l (variable-occurs-p2l x l subst)))
    :if-variable (eq x y)))

(defun variable-occurs-p1 (x y)
  (variable-occurs-p1-macro))

(defun variable-occurs-p2 (x y subst)
  (variable-occurs-p2-macro))

(defun variable-occurs-p1l (x l)
  (dolist (y l nil)
    (when (variable-occurs-p1-macro)
      (return t))))

(defun variable-occurs-p2l (x l subst)
  (dolist (y l nil)
    (when (variable-occurs-p2-macro)
      (return t))))

(defun variable-occurs-p (x y subst)
  "return t if variable x occurs in y, nil otherwise"
  (if (null subst)
      (variable-occurs-p1-macro)
      (variable-occurs-p2-macro)))

(defun special-unify-p (x subst)
  (dereference
    x subst
    :if-compound (or (function-unify-code (head x))
                     (loop for x1 in (args x)
                           thereis (special-unify-p x1 subst)))))

(defun skolem-occurs-p (x subst)
  (dereference
    x subst
    :if-constant (constant-skolem-p x)
    :if-compound (or (function-skolem-p (head x))
		     (loop for x1 in (args x)
			   thereis (skolem-occurs-p x1 subst)))))

(defun disallowed-symbol-occurs-in-answer-p (x subst)
  (dereference
    x subst
    :if-constant (not (constant-allowed-in-answer x))
    :if-compound (or (not (function-allowed-in-answer (head x)))
		     (loop for x1 in (args x)
			   thereis (disallowed-symbol-occurs-in-answer-p x1 subst)))))

(defun embedding-variable-occurs-p (x subst)
  (dereference
    x subst
    :if-compound (loop for x1 in (args x)
		       thereis (embedding-variable-occurs-p x1 subst))
    :if-variable (embedding-variable-p x)))

;;; subst.lisp EOF
