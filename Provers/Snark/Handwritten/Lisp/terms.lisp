;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: terms.lisp
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

(defconstant none :none)			;special null value to use when NIL won't do
(defconstant false 'false)
(defconstant true 'true)
(defconstant bottom-sort false)
(defconstant top-sort true)

(defvar *cons*)
(defvar *=*)
(defvar *not*)
(defvar *and*)
(defvar *or*)
(defvar *implies*)
(defvar *implied-by*)
(defvar *iff*)
(defvar *xor*)
(defvar *if*)
(defvar *forall*)
(defvar *exists*)
(defvar *answer-if*)

(defstruct (compound-appl
            (:constructor make-compound-appl (head args &optional (vars (variablesl args)))))
  (head nil :read-only t)
  (args nil :read-only t)
  (number (nonce) :read-only t)
  (vars nil :read-only t))

(definline cons-function-symbol-p (fn)
  (eq *cons* fn))

(definline constant-p (x)
  (and (atom x) (not (compound-appl-p x))))

(definline variable-p (x)
  (and (consp x) (eq '%vari (carc x))))

(definline compound-p (x)
  (if (consp x) (neq '%vari (carc x)) (compound-appl-p x)))

(defun make-compound%2 (head arg1 arg2)
  (if (cons-function-symbol-p head)
      (cons arg1 arg2)
      (make-compound-appl head (list arg1 arg2))))

(defun make-compound%* (head args)
  (if (cons-function-symbol-p head)
      (cons (first args) (second args))
      (make-compound-appl head args)))

(defmacro make-compound (head &rest args)
  ;; e.g., (make-compound 'f 'a 'b 'c) = (f a b c)
  (case (length args)
    (0
     `(make-compound-appl ,head nil nil))
    (2
     `(make-compound%2 ,head ,@args))
    (otherwise
     `(make-compound-appl ,head (list ,@args)))))

(defmacro make-compound* (head &rest args)
  ;; e.g., (make-compound* 'f '(a b c)) = (make-compound* 'f 'a '(b c)) = (f a b c)
  `(make-compound%* ,head (list* ,@args)))

(definline argsa (appl)
  ;; only if appl is compound-appl, not compound-cons
  (compound-appl-args (the compound-appl appl)))

(definline arg1a (appl)
  ;; only if appl is compound-appl, not compound-cons
  (first (argsa appl)))

(definline arg2a (appl)
  ;; only if appl is compound-appl, not compound-cons
  (second (argsa appl)))

(definline args (compound)
  ;; note: (iff (neq (args compound) (args compound)) (eq *cons* (head compound)))
  (if (consp compound) (list (carc compound) (cdrc compound)) (argsa compound)))

(definline arg1 (compound)
  (if (consp compound) (carc compound) (arg1a compound)))

(definline arg2 (compound)
  (if (consp compound) (cdrc compound) (arg2a compound)))

(definline heada (appl)
  ;; only if appl is compound-appl, not compound-cons
  (compound-appl-head (the compound-appl appl)))

(definline head (compound)
  (if (consp compound) *cons* (heada compound)))

(defmacro fancy-make-compound (head &rest args)
  (let ((fn (gensym)))
    `(let ((,fn (function-make-compound-function ,head)))
       (if ,fn
	   (funcall ,fn ,@args)
	   (make-compound ,head ,@args)))))

(defmacro fancy-make-compound* (head &rest args)
  (let ((fn (gensym)))
    `(let ((,fn (function-make-compound*-function ,head)))
       (if ,fn
           ,(if (null (rest args))
                `(funcall ,fn ,(first args))
	        `(funcall ,fn (list* ,@args)))
	   (make-compound* ,head ,@args)))))

(defun make-compound2 (head args)
  ;; e.g., (make-compound2 'and '(a b c)) = (and a (and b c))
  ;; (cl:assert (<= 2 (length args)))
  (cond
    ((null (rest (rest args)))
     (make-compound* head args))
    (t
     (make-compound head (first args) (make-compound2 head (rest args))))))

(defmacro make-a1-compound* (head identity &rest args)
  (let ((x (gensym)))
    `(let ((,x (list* ,@args)))
       (cond
	 ((null ,x)
	  ,identity)
	 ((null (rest ,x))
	  (first ,x))
	 (t
	  (make-compound* ,head ,x))))))

(defmacro dereference (x subst &key
                         (if-variable nil)
                         (if-constant nil)
                         (if-compound nil if-compound-supplied)	;3 disjoint types of compound
                         (if-compound-cons nil if-compound-cons-supplied)
                         (if-compound-appl nil if-compound-appl-supplied)
                         (if-compound-ground nil if-compound-ground-supplied)
                         (if-compound-nonground nil if-compound-nonground-supplied))
  ;; dereferences x leaving result in x
  (cl:assert (symbolp x))
  (cl:assert (symbolp subst))
  (cl:assert (implies if-compound-supplied
                      (and (not if-compound-cons-supplied)
                           (not if-compound-appl-supplied)
                           (not if-compound-ground-supplied)
                           (not if-compound-nonground-supplied))))
  (cl:assert (implies if-compound-appl-supplied
                      (and (not if-compound-ground-supplied)
                           (not if-compound-nonground-supplied))))
  (flet ((make-dispatch-code (x if-variable if-constant if-compound
                                if-compound-cons if-compound-appl
                                if-compound-ground if-compound-nonground)
       (cond
        ((or if-compound-ground-supplied
             if-compound-nonground-supplied)
         `(if (consp ,x)
              ,(if (or if-variable if-compound-cons)
                   `(if (eq '%vari (carc ,x))
                        ,if-variable
                        ,if-compound-cons)
                   nil)
              (if (compound-appl-p ,x)
                  (if (null (compound-appl-vars ,x))
                      ,if-compound-ground
                      ,if-compound-nonground)
                  ,if-constant)))
        ((or if-compound-cons-supplied
             if-compound-appl-supplied)
         `(if (consp ,x)
              ,(if (or if-variable if-compound-cons)
                   `(if (eq '%vari (carc ,x))
                        ,if-variable
                        ,if-compound-cons)
                   nil)
              ,(if (or if-constant if-compound-appl)
                   `(if (compound-appl-p ,x)
                        ,if-compound-appl
                        ,if-constant)
                   nil)))
        ((or if-variable
             if-compound)
         `(if (and (consp ,x) (eq '%vari (carc ,x)))
              ,if-variable
              (if (or (consp ,x) (compound-appl-p ,x))
                  ,if-compound
                  ,if-constant)))
        (if-constant
         `(if (consp ,x)
              nil
              (if (compound-appl-p ,x)
                  nil
                  ,if-constant)))
        (t
         nil)))
     (make-lookup-variable-code (x subst if-bound if-unbound)
       ;; substitution is alternating list of variables and values
       (let ((bindings (gensym))
	     (check-binding (gensym)))
	 `(let ((,bindings ,subst))
	    (tagbody
	      ,check-binding
	      (cond
               ((null ,bindings)
                ,if-unbound)
               ((eq ,x (carc ,bindings))
                (setq ,x (cadrcc ,bindings))
                ,if-bound)
               (t
                (setq ,bindings (cddrcc ,bindings))
                (go ,check-binding))))))))
    (if (null subst)
	(make-dispatch-code
         x if-variable if-constant if-compound
         if-compound-cons if-compound-appl
         if-compound-ground if-compound-nonground)
	(let ((dereference (gensym))
	      (repeat (gensym)))
	  `(block ,dereference
	     (tagbody
	       ,repeat
	       ,(make-dispatch-code
                 x
                 (make-lookup-variable-code
                  x subst
                  `(go ,repeat)
                  `(return-from ,dereference ,if-variable))
                 `(return-from ,dereference ,if-constant)
                 `(return-from ,dereference ,if-compound)
                 `(return-from ,dereference ,if-compound-cons)
                 `(return-from ,dereference ,if-compound-appl)
                 `(return-from ,dereference ,if-compound-ground)
                 `(return-from ,dereference ,if-compound-nonground))))))))

(defmacro match-term (term1 term2 subst &key
		      if-constant*constant if-constant*compound if-constant*variable
		      if-compound*constant if-compound*compound if-compound*variable
		      if-variable*constant if-variable*compound if-variable*variable)
  (let ((s (gensym)))
    `(let ((,s ,subst))
       (dereference
	 ,term1 ,s
	 :if-constant (dereference
			,term2 ,s
			:if-constant ,if-constant*constant
			:if-compound ,if-constant*compound
			:if-variable ,if-constant*variable)
	 :if-compound (dereference
			,term2 ,s
			:if-constant ,if-compound*constant
			:if-compound ,if-compound*compound
			:if-variable ,if-compound*variable)
	 :if-variable (dereference
			,term2 ,s
			:if-constant ,if-variable*constant
			:if-compound ,if-variable*compound
			:if-variable ,if-variable*variable)))))

(defmacro prefer-to-bind-p (var2 var1)
  (declare (ignore var2 var1))
  nil)

(defvar *frozen-variables* nil)			;list of variables not allowed to be instantiated

(definline variable-frozen-p (var)
  (let ((l *frozen-variables*))
    (and l (member var l :test #'eq))))

(definline unfrozen-variable-p (x)
  (and (variable-p x)
       (not (variable-frozen-p x))))

(definline make-tc (term count)
  ;; make term and count pair for count-arguments
  (cons term count))

(definline tc-term (x)
  ;; term part of term and count pair created by count-arguments
  ;; term and count pair is represented as (term . count)
  (carc x))

(defmacro tc-count (x)
  ;; count part of term and count pair created by count-arguments
  ;; term and count pair is represented as (term . count)
  `(the fixnum (cdrc ,x)))

;;; terms.lisp EOF
