;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: nonhorn-magic-set.lisp
;;; Copyright (c) 2000-2002 Mark E. Stickel
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

(defun make-magic-goal-atom (atom)
  (flet ((magic-goal-name (name)
           (intern (concatenate 'string (symbol-name :goal-) (string name)) :snark-user)))
    (dereference
     atom nil
     :if-constant (let ((v (constant-magic atom)))
                    (if (or (null v) (eq 'goal v))
                        true
                        (if (eq t v)
                            (setf (constant-magic atom)
                                  (declare-proposition
                                   (magic-goal-name atom)
                                   :magic 'goal))
                            v)))
     :if-compound (let* ((head (head atom))
                         (v (function-magic head)))
                    (if (or (null v) (eq 'goal v))
                        true
                        (make-compound* (if (eq t v)
                                            (setf (function-magic head)
                                                  (declare-relation
                                                   (magic-goal-name (function-name head))
                                                   (function-arity head)
                                                   :magic 'goal))
                                            v)
                                        (args atom)))))))

(defun magic-transform-clause (cc clause &key (transform-negative-clauses t) (transform-positive-units nil))
  ;; {d} yields
  ;;   {d}              if transform-positive-units is false
  ;;   or
  ;;   {~goal_d, d}     if transform-positive-units is true
  ;; {d, e, f} yields
  ;;   {~goal_d, ~goal_e, ~goal_f, d, e, f}
  ;; {~a} yields
  ;;   {goal_a}         if transform-negative-clauses is true
  ;;   and
  ;;   {~a}
  ;; {~a, ~b, ~c} yields
  ;;   {goal_a}         if transform-negative-clauses is true
  ;;   and
  ;;   {~a, goal_b}     if transform-negative-clauses is true
  ;;   and
  ;;   {~a, ~b, goal_c} if transform-negative-clauses is true
  ;;   and
  ;;   {~a, ~b, ~c}
  ;; {~a, ~b, ~c, d, e, f} yields
  ;;   {~goal_d, ~goal_e, ~goal_f, goal_a}
  ;;   and
  ;;   {~goal_d, ~goal_e, ~goal_f, ~a, goal_b}
  ;;   and
  ;;   {~goal_d, ~goal_e, ~goal_f, ~a, ~b, goal_c}
  ;;   and
  ;;   {~goal_d, ~goal_e, ~goal_f, ~a, ~b, ~c, d, e, f}
  (let ((posatoms nil) posatoms-last
        (negatoms nil) negatoms-last)
    (prog->
      (map-atoms-in-clause clause ->* atom polarity)
      (if (eq :pos polarity) (collect atom posatoms) (collect atom negatoms)))
    (cl:assert (not (and (null posatoms) (null negatoms))))
    (let ((l nil) l-last)
      (dolist (atom posatoms)
        (collect (negate (make-magic-goal-atom atom)) l))
      (dolist (atom negatoms)
        (unless (and (null posatoms) (not transform-negative-clauses))
          (funcall cc (disjoin* (append l (list (make-magic-goal-atom atom))))))
        (collect (negate atom) l))
      (cond
       ((and (null negatoms) (null (rest posatoms)) (not transform-positive-units))
        (funcall cc (first posatoms)))
       (t
        (funcall cc (disjoin* (append l posatoms)))))))
  nil)

(defun magic-transform-wff (wff &key (transform-negative-clauses t) (transform-positive-units nil))
  ;; for use only if wff is a clause or conjunction of clauses
  ;; magic-transform-wff is idempotent
  (if (or (eq true wff) (eq false wff))
      wff
      (let ((clauses nil) clauses-last)
        (prog->
          (map-conjuncts wff ->* clause)
          (magic-transform-clause
           clause
           :transform-negative-clauses transform-negative-clauses
           :transform-positive-units transform-positive-units
           ->* clause)
          (collect clause clauses))
        (conjoin* clauses))))

(defun proposition-magic-goal-p (prop)
  (eq 'goal (constant-magic prop)))

(defun relation-magic-goal-p (rel)
  (eq 'goal (function-magic rel)))

(defun magic-goal-atom-p (atom)
  (dereference
   atom nil
   :if-constant (proposition-magic-goal-p atom)
   :if-compound (relation-magic-goal-p (head atom))))

(defun magic-goal-occurs-p (wff)
  (prog->
    (map-atoms-in-wff wff ->* atom polarity)
    (when (and (eq :pos polarity) (magic-goal-atom-p atom))
      (return-from prog-> t))))

;;; nonhorn-magic-set.lisp EOF
