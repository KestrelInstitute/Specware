;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: subsume-clause.lisp
;;; Copyright (c) 2002-2003 Mark E. Stickel
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

(defun clause-subsumes-p (clause1 clause2)
  ;; does clause1 subsume clause2?
  (clause-subsumes-p1
   (atoms-in-clause2 clause1)
   (atoms-in-clause2 clause2)
   (variables clause2 nil *frozen-variables*)))

(defun clause-subsumes-p1 (l1 l2 frozen-variables)
  (prog->
    (clause-subsumes1 l1 l2 frozen-variables ->* subst)
    (declare (ignore subst))
    (return-from prog-> t)))

(defun clause-subsumes1 (cc l1 l2 frozen-variables)
  ;; returns nil
  (cond
   ((null l1)					;clause1 is the empty clause
    (funcall cc nil)
    nil)
   ((null l2)					;clause2 is the empty clause
    nil)
   (t
    (with-clock-off clause-to-clause-subsumption-tests
      ;; should rearrange l1 before calling clause-subsumers
      (let ((subsumerss (clause-subsumers l1 l2 frozen-variables t)))
        ;; rearrange subsumerss to be in ascending order by length
        (let ((v (rest subsumerss)))
          (cond
           ((null v)
            )
           ((null (rest v))
            (let ((subsumers1 (first subsumerss)) (subsumers2 (first v)))
              (when (length< subsumers2 subsumers1)
                (setf (first subsumerss) subsumers2)
                (setf (first v) subsumers1))))
           (t
            (mapl (lambda (l) (setf (car l) (let ((x (car l))) (cons (length x) x)))) subsumerss)
            (setf subsumerss (sort subsumerss #'< :key #'car))
            (mapl (lambda (l) (setf (car l) (cdar l))) subsumerss))))
        (combine-subsumers2 cc nil subsumerss))))))

(defun clause-subsumers (l1 l2 *frozen-variables* &optional opt)
  (let ((subsumerss nil) subsumerss-last)
    (prog->
      (quote nil -> subst)
      (quote t -> *subsuming*)
      (dolist l1 ->* x)
      (second x -> polarity)
      (first x -> atom1)
      (quote nil -> subsumers)
      (quote nil -> subsumers-last)
      (prog->
        (dolist l2 ->* y)
        (when (eq polarity (second y))
          (first y -> atom2)
          (unify atom1 atom2 subst ->* subst*)
          (when (and opt (eq subst subst*))	;if there is an exact match, ignore other matches
            (setf subsumers (list subst*))
            (return-from prog->))
          (collect subst* subsumers)))
      ;; subsumers is the list of subsuming substitutions
      ;; by atom1 in clause1 of any atom2 in clause2
      (when opt
        (cond
         ((null subsumers)			;if there is no match for atom1, return nil
          (return-from clause-subsumers nil))
         ((null (rest subsumers))		;if there is just one match, use it as subst
          (setf subst (first subsumers)))))
      ;; subsumerss is a list of a list of subsuming substitutions
      ;; (one list of subsuming substitutions for each atom in clause1)
      (collect subsumers subsumerss))
    subsumerss))

(defun combine-subsumers2 (cc subst1 subsumerss)
;;returns nil
  (prog->
    (dolist (pop subsumerss) ->* subst2)
    (combine-subsumers subst1 subst2 -> subst)
    (unless (eq none subst)
      (if (null subsumerss)
          (funcall cc subst)
          (combine-subsumers2 cc subst subsumerss)))))

(defun combine-subsumers (subst1 subst2)
  (cond
   ((null subst1)
    subst2)
   ((or (null subst2) (eq subst1 subst2))
    subst1)
   (t
    (let ((subst subst2))
      (when (substitution-shorterp subst2 subst1)
        (setf subst2 subst1)
        (setf subst1 subst)
        (setf subst subst2))
      (prog->
        (map-substitution subst1 ->* var value1)
        (lookup-variable-in-substitution var subst2 -> value2)
        (cond
         ((eq none value2)
          (setf subst (bind-variable-to-term var value1 subst)))
         ((not (equal-p value1 value2))
          (return-from combine-subsumers none))))
      subst))))

(defun condenser (clause)
  ;; see FASTCONDENSE algorithm in
  ;; G. Gottlob and C. Fermueller
  ;; "Removing redundancy from a clause"
  ;; Artificial Intelligence (1993)
  (let ((atoms2 nil) atoms2-last (catoms nil) (ground t))
    (prog->
      (map-atoms-in-clause clause ->* atom polarity)
      (dereference atom nil :if-compound-appl (heada atom) -> head)
      (and head (variables atom) -> vars)
      (list atom polarity head vars -> x)
      (collect x atoms2)
      (when head
        (push x catoms)
        (when vars
          (setf ground nil))))
    ;; catoms contains all nonpropositional atoms
    ;; only nonground catoms might be removable by condensing
    (cond
     ((or ground (null (rest catoms)))
      clause)
     (t
      (let ((condensed nil) (atoms1 nil) (atoms2vars nil) atoms2*)
        (prog->
          (dotails catoms ->* l)
          (first l -> x)				;consider removing x
          (when (fourth x)				;must be nonground
            (first x -> atom)
            (second x -> polarity)
            (third x -> head)
            (when (and (dolist (y catoms)
                         (when (and (neq x y)		;must match another catom
                                    (eq head (third y))
                                    (eq polarity (second y))
                                    (not (member y condensed))
                                    (subsumes-p1 atom (first y) (fourth y)))
                           (return t)))
                       (clause-subsumes-p1
                        (or atoms1 (setf atoms1 (atoms-in-clause2 clause nil t)))	;renumbers
                        (setf atoms2* (remove x atoms2))
                        (or atoms2vars (setf atoms2vars (reduce 'union catoms :key #'fourth)))))
              (setf atoms2 atoms2*)
              (push x condensed))))
        (if condensed
            (atoms-to-clause2 atoms2)
            clause))))))

;;; subsume-clause.lisp EOF
