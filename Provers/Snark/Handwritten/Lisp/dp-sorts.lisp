;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: dp-sorts.lisp
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

;;; notes:
;;; use *sort-theory* clause set to represent sort theory
;;; with top-sort=true, bottom-sort=false

;;(defconstant false 'false)
;;(defconstant true 'true)

(declaim (special *sort-theory* *input-sort-wff* *check-sorts-nontrivial*))

(defvar *dp-sort-intersections*)

(defun make-sort-theory-dp-clause-set ()
  (let ((clause-set (make-dp-clause-set)))
    (dp-insert '(true) clause-set)
    (dp-insert '((not false)) clause-set)
    (checkpoint-dp-clause-set clause-set)
    clause-set))

;;; dp-sorts.lisp maintains a checkpoint as of the last sort declaration so
;;; that it can repeatedly evaluate sort queries by inserting clauses, testing
;;; satisfiability, and restoring without extra checkpoint and uncheckpoint operations
;;; so, wrap an extra uncheckpoint and checkpoint around these checkpoint operations

(defun checkpoint-dp-sort-theory (clause-set)
  (uncheckpoint-dp-clause-set clause-set)
  (checkpoint-dp-clause-set clause-set)
  (checkpoint-dp-clause-set clause-set))

(defun restore-dp-sort-theory (clause-set)
  (uncheckpoint-dp-clause-set clause-set)
  (restore-dp-clause-set clause-set)
  (checkpoint-dp-clause-set clause-set))

(defun uncheckpoint-dp-sort-theory (clause-set)
  (uncheckpoint-dp-clause-set clause-set)
  (uncheckpoint-dp-clause-set clause-set)
  (checkpoint-dp-clause-set clause-set))

(defun dp-satisfiable-sort-theory-p (clause-set)
  (let ((dp-tracing nil)
        (dp-tracing-choices nil))
  (dp-satisfiable-p clause-set
		    :find-all-models nil
		    :print-summary nil
		    :print-warnings nil
		    :dependency-check nil
		    :pure-literal-check nil)))

(defun dp-subsort-p (x y)
  ;; returns true for both identical sorts and strict subsorts
  (let ((clause-set *sort-theory*))
    (dp-insert (list x) clause-set)
    (dp-insert (list `(not ,y)) clause-set)
    (prog1
      (not (dp-satisfiable-sort-theory-p clause-set))
      (restore-dp-clause-set clause-set))))

(defun dp-sort-disjoint-p (x y)
  (let ((clause-set *sort-theory*))
    (dp-insert (list x) clause-set)
    (dp-insert (list y) clause-set)
    (prog1
      (not (dp-satisfiable-sort-theory-p clause-set))
      (restore-dp-clause-set clause-set))))

(defun dp-sort-intersection (x y naming)
  (declare (ignore naming))
  (let ((clause-set *sort-theory*))
    (dp-insert (list x) clause-set)
    (dp-insert (list y) clause-set)
    (if (prog1
          (dp-satisfiable-sort-theory-p clause-set)
          (restore-dp-clause-set clause-set))      
        (dp-sort-intersection1 x y)
        false)))

(defun dp-sort-intersection1 (x y)
  (let* ((xx (or (copy-list (get x 'intersection-of-sorts)) (list x)))
         (yy (or (copy-list (get y 'intersection-or-sorts)) (list y)))
         (zz (delete-duplicates (sort (nconc xx yy) #'string<)))
         (sort (gethash zz *dp-sort-intersections*)))
    (unless sort
      (setq sort (make-symbol (format nil "~A~{&~A~}" (first zz) (rest zz))))
      (setf (gethash zz *dp-sort-intersections*) sort)
      (setf (get sort 'intersection-of-sorts) zz)
      (declare-sort sort :iff `(and ,@zz)))
    sort))

(defun dp-assert-subsort (x y)
  (let ((clause-set *sort-theory*)
        v)
    (cond
     ((dp-subsort-p x y)
      )
     (t
      (uncheckpoint-dp-clause-set clause-set)
      (dp-insert (list `(not ,x) y) clause-set)
      (checkpoint-dp-clause-set clause-set)))
    (cond
     ((and *check-sorts-nontrivial*
           (setq v (dp-check-sorts-nontrivial1 (list x y))))
      (error "Declaring ~A subsort of ~A forces ~A to be ~A in current sort theory."
             x y (car v) (cdr v)))
     (t
      t))))

(defun dp-assert-sort-disjoint (l)
  ;; every element of l is disjoint from every other element of l
  (let ((clause-set *sort-theory*)
        v)
    (dotails (l l)
      (let ((x (first l)))
        (dolist (y (rest l))
          (cond
           ((dp-sort-disjoint-p x y)
            )
           (t
	    (uncheckpoint-dp-clause-set clause-set)
            (dp-insert (list `(not ,x) `(not ,y)) clause-set)
            (checkpoint-dp-clause-set clause-set))))))
    (cond
     ((and *check-sorts-nontrivial*
           (setq v (dp-check-sorts-nontrivial1 l)))
      (error "Declaring ~{~A ~}disjoint forces ~A to be ~A in current sort theory."
             l (car v) (cdr v)))
     (t
      t))))

(defun dp-assert-sort-definition (wff)
  (let ((clause-set *sort-theory*)
        v)
    (uncheckpoint-dp-clause-set clause-set)
    (let ((*input-sort-wff* t))
      (dp-insert-wff wff clause-set))
    (checkpoint-dp-clause-set clause-set)
    (cond
     ((and *check-sorts-nontrivial*
           (setq v (dp-check-sorts-nontrivial1)))	; should add argument
      (error "Declaring ~A forces ~A to be ~A in current sort theory." wff (car v) (cdr v)))
     (t
      t))))

(defun dp-check-sorts-nontrivial ()
  (let ((v (dp-check-sorts-nontrivial1)))
    (when v
      (error "~A is ~A in current sort theory." (car v) (cdr v)))))

(defun dp-check-sorts-nontrivial1 (&optional l)
  (let ((clause-set *sort-theory*))
    (dolist (atom
	      (if l
		  (mapcar (lambda (x) (atom-named x clause-set)) l)
		  (dp-clause-set-atoms clause-set))
	     nil)
      (let ((sort-name (dp-atom-name atom)))
        (unless (or (eq true sort-name) (eq false sort-name))
          (when (prog2
                 (dp-insert (list sort-name) clause-set)
                 (not (dp-satisfiable-sort-theory-p clause-set))
                 (restore-dp-clause-set clause-set))
            (return (cons sort-name false)))
          (when (prog2
                 (dp-insert (list `(not ,sort-name)) clause-set)
                 (not (dp-satisfiable-sort-theory-p clause-set))
                 (restore-dp-clause-set clause-set))
            (return (cons sort-name true))))))))

(defun dp-print-sort-theory ()
  (dp-clauses (lambda (clause)
                (unless (or (equal '(true) clause)
                            (equal '((not false)) clause))
                  (let ((posatoms
                         (mapcan (lambda (x)
                                   (unless (negative-literal-p x)
                                     (list x)))
                                 clause))
                        (negatoms
                         (mapcan (lambda (x)
                                   (when (negative-literal-p x)
                                     (list (complementary-literal x))))
                                 clause)))
                    (cond
                     ((null posatoms)
                      (print (if (eql 2 (length negatoms))
                                 `(sort-disjoint
                                   ,(first negatoms)
                                   ,(second negatoms))
                                 `(not
                                   ,(if (null (rest negatoms))
                                        (first negatoms)
                                        `(intersection ,@negatoms))))))
                     (negatoms
                      (print
                       (if (null (rest negatoms))
                           (if (null (rest posatoms))
                               `(subsort
                                 ,(first negatoms)
                                 ,(first posatoms))
                               `(subsort
                                 ,(first negatoms)
                                 (union ,@posatoms)))
                           (if (null (rest posatoms))
                               `(subsort
                                 (intersection ,@negatoms)
                                 ,(first posatoms))
                               `(subsort
                                 (intersection ,@negatoms)
                                 (union ,@posatoms))))))
                     (t
                      (print
                       (if (null (rest posatoms))
                           (first posatoms)
                           `(union ,@posatoms))))))
                  (terpri)))
	      *sort-theory*))

;;; dp-sorts.lisp EOF
