;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: subsume.lisp
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

(declaim
  (special
    *false-rows*
    *constraint-rows*))

(defvar *subsuming* nil)

(defun subsume (cc x y &optional subst)
  (prog->
    (identity *subsuming* -> sb)
    (quote t -> *subsuming*)
    (identity *frozen-variables* -> fv)		;save list of frozen variables
    (variables y subst fv -> *frozen-variables*)	;add y's variables to frozen variables
    (unify x y subst ->* subst)
    (identity sb -> *subsuming*)
    (identity fv -> *frozen-variables*)		;restore list of frozen variables
    (funcall cc subst)))

(defun subsumes-p (x y &optional subst)
  ;; x subsumes y?
  (subsumes-p1 x y (variables y subst *frozen-variables*) subst))

(defun subsumes-p1 (x y *frozen-variables* &optional subst)
  (let ((*subsuming* t))
    (unify-p x y subst)))

(defun subsumed-p (x y &optional subst)
  ;; x is subsumed by y?
  (subsumed-p1 x y (variables x subst *frozen-variables*) subst))

(defun subsumed-p1 (x y *frozen-variables* &optional subst)
  (let ((*subsuming* t))
    (unify-p y x subst)))

(defun subsumers (x y &optional subst)
  (subsumers1 x y (variables y subst *frozen-variables*) subst))

(defun subsumers1 (x y *frozen-variables* &optional subst)
  (let ((*subsuming* t))
    (unifiers x y subst)))

;;; use-subsumption = nil		don't use subsumption
;;; use-subsumption = :forward		use only forward subsumption
;;; use-subsumption = t			use forward and backward subsumption
;;;
;;; use-subsumption-by-false further specifies the behavior of use-subsumption in the case of
;;; "false rows" (those for which row-wff is false, kept in *false-rows* and *constraint-rows*)
;;;
;;; use-subsumption-by-false = nil	don't use subsumption
;;; use-subsumption-by-false = :false   use only forward subsumption on other false rows
;;; use-subsumption-by-false = :forward	use just forward subsumption generally
;;; use-subsumption-by-false = t	use forward and backward subsumption

;;; uses subsumption-mark, subsumption-matches fields of row
;;; uses containing-wffs property on term-memory records for literals

(defvar clause-subsumption t)

(defvar subsumption-mark)

(defun forward-subsumed (row)
  (prog->
    (forward-subsumption row ->* subsuming-row)
    (declare (ignore subsuming-row))
    (return-from forward-subsumed t))
  nil)

(defun forward-subsumption (cc row)
  (with-clock-on forward-subsumption
    (prog->
      (row-present-in-context-p row ->nonnil row-context)
      (flet ((FSUBSUME (row2 test)
               (prog->
                 (row-present-in-context-p row2 ->nonnil row2-context)
		 (context-subsumption-p row2-context row-context ->nonnil new-row-context)
                 (cond
                  ((eq t new-row-context)
                   (when (implies test (wff-subsumption nil row2 row))
                     (funcall cc row2)))
                  (t
                   (when (implies test (wff-subsumption nil row2 row))
		     (setf (row-context row) (setf row-context new-row-context))))))))
        (prog->
          (row-wff row -> wff)
          (when (let ((u (use-subsumption-by-false?))) (if (eq :false u) (eq false wff) u))
            (prog->
              (map-rows :rowset *false-rows* :reverse t ->* row2)
              (fsubsume row2 t))
            (prog->
              (map-rows :rowset *constraint-rows* :reverse t ->* row2)
              (fsubsume row2 t)))
          (cond
           ((eq false wff)
            )
           ((and clause-subsumption (or (clause-p wff) (setq clause-subsumption nil)))
            (forward-clause-subsumption row wff ->* row2)
            (fsubsume row2 nil))
           (t
            (forward-or-backward-wff-subsumption wff :pos :only nil (incf subsumption-mark) nil row ->* row2)
            (fsubsume row2 nil))))))))

(defun backward-subsumption (cc row)
  (with-clock-on backward-subsumption
    (prog->
      (row-present-in-context-p row ->nonnil row-context)
      (flet ((BSUBSUME (row2 test)
               (prog->
                 (row-present-in-context-p row2 ->nonnil row2-context)
		 (context-subsumption-p row-context row2-context ->nonnil new-row2-context)
                 (cond
                  ((eq t new-row2-context)
                   (when (implies test (wff-subsumption nil row row2))
                     (funcall cc row2)))
                  (t
                   (when (implies test (wff-subsumption nil row row2))
                     (setf (row-context row2) new-row2-context)))))))
        (prog->
          (row-wff row -> wff)
          (cond
           ((eq false wff)
            (when (let ((u (use-subsumption-by-false?))) (and u (neq :forward u) (neq :false u)))
              (map-rows :reverse t ->* row2)
              (bsubsume row2 t)))
           ((and clause-subsumption (or (clause-p wff) (setq clause-subsumption nil)))
            (backward-clause-subsumption row wff ->* row2)
            (bsubsume row2 nil))
           (t
            (forward-or-backward-wff-subsumption wff :pos :only nil (incf subsumption-mark) t row ->* row2)
            (bsubsume row2 nil))))))))

(defun forward-clause-subsumption (cc row2 clause)
  ;; applies fun to each stored clause that subsumes this clause
  ;; candidate subsuming clauses are the union of sets of clauses
  ;; that have generalizations of literals in this clause
  (do ((w (atoms-in-wff2 clause) (rest w))
       (candidate-subsuming-clauses nil)
       (mark (incf subsumption-mark))
       atom atompolarity)
      ((null w)
       (dolist (row candidate-subsuming-clauses)	;candidate subsuming clauses contains no duplicates
	 (when (and (LET ((N 0))		;INEFFICIENT
		      (MAP-ATOMS-IN-CLAUSE (LAMBDA (ATOM POLARITY)
                                             (DECLARE (IGNORE ATOM POLARITY))
                                             (INCF N))
					   (ROW-WFF ROW))
		      (= N (LENGTH (ROW-SUBSUMPTION-MATCHES ROW))))
		    (if (use-dp-subsumption?)
			(dp-subsume+ row row2)
			(clause-subsumption row row2)))
	   (funcall cc row))))
    (setf atom (first (first w)))
    (setf atompolarity (second (first w)))
    (prog->
      (retrieve-generalization-terms
	atom
	nil
	(ecase atompolarity
	  (:pos
	    #'tme-rows-containing-atom-positively)
	  (:neg
	    #'tme-rows-containing-atom-negatively))
	->* atom2 rows)
      (map-rows :rowset rows :reverse t ->* row)
      (cond
	((eql (row-subsumption-mark row) mark)
	 (let ((v (assoc atom2 (row-subsumption-matches row))))
	   (cond
	     (v
	      (push atom (cdr v)))
	     (t
	      (push (list atom2 atom) (row-subsumption-matches row))))))
	(t
	 (setf (row-subsumption-mark row) mark)
	 (setf (row-subsumption-matches row) (list (list atom2 atom)))
	 (push row candidate-subsuming-clauses))))))

(defun backward-clause-subsumption (cc row2 clause)
  ;; applies fun to each stored clause that this clause subsumes
  ;; candidate subsumed clauses are the intersection of sets of clauses
  ;; that have instances of literals in this clause
  (do ((w (atoms-in-wff2 clause) (rest w))
       (candidate-subsumed-clauses nil)		;might have duplicates
       (old-mark none new-mark)		;used to identify wffs involved in this subsumption operation
       (new-mark (incf subsumption-mark) (incf subsumption-mark))
       (first-atom t nil)
       atom atompolarity)
      ((null w)
       (dolist (row candidate-subsumed-clauses)	;candidate-subsumed-clauses may contain duplicates
	 (when (row-subsumption-mark row)
	   (setf (row-subsumption-mark row) nil)	;don't process duplicates
	   (when (if (use-dp-subsumption?)
		     (dp-subsume+ row2 row)
		     (clause-subsumption row2 row))
	     (funcall cc row)))))
    (setf atom (first (first w)))
    (setf atompolarity (second (first w)))
    (prog->
      (retrieve-instance-terms
	atom
	nil
	(ecase atompolarity
	  (:pos
	    #'tme-rows-containing-atom-positively)
	  (:neg
	    #'tme-rows-containing-atom-negatively))
	->* atom2 rows)
      (map-rows :rowset rows :reverse t ->* row)
      (cond
	((eql (row-subsumption-mark row) old-mark)	;matches exist for all preceding literals, but not this one yet
	 (setf (row-subsumption-mark row) new-mark)
	 (push (list atom atom2) (row-subsumption-matches row))
	 (when (null (rest w))			;this is last atom to be matched
	   (push row candidate-subsumed-clauses)))
	((eql (row-subsumption-mark row) new-mark)	;matches exist for all preceding literals and this one
	 (push atom2 (cdr (assoc atom (row-subsumption-matches row))))
	 (when (null (rest w))			;this is last atom to be matched
	   (push row candidate-subsumed-clauses)))
	(first-atom
	 (setf (row-subsumption-mark row) new-mark)
	 (setf (row-subsumption-matches row) (list (list atom atom2)))
	 (when (null (rest w))			;this is last atom to be matched
	   (push row candidate-subsumed-clauses)))))))

(defun clause-subsumption (subsuming-row subsumed-row)
  (catch 'subsumed
    (prog->
      (row-constraints subsuming-row -> subsuming-constraint-alist)
      (row-constraints subsumed-row  -> subsumed-constraint-alist)
      (if (use-answers-during-subsumption?) (row-answer subsuming-row) false -> subsuming-answer)
      (if (use-answers-during-subsumption?) (row-answer subsumed-row) false -> subsumed-answer)
      
      (quote t -> *subsuming*)
      (row-variables subsumed-row *frozen-variables* -> *frozen-variables*)
      
      (atoms-in-clause2 (row-wff subsuming-row) -> l1)
      (atoms-in-clause2 (row-wff subsumed-row) -> l2)
      (unless (list-shorterp l2 l1)		;don't allow a clause to subsume its factors
        (clause-subsumes1 l1 l2 *frozen-variables* ->* subst)
        (unify subsuming-answer subsumed-answer subst ->* subst)
        (cond
         #+ignore
	 ((use-constraint-solver-in-subsumption?)
	  (when (eq false
		    (funcall (constraint-simplification-function?)
			     (conjoin subsuming-constraint (negate subsumed-constraint subst) subst)))
	    (throw 'subsumed t)))
	 (t
	  (dp-subsume-constraint-alists* subsuming-constraint-alist subsumed-constraint-alist subst ->* subst)
	  (declare (ignore subst))
	  (throw 'subsumed t))))
      nil)))

(defun forward-or-backward-wff-subsumption (cc subwff polarity phase old-mark new-mark backward-p row)
  (dereference
    subwff nil
    :if-variable (error "Can't use variable wff in subsumption.")
    :if-constant (cond
		   ((or (eq true subwff) (eq false subwff))
		    (error "Can't use truth values in subsumption."))
		   (t
		    (forward-or-backward-atom-subsumption cc subwff polarity phase old-mark new-mark backward-p row)))
    :if-compound (let* ((head (head subwff))
			(kind (function-logical-symbol-p head))
			(args (args subwff)))
		   (when (and kind (null args))
		     (error "Can't use connectives with no arguments in subsumption."))
		   (ecase kind
		     (not
		       (forward-or-backward-wff-subsumption
			 cc (first args) (opposite-polarity polarity) phase old-mark new-mark backward-p row))
		     ((and or)
		      (cond
			((if backward-p (eq 'or kind) (eq 'and kind))
			 (do ((args args (rest args))
			      (first t nil)
			      (m old-mark)
			      n)
			     ((null (rest args))
			      (forward-or-backward-wff-subsumption
				cc (first args) polarity
				(ecase phase
				  (:only (if first :only :last))
				  (:first (if first :first :middle))
				  (:middle :middle)
				  (:last :last))
				m new-mark
				backward-p row))
			   (setq n (incf subsumption-mark))
			   (forward-or-backward-wff-subsumption
			     cc (first args) polarity
			     (ecase phase
			       (:only (if first :first :middle))
			       (:first (if first :first :middle))
			       (:middle :middle)
			       (:last :middle))
			     m n
			     backward-p row)
			   (setq m n)))
			(t
			 (do ((args args (rest args)))
			     ((null args))
			   (forward-or-backward-wff-subsumption
			     cc
			     (first args) polarity phase old-mark new-mark
			     backward-p row)))))
		     (implies
		       (forward-or-backward-wff-subsumption
			 cc
			 (make-compound *or*
					   (make-compound *not* (first args))
					   (second args))
			 polarity phase old-mark new-mark
			 backward-p row))
		     (implied-by
		       (forward-or-backward-wff-subsumption
			 cc
			 (make-compound *or*
					   (make-compound *not* (second args))
					   (first args))
			 polarity phase old-mark new-mark
			 backward-p row))
		     ((iff xor)			;should be more efficient
		      (cond
			((null (rest args))
			 (forward-or-backward-wff-subsumption
			   cc (first args) polarity phase old-mark new-mark backward-p row))
			(t
			 (let ((x (first args))
			       (y (if (null (cddr args)) (second args) (make-compound head (rest args)))))
			   (forward-or-backward-wff-subsumption
			     cc
			     (if (eq 'iff kind)
				 (make-compound *or*
						   (make-compound *and*
								     x
								     y)
						   (make-compound *and*
								     (make-compound *not* x)
								     (make-compound *not* y)))
				 (make-compound *or*
						   (make-compound *and*
								     x
								     (make-compound *not* y))
						   (make-compound *and*
								     (make-compound *not* x)
								     y)))
			     polarity phase old-mark new-mark
			     backward-p row)))))
		     (if			;should be more efficient
		       (forward-or-backward-wff-subsumption
			 cc
			 (make-compound *and*
					   (make-compound *or*
							     (make-compound *not* (first args))
							     (second args))
					   (make-compound *and*
							     (first args)
							     (third args)))
			 polarity phase old-mark new-mark
			 backward-p row))
		     ((nil)
		      (forward-or-backward-atom-subsumption
			cc subwff polarity phase old-mark new-mark backward-p row))))))

(defun forward-or-backward-atom-subsumption (cc atom polarity phase old-mark new-mark backward-p row)
  (funcall (if backward-p #'retrieve-instance-entries #'retrieve-generalization-entries)
	   (lambda (e row2s)
             (declare (ignore e))
             (prog->
               (dolist row2s ->* row2)
               (ecase phase
                 (:only
                  (when (if backward-p
                            (if (use-dp-subsumption?)
                                (dp-subsume+ row row2)
                                (wff-subsumption nil row row2))
                            (if (use-dp-subsumption?)
                                (dp-subsume+ row2 row)
                                (wff-subsumption nil row2 row)))
                    (funcall cc row2)))
                 (:first
                  (setf (row-subsumption-mark row2) new-mark))
                 (:middle
                  (when (eql (row-subsumption-mark row2) old-mark)
                    (setf (row-subsumption-mark row2) new-mark)))
                 (:last
                  (when (eql (row-subsumption-mark row2) old-mark)
                    (when (if backward-p
                              (if (use-dp-subsumption?)
                                  (dp-subsume+ row row2)
                                  (wff-subsumption nil row row2))
                              (if (use-dp-subsumption?)
                                  (dp-subsume+ row2 row)
                                  (wff-subsumption nil row2 row)))
                      (funcall cc row2)))))))
	   atom
	   nil
	   (if (eq polarity :pos)
	       #'tme-rows-containing-atom-positively
	       #'tme-rows-containing-atom-negatively)))

(defun wff-subsumption (matches subsuming-row subsumed-row)
  (declare (ignore matches))
  (catch 'subsumed
    (prog->
      (row-wff subsuming-row -> subsuming-wff)
      (row-wff subsumed-row  -> subsumed-wff)
      (row-constraints subsuming-row -> subsuming-constraint-alist)
      (row-constraints subsumed-row  -> subsumed-constraint-alist)
      (if (use-answers-during-subsumption?) (row-answer subsuming-row) false -> subsuming-answer)
      (if (use-answers-during-subsumption?) (row-answer subsumed-row) false -> subsumed-answer)

      (quote t -> *subsuming*)
      (row-variables subsumed-row *frozen-variables* -> *frozen-variables*)

      (quote nil -> subst)
      (wff-subsumption* subsuming-wff subsumed-wff subst ->* subst)
      (unify subsuming-answer subsumed-answer subst ->* subst)
      (cond
       #+ignore
	((use-constraint-solver-in-subsumption?)
	 (when (eq false
		   (funcall (constraint-simplification-function?)
			    (conjoin subsuming-constraint (negate subsumed-constraint subst) subst)))
	   (throw 'subsumed t)))
	(t
	 (dp-subsume-constraint-alists* subsuming-constraint-alist subsumed-constraint-alist subst ->* subst)
;;       (wff-subsumption* subsuming-wff subsumed-wff subst ->* subst)
	 (declare (ignore subst))
	 (throw 'subsumed t))))))

(defun wff-subsumption* (cc subsuming-wff subsumed-wff subst)
  ;; assume variables of subsumed-wff are already frozen so that
  ;; unification really does subsumption
  (let (interpretations)
    ;; find every interpretation in which subsuming-wff is true and subsumed-wff is false
    #|
    (salsify t subsuming-wff nil
	     (lambda (interp1)
		 (salsify nil subsumed-wff interp1
			  (lambda (interp2)
			      (push (cons interp1 (ldiff interp2 interp1)) interpretations)))))
    |#
    (let (u v)
      (salsify t subsuming-wff nil (lambda (interp1) (push interp1 u)))
      (salsify nil subsumed-wff nil (lambda (interp2) (push interp2 v)))
      (dolist (interp1 u)
	(dolist (interp2 v)
	  (push (cons interp1 interp2) interpretations))))
    (LET (W)
      (DOLIST (INTERP INTERPRETATIONS)
	(LET ((N (NMATCHES INTERP subst)))
	  (WHEN (= N 0)
	    (RETURN-FROM WFF-SUBSUMPTION* NIL))
	  (PUSH (CONS N INTERP) W)))
      (SETQ W (SORT W #'< :KEY #'CAR))
      (SETQ INTERPRETATIONS NIL)
      (DOLIST (X W)
	(PUSH (CDR X) INTERPRETATIONS)))
    (wff-subsumption*1 cc interpretations subst)))

(defun wff-subsumption*1 (cc interpretations subst)
  (cond
    ((null interpretations)
     (funcall cc subst))
    (t
     (do ((x (caar interpretations) (cdr x)))
	 ((null x))
       (do ((y (cdar interpretations) (cdr y)))
	   ((null y))
	 (unless (eq (cdar x) (cdar y))
	   (when (equal-p (caar x) (caar y) subst)
	     (wff-subsumption*1 cc (cdr interpretations) subst)
	     (return-from wff-subsumption*1 nil)))))
     (do ((x (caar interpretations) (cdr x)))
	 ((null x))
       (do ((y (cdar interpretations) (cdr y)))
	   ((null y))
	 (unless (eq (cdar x) (cdar y))
	   (prog->
	     (unify (caar x) (caar y) subst ->* subst)
	     (wff-subsumption*1 cc (cdr interpretations) subst))))))))

(defun nmatches (interpretation subst)
  (do ((x (car interpretation) (cdr x))
       (n 0))
      ((null x) n)
    (do ((y (cdr interpretation) (cdr y)))
	((null y))
      (unless (eq (cdar x) (cdar y))
	(when (unify-p (caar x) (caar y) subst)
	  (incf n))))))

(defun list-shorterp (l1 l2)
  (loop
    (cond
     ((null l1)
      (return (not (null l2))))
     ((null l2)
      (return nil))
     (t
      (setf l1 (cdr l1))
      (setf l2 (cdr l2))))))

;;; wff-subsumption* allows wffs to subsume their own factors

;;; when subsuming one atom in an interpretation by
;;; another, make sure one is from the subsuming wff
;;; and the other is from the subsumed wff???
;;; split these lists to do M*N comparisons
;;; instead of (M+N)*(M+N)

;;; subsume.lisp EOF
