;;; -*- Mode: LISP; Syntax: Common-Lisp -*-
;;; File: davis-putnam3.lisp
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

#-snark (in-package #-(or clicc gcl) :common-lisp-user #+(or clicc gcl) :user)
#+snark (in-package :snark)
(eval-when (:compile-toplevel :load-toplevel)
  (export '(dp-prover dp-version
	    dp-tracing dp-tracing-state dp-tracing-models dp-tracing-choices
	    dp-satisfiable-p dp-satisfiable-file-p make-dp-clause-set
	    dp-insert dp-insert-sorted dp-insert-wff dp-insert-file
	    dp-count dp-clauses dp-output-clauses-to-file wff-clauses
	    dp-horn-clause-set-p
            checkpoint-dp-clause-set restore-dp-clause-set uncheckpoint-dp-clause-set
	    choose-an-atom-of-a-shortest-positive-clause
	    choose-an-atom-of-a-shortest-positive-clause-randomly
	    choose-an-atom-of-a-shortest-positive-clause-with-most-occurrences
	    choose-an-atom-of-a-shortest-positive-clause-with-most-occurrences-randomly
	    lookahead-true lookahead-false
	    lookahead-true-false lookahead-false-true)))

(defparameter dp-prover :|LDPP'|)		;the name of this prover
(defparameter dp-version "3.437")		;its version number

;;;                        LDPP'
;;;
;;;     Satisfiability Testing by the Davis-Putnam Procedure
;;; Using List Representation for a Set of Propositional Clauses
;;;                         by
;;;                  Mark E. Stickel
;;;           Artificial Intelligence Center
;;;                 SRI International
;;;            Menlo Park, California 94025
;;;                (stickel@ai.sri.com)
;;;
;;; LDPP' is a fairly fast implementation of the Davis-Putnam procedure,
;;; but still has several deficiencies.  There is
;;;   no checking that a negative clause exists
;;;   no intelligent literal selection criteria
;;;   no looking for symmetry
;;;
;;;
;;; Some information about LDPP' and related systems can be found in
;;; H. Zhang and M.E. Stickel.  Implementing the Davis-Putnam algorithm by tries.
;;; Technical Report, Computer Science Department, The University of Iowa,
;;; Iowa City, Iowa, August 1994.
;;; obtainable by FTP from ftp.cs.uiowa.edu: /pub/hzhang/sato/papers/davis.dvi.Z
;;;
;;;
;;; Usage:
;;; A set of clauses can be created incrementally by
;;;  (setq clause-set (make-dp-clause-set))
;;; followed by calls
;;;  (dp-insert clause clause-set) or
;;;  (dp-insert-wff wff clause-set).
;;; A set of clauses can be tested for satisfiability by
;;;  (dp-satisfiable-p clause-set {options}*).
;;; A set of clauses or wffs in a file can be tested by
;;;  (dp-satisfiable-file-p filename {options}*).
;;; See examples at the end of this file.
;;;
;;;
;;; LDPP' is an implementation of the Davis-Putnam procedure without logical
;;; refinements.  It is efficient because of the way it performs the crucial
;;; truth-value assignment operation.  LDPP' uses reversible destructive list
;;; operations, similarly to Crawford and Auton's TABLEAU, Letz's SEMPROP,
;;; Zhang's SATO, and McCune's MACE theorem provers.
;;; 
;;; In LDPP', a set of clauses is represented by a list of structures for
;;; clauses and a list of structures for atomic formulas.  The structure for
;;; a clause contains the fields:
;;; 
;;; * POSITIVE-LITERALS, NEGATIVE-LITERALS:  List of pointers to structures
;;;   for atomic formulas occurring positively (resp., negatively) in this
;;;   clause.
;;; 
;;; * NUMBER-OF-UNRESOLVED-POSITIVE-LITERALS, NUMBER-OF-UNRESOLVED-NEGATIVE-LITERALS:
;;;   This is the number of atomic formulas in POSITIVE-LITERALS
;;;   (resp., NEGATIVE-LITERALS) that have not been resolved away.
;;;   They may have been assigned the opposite truth-value and the clause
;;;   is really subsumed.
;;; 
;;; The structure for an atomic formula contains the fields:
;;; 
;;; * VALUE: This is TRUE if the atomic formula has been assigned the value
;;;   true, FALSE if it has been assigned false, and NIL if no value has been
;;;   assigned.
;;; 
;;; * CONTAINED-POSITIVELY-CLAUSES, CONTAINED-NEGATIVELY-CLAUSES:  List of
;;;   pointers to structures for clauses that contain this atomic formula
;;;   positively (resp., negatively).
;;; 
;;; To assign true to an atomic formula:
;;; 
;;; * Its VALUE field is set to TRUE.
;;; 
;;; * Every clause in CONTAINED-NEGATIVELY-CLAUSES has its
;;;   NUMBER-OF-UNRESOLVED-NEGATIVE-LITERALS field decremented by one.
;;;   Note that we don't modify NEGATIVE-LITERALS itself.
;;;   If the sum of NUMBER-OF-UNRESOLVED-NEGATIVE-LITERALS
;;;   and NUMBER-OF-UNRESOLVED-POSITIVE-LITERALS is zero, the current truth
;;;   assignment yields the unsatisfiable empty clause.  If the sum is one, a
;;;   new unit clause has been produced.  The newly derived unit clause can be
;;;   identified by finding the only atom in POSITIVE-LITERALS or
;;;   NEGATIVE-LITERALS whose VALUE is NIL.  These are queued and assigned
;;;   values before assign exits so that all unit propagation is done inside
;;;   the assign procedure.
;;; 
;;; To undo an assignment of true to an atomic formula and thus restore
;;; the set of clauses to their state before the assignment so alternative
;;; assignments can be tested:
;;; 
;;; * The VALUE field for the atomic formula is set to NIL.
;;; 
;;; * Every clause in CONTAINED-NEGATIVELY-CLAUSES has its
;;;   NUMBER-OF-UNRESOLVED-NEGATIVE-LITERALS field incremented by one.
;;; 
;;; Assignment of false to an atomic formula is done analogously.



#+(and (not snark) (not (or lucid symbolics gcl)))
(declaim (optimize (compilation-speed 0) (speed 3) (safety 0) (debug 0)))
#+(AND (NOT SNARK) (OR LUCID SYMBOLICS GCL))
(eval-when (compile load eval)
  (proclaim '(optimize (compilation-speed 0) (speed 3) (safety 0))))



#-snark
(defmacro collect (item place)
  ;; like (setf place (nconc place (list item)))
  ;; except last cell of list is remembered in place-last
  ;; so that operation is O(1)
  ;; collect can be used instead of (push item place) + (nreverse place) loop idiom
  ;; user must declare place-last variable or slot
  (let* ((args (if (atom place) nil (mapcar (lambda (arg) (list (gensym) arg)) (rest place))))
         (place (if (atom place) place (cons (first place) (mapcar #'first args))))
         (place-last (if (atom place)
                         (intern (concatenate 'string (symbol-name place) "-LAST"))
                         (cons (intern (concatenate 'string (symbol-name (first place)) "-LAST"))
                               (rest place))))
         (v (gensym))
         (l (gensym)))
    `(let* ((,v (cons ,item nil)) ,@args (,l ,place))
       (cond
        ((null ,l)
         (setf ,place (setf ,place-last ,v)))
        (t
         (rplacd ,place-last (setf ,place-last ,v))
         ,l)))))

#-snark
(defmacro ncollect (list place)
  ;; like (setf place (nconc place list))
  ;; except last cell of list is remembered in place-last
  (let* ((args (if (atom place) nil (mapcar (lambda (arg) (list (gensym) arg)) (rest place))))
         (place (if (atom place) place (cons (first place) (mapcar #'first args))))
         (place-last (if (atom place)
                         (intern (concatenate 'string (symbol-name place) "-LAST"))
                         (cons (intern (concatenate 'string (symbol-name (first place)) "-LAST"))
                               (rest place))))
         (v (gensym))
         (l (gensym)))
    `(let* ((,v ,list) ,@args (,l ,place))
       (cond
        ((null ,v)
         ,l)
        ((null ,l)
	 (setf ,place-last (last ,v))
         (setf ,place ,v))
        (t
         (rplacd ,place-last ,v)
	 (setf ,place-last (last ,v))
         ,l)))))



(defvar dp-tracing 10000)			;prints trace information
(defvar dp-tracing-state 10)			;prints current choice points
						;once every 10000*10 branches
(defvar dp-tracing-models nil)			;prints models found
(defvar dp-tracing-choices 2)			;print values of split atoms
						; to this depth of splitting
						; beyond shallowest backtrack
;;; When dp-tracing is the number N, branch number is printed once for each
;;; N branches.
;;; When dp-tracing = T, dp-tracing enables the following:
;;;  print number of branches each time a branch is added
;;;  print Succeed(M/N) when terminating a success branch
;;;  print Fail(M/N) when terminating a failure branch
;;; where M is the number of success/failure branches
;;; and N is total number of terminated branches so far.

(defstruct (dp-clause-set
            (:print-function print-dp-clause-set3)
            (:copier nil))
  (atoms nil)
  (number-of-atoms 0 :type integer)	;in atom-hash-table, may not all appear in clauses
  (number-of-clauses 0 :type integer)
  (number-of-literals 0 :type integer)
  (p-clauses nil)			;clauses that initially contained only positive literals
  (n-clauses nil)			;clauses that initially contained only negative literals
  (m1-clauses nil)			;clauses that initially were mixed Horn clauses
  (m2-clauses nil)			;clauses that initially were mixed non-Horn clauses
  (atom-hash-table (make-hash-table :test #'equal))
  (atoms-last nil)
  (p-clauses-last nil)
  (n-clauses-last nil)
  (m1-clauses-last nil)
  (m2-clauses-last nil)
  (number-to-atom-hash-table (make-hash-table))
  (checkpoint-level 0 :type fixnum)
  (checkpoints nil))

(defstruct (dp-clause
            (:print-function print-dp-clause)
            (:copier nil))
  (number-of-unresolved-positive-literals 0 :type fixnum)
  (number-of-unresolved-negative-literals 0 :type fixnum)
  (positive-literals nil :type list)
  (negative-literals nil :type list)
  (subsumption-mark nil)
  (next nil))

(defstruct (dp-atom
            (:print-function print-dp-atom)
            (:copier nil))
  name
  number
  (value nil)
  (contained-positively-clauses nil)
  (contained-negatively-clauses nil)
  (derived-from-clause nil)
  (used-in-refutation-p nil)
  (next nil)
  (choice-point nil)
  true-triable					;used by lookahead
  false-triable					;used by lookahead
  (number-of-occurrences 0 :type integer)
  (checkpoints nil))

(defvar *default-find-all-models* 1)
(defvar *default-model-test-function* nil)
(defvar *default-dependency-check* t)
(defvar *default-pure-literal-check* t)
(defvar *default-atom-choice-function* 'choose-an-atom-of-a-shortest-positive-clause)
(defvar *default-more-units-function* nil)
(defvar *default-branch-limit* nil)
(defvar *default-time-limit* nil)
(defvar *default-minimal-models-suffice* t)
(defvar *default-minimal-models-only* nil)
(defvar *default-convert-to-clauses* nil)
(defvar *default-dimacs-cnf-format* :p)
(defvar *default-subsumption* nil)
(defvar *default-print-summary* t)
(defvar *default-print-warnings* t)

(defvar *dependency-check*)
(defvar *more-units-function*)
(defvar *minimal-models-suffice*)
(defvar *clause-set*)
(defvar *assignment-count* 0)
(declaim (type integer *assignment-count*))

(defun dp-satisfiable-p (clause-set
			 &key
			 (find-all-models *default-find-all-models*)
			 (model-test-function *default-model-test-function*)
                         ((:dependency-check *dependency-check*) *default-dependency-check*)
                         (pure-literal-check *default-pure-literal-check*)
			 (atom-choice-function *default-atom-choice-function*)
			 ((:more-units-function *more-units-function*) *default-more-units-function*)
			 (branch-limit *default-branch-limit*)
			 (time-limit *default-time-limit*)
			 ((:minimal-models-suffice *minimal-models-suffice*) *default-minimal-models-suffice*)
                         (minimal-models-only *default-minimal-models-only*)
                         (subsumption *default-subsumption*)
			 (print-summary *default-print-summary*)
			 (print-warnings *default-print-warnings*))
  ;; Determines satisfiability of the set of clauses in clause-set.
  ;; If find-all-models argument is T, dp-satisfiable-p will return
  ;; a list of all models it finds in an exhaustive search; if it is NIL, T/NIL
  ;; will be returned if a model is/is not found; if it is an integer N >= 1,
  ;; only the first N models will be returned; if it is an integer N <= -1,
  ;; models after the first -N will be searched for and counted but not
  ;; returned.
  ;;
  ;; DP-SATISFIABLE-P ordinarily is not guaranteed to find all models but only
  ;; all minimal models (and possibly some non-minimal ones).  It returns
  ;; only the true atoms of a model; all others are false.  A model M is
  ;; minimal if for no other model M' is it the case that the true atoms
  ;; of M' are a proper subset of the true atoms of M.  For many types of
  ;; problems (e.g., quasigroup existence and N-queens problems) all models
  ;; are minimal.  A set of clauses with no more positive clauses is
  ;; recognized to be satisfiable under the assignment of false to all
  ;; unassigned atoms.
  ;;
  ;; If minimal-models-suffice argument is NIL, DP-SATISFIABLE-P behavior is
  ;; modified to exhaustively find assignments that explicitly satisfy every
  ;; clause; false assignments are represented as negative literals in
  ;; the models returned.  Atoms not assigned a value can be either true
  ;; or false.
  ;;
  ;; If minimal-models-only argument is non-NIL, only minimal models
  ;; will be returned.  As in Bry and Yahya's MM-SATCHMO, false
  ;; assignments are considered before true ones when branching
  ;; and redundant models are pruned by adding negated models as
  ;; clauses.  Pure-literal-check will not assign true to a pure atom.
  ;;
  ;; If dependency-check argument is non-NIL, a form of intelligent
  ;; backtracking is used.  If there are only failures below the
  ;; true assignment at a choice point, and the assignment was never
  ;; used to generate any of the contradictions, exploration of
  ;; the false assignment will be skipped, as it will fail for
  ;; the same reasons.
  ;;
  ;; If pure-literal-check argument is non-NIL, literals that are
  ;; pure in the original set of clauses will be assigned a satisfying
  ;; value.  There is no checking if a literal becomes pure later.
  ;;
  ;; If more-units-function argument is non-nil, it names a function
  ;; to be executed after unit propagation.  The function may
  ;; detect unsatisfiability or compute more unit clauses by
  ;; additional means such as 2-closure or lookahead.
  (assert-unvalued-dp-clause-set-p clause-set)
  (cl:assert (or (eq find-all-models t)
	         (eq find-all-models nil)
	         (and (integerp find-all-models)
		      (not (zerop find-all-models))))
	     (find-all-models)
	     "find-all-models = ~A but should be t, nil, or a nonzero integer." find-all-models)
;;(cl:assert (not (and *dependency-check* *more-units-function*))
;;	     (*dependency-check* *more-units-function*)
;;	     "Dependency-check cannot be used with more-units-function.")
  (cl:assert (not (and minimal-models-only (not *minimal-models-suffice*)))
             (minimal-models-only *minimal-models-suffice*)
             "Minimal-models-only cannot be used without minimal-models-suffice.")
  (cl:assert (not (and pure-literal-check (not *minimal-models-suffice*)))
	     (pure-literal-check *minimal-models-suffice*)
	     "Pure-literal-check cannot be used without minimal-models-suffice.")
  (let* ((*print-pretty* nil)
	 (models nil) models-last
	 (branch-count 1)
	 (success-branch-count 0)
	 (failure-branch-count 0)
	 (cutoff-branch-count 0)
	 (report-reaching-branch-limit print-summary)
	 (*assignment-count* 0)
	 (forced-choice-count 0)
	 (dp-tracing-choices (if (eq dp-tracing t) t dp-tracing-choices))
	 (dp-tracing-choices-depth (if (and dp-tracing-choices
					    (not (eq dp-tracing-choices t))
					    (>= 0 dp-tracing-choices))
				       0
				       10000))
	 (*clause-set* clause-set)
	 start-time)
    (declare (type integer branch-count success-branch-count failure-branch-count)
             (type integer cutoff-branch-count forced-choice-count))
    (macrolet
      ((process-success-branch ()
         `(progn
            (incf success-branch-count)
            (when (eq dp-tracing t)
              (format t "Succeed (~D/~D)~%"
		      success-branch-count
		      (+ success-branch-count failure-branch-count cutoff-branch-count)))
            (when minimal-models-only
              ;; add constraint to eliminate supermodel generation
              (add-model-constraint clause-set))
	    (cond
	      ((null find-all-models)
	       t)
	      ((or (eq find-all-models t)
		   (plusp find-all-models)
		   (<= success-branch-count (- find-all-models)))
		(let ((model (if *minimal-models-suffice*
				 (true-atoms clause-set)
				 (valued-atoms clause-set))))
		  (when dp-tracing-models
		    (format t "~&Model ~D = ~A "
			    success-branch-count
			    model))
		  (cond
                    ((and minimal-models-only (null model))
                     (cl:assert (null models))
                     (list model))
		    (t
		     (collect model models)
		     (if (eql success-branch-count find-all-models)
			 models
			 nil)))))
	      (t
	       nil))))
       (process-failure-branch ()
         `(progn
            (incf failure-branch-count)
            (when (eq dp-tracing t)
              (format t "Fail (~D/~D)~%"
		      failure-branch-count
		      (+ success-branch-count failure-branch-count cutoff-branch-count)))
            nil))
       (process-cutoff-branch ()
	 `(progn
	    (incf cutoff-branch-count)
	    (when (eq dp-tracing t)
	      (format t "Cutoff (~D/~D)~%"
		      cutoff-branch-count
		      (+ success-branch-count failure-branch-count cutoff-branch-count)))
	    nil)))
      (labels
        ((dp-satisfiable-p* (depth)
	   (declare (fixnum depth))
	   (multiple-value-bind (atom value1 value2 chosen-clause)
	       ;; try value1, then value2
	       (funcall atom-choice-function clause-set)
             (when (and minimal-models-only (eq :false value2))
               ;; try false assignment first when seeking minimal-models
               (setq value1 :false value2 :true))
             (cond
	       ((eq atom :unsatisfiable)
		(process-failure-branch))
	       ((and branch-limit
		     (>= branch-count branch-limit)
		     (or (null time-limit)
			 (let ((time (run-time-since start-time)))
			   (cond
			     ((>= time time-limit)
			      t)
			     (t
			      (setq branch-limit (max branch-limit (ceiling (* branch-count (min 100 (/ time-limit time))))))
			      nil)))))
		(when report-reaching-branch-limit
		  (format t "~&Branch limit reached.")
		  (print-dp-choice-points clause-set (run-time-since start-time))
		  (setq dp-tracing-choices nil)
		  (setq report-reaching-branch-limit nil))
		(setq time-limit nil)		;done with this now
		(setq *dependency-check* nil)	;treat remaining branches as failed, not cutoff
		(process-failure-branch))
	       ((eq atom :satisfiable)
		(if (or (null model-test-function)
			(progn
			  (when (or (eq dp-tracing t) dp-tracing-models)
			    (format t "Test model "))
			  (funcall model-test-function (if *minimal-models-suffice*
							   (true-atoms clause-set)
							   (valued-atoms clause-set)))))
		    (process-success-branch)
		    (process-failure-branch)))
	       (t
		(cl:assert (null (dp-atom-value atom)) ()
			   "Atom ~A was chosen for splitting, but it is already ~A."
			   atom (dp-atom-value atom))
		(let (v (cut nil))
		  ;; must make a copy of chosen-clause for trace output
		  ;; before making truth-value assignments
		  (when (and dp-tracing-choices
			     chosen-clause
			     (or (eq dp-tracing-choices t)
				 (< depth dp-tracing-choices-depth)))
		    (setq chosen-clause (decode-dp-clause chosen-clause)))
		  (setf (dp-atom-value atom) value1)
		  (setf (dp-atom-next atom) nil)
		  (cond
		    ((null value2)
		     (incf forced-choice-count)
		     (when (and dp-tracing-choices
				(or (eq dp-tracing-choices t)
				    (< depth dp-tracing-choices-depth)))
		       (print-dp-trace-line depth atom value1 nil t chosen-clause))
                     (setq v (assign-atoms atom))
		     (cond
		       ((eq v :unsatisfiable)
			(process-failure-branch))
		       (t
			(prog1 (dp-satisfiable-p* depth)
			       (unassign-atoms v)))))
		    (t
		     (incf branch-count)
		     (cond
		       ((and dp-tracing-choices
			     (or (eq dp-tracing-choices t)
				 (< depth dp-tracing-choices-depth)))
			(print-dp-trace-line depth atom value1 branch-count nil chosen-clause))
		       ((and dp-tracing (eql 0 (rem branch-count dp-tracing)))
			(when (and dp-tracing-state
				   (eql 0 (rem branch-count (* dp-tracing dp-tracing-state))))
			  (print-dp-choice-points clause-set (run-time-since start-time)))
			(princ branch-count)
			(princ " ")
			(force-output)))
                     (setq v (assign-atoms atom))
		     (cond
		       ((if (eq v :unsatisfiable)
			    (process-failure-branch)
			    (prog2
			      (setf (dp-atom-choice-point atom) branch-count)
			      (if (not *dependency-check*)
				  (prog1 (dp-satisfiable-p* (1+ depth))
					 (unassign-atoms v))
;;				  (let ((old-success-branch-count success-branch-count))	;miscompiled in GCL
				  (let ((old-success-branch-count 0))
                                    (declare (type integer old-success-branch-count))
				    (setq old-success-branch-count success-branch-count)
				    (prog1 (dp-satisfiable-p* (1+ depth))
					   (when (and *dependency-check*
						      (not (dp-atom-used-in-refutation-p atom))
						      (eql old-success-branch-count
							   success-branch-count))
					     (setq cut t))
					   (unassign-atoms v))))
			      (setf (dp-atom-choice-point atom) nil)))
			)
		       (t
			(cond
			  ((null dp-tracing-choices)
			   )
			  ((eq dp-tracing-choices t)
			   (print-dp-trace-line depth atom value2 nil t nil))
			  ((< depth dp-tracing-choices-depth)
			   (let ((n (+ depth dp-tracing-choices)))
			     (when (< n dp-tracing-choices-depth)
			       (setq dp-tracing-choices-depth n)))
			   (print-dp-trace-line depth atom value2 nil t nil)))
                        (cond
                          (cut
                           (process-cutoff-branch))
                          (t
			   (setf (dp-atom-value atom) value2)
			   (setf (dp-atom-next atom) nil)
                           (setq v (assign-atoms atom))
			   (cond
			     ((eq v :unsatisfiable)
			      (process-failure-branch))
			     (t
			      (prog1 (dp-satisfiable-p* depth)
				     (unassign-atoms v))))))))))))))))
        (when print-summary
          (dp-count clause-set t))
        (when subsumption
          (dp-subsumption clause-set print-summary))
	(when print-summary
	  (format t "~%~A version ~A control settings:" dp-prover dp-version)
          (format t "~%  atom-choice-function   = ~A" atom-choice-function)
	  (format t "~%  more-units-function    = ~A" *more-units-function*)
	  (format t "~%  model-test-function    = ~A" model-test-function)
	  (format t "~%  dependency-check       = ~A" *dependency-check*)
	  (format t "~%  pure-literal-check     = ~A" pure-literal-check)
	  (format t "~%  find-all-models        = ~A" find-all-models)
          (cond
           (minimal-models-only
            (format t "~%  minimal-models-only    = ~A" minimal-models-only))
           ((not *minimal-models-suffice*)
	    (format t "~%  minimal-models-suffice = ~A" *minimal-models-suffice*)))
	  (when branch-limit
	    (format t "~%  branch-limit           = ~A" branch-limit))
	  (when time-limit
	    (format t "~%  time-limit             = ~A" time-limit))
	  (terpri))
	(when print-warnings
          (let ((neg-pure-atoms nil) neg-pure-atoms-last
                (pos-pure-atoms nil) pos-pure-atoms-last)
            (dolist (atom (dp-clause-set-atoms clause-set))
              (when (and (null (dp-atom-contained-positively-clauses atom))	;atom occurs negatively only
                         (dp-atom-contained-negatively-clauses atom))
                (collect atom neg-pure-atoms))
              (when (and (null (dp-atom-contained-negatively-clauses atom))	;atom occurs positively only
                         (dp-atom-contained-positively-clauses atom))
                (collect atom pos-pure-atoms)))
            (when neg-pure-atoms
              (warn "There are no positive occurrences of atom~P ~A~{, ~A~}."
                    (unless (rest neg-pure-atoms) 1)
                    (first neg-pure-atoms)
                    (rest neg-pure-atoms)))
            (when pos-pure-atoms
              (warn "There are no negative occurrences of atom~P ~A~{, ~A~}."
                    (unless (rest pos-pure-atoms) 1)
                    (first pos-pure-atoms)
                    (rest pos-pure-atoms)))))
        (let (time initial-units (result nil) (pure-literals nil)
	      (positive-pure-literal-count 0) (negative-pure-literal-count 0)
	      (normal-exit nil))
          (declare (type integer positive-pure-literal-count negative-pure-literal-count))
	  (setq start-time (run-time-since 0.0))
	  ;; time-limit uses branch-limit that is raised when reached
	  ;; until time-limit is reached
	  (when time-limit
	    (unless branch-limit
	      (setq branch-limit 1000)))
	  (when pure-literal-check
	    (dolist (atom (dp-clause-set-atoms clause-set))
	      (unless (dp-atom-value atom)
		(cond
		  ((and (null (dp-atom-contained-positively-clauses atom))	;atom occurs negatively only
			(dp-atom-contained-negatively-clauses atom))
		   (incf negative-pure-literal-count)
		   (setf (dp-atom-value atom) :false)
		   (setf (dp-atom-next atom) pure-literals)
		   (setq pure-literals atom))
		  ((and (null (dp-atom-contained-negatively-clauses atom))	;atom occurs positively only
			(dp-atom-contained-positively-clauses atom)
                        (not minimal-models-only))
		   (incf positive-pure-literal-count)
		   (setf (dp-atom-value atom) :true)
		   (setf (dp-atom-next atom) pure-literals)
		   (setq pure-literals atom)))))
	    (when pure-literals
              (setq pure-literals (assign-atoms pure-literals))))
	  (unwind-protect
	      (progn
		(cond
		  ((or (eq (setq initial-units (find-unit-clauses clause-set))
			   :unsatisfiable)
		       (eq (setq initial-units (assign-atoms initial-units))
			   :unsatisfiable))
		   (setq result (process-failure-branch)))
		  (t
		   (setq result (dp-satisfiable-p* 0))
		   (unassign-atoms initial-units)))
		(when pure-literals
		  (unassign-atoms pure-literals))
		(setq normal-exit t))
	    (setq time (run-time-since start-time))
	    (unless normal-exit
	      (when print-summary
		(format t "~&Abnormal exit.")
		(print-dp-choice-points clause-set time))
	      (fix-dp-clause-set clause-set))
	    (when print-summary
	      (format t "~&Found ~D success, ~D failure, ~D cutoff, ~D total branches in ~,1F seconds."
		      success-branch-count
		      failure-branch-count
		      cutoff-branch-count
		      (+ success-branch-count failure-branch-count cutoff-branch-count)
		      time)
	      #+ignore
	      (format t "~%~D assignment~:P." *assignment-count*)
	      (when (plusp positive-pure-literal-count)
		(format t "~%~D atom~:P occurred purely positively in the input."
			positive-pure-literal-count))
	      (when (plusp negative-pure-literal-count)
		(format t "~%~D atom~:P occurred purely negatively in the input."
			negative-pure-literal-count))
	      (when (plusp forced-choice-count)
		(format t "~%~D choice~:P forced." forced-choice-count))))
	  (values (or result models)
		  success-branch-count
		  failure-branch-count
		  cutoff-branch-count
		  time
		  *assignment-count*
		  positive-pure-literal-count
		  negative-pure-literal-count
		  forced-choice-count))))))

(defun dp-satisfiable-file-p (filename &rest options
			      &key
			      (convert-to-clauses *default-convert-to-clauses*)
			      (dimacs-cnf-format *default-dimacs-cnf-format*)
			      (print-summary *default-print-summary*)
			      (print-warnings *default-print-warnings*)
			      &allow-other-keys)
  (apply #'dp-satisfiable-p
	 (dp-insert-file filename nil
			 :convert-to-clauses convert-to-clauses
			 :dimacs-cnf-format dimacs-cnf-format
			 :print-summary print-summary
			 :print-warnings print-warnings)
         (do ((x options (cddr x))
              (v nil) v-last)
             ((null x)
              v)
           (unless (member (first x) '(:convert-to-clauses :dimacs-cnf-format))
	     (collect (first x) v)
	     (collect (second x) v)))))

(defun dp-insert (clause clause-set &optional (print-warnings *default-print-warnings*))
  (cl:assert (not (null clause)) ()
	     "Cannot insert the empty clause.")
  (if clause-set
      (assert-dp-clause-set-p clause-set)
      (setq clause-set (make-dp-clause-set)))
  (unless (eq print-warnings :safe)
    (let ((v (clause-contains-repeated-atom clause)))
      (cond
	((eq v :tautology)
	 (when print-warnings
	   (warn "Complementary literals in clause ~A." clause))
	 (return-from dp-insert
	   clause-set))
	(v
	 (when print-warnings
	   (warn "Duplicate literals in clause ~A." clause))
	 (setq clause (delete-duplicates clause :test #'equal))))))
  (let ((cl (make-dp-clause))
        (nlits 0)
        (p 0)
        (n 0)
        (positive-literals nil)
        (negative-literals nil)
        positive-literals-last
        negative-literals-last)
    (dolist (lit clause)
      (let* ((neg (negative-literal-p lit))
             (atom0 (or neg lit))
             (atom (if (dp-atom-p atom0)
                       atom0
                       (atom-named atom0
                                   clause-set
                                   :if-does-not-exist :create))))
	(checkpoint-dp-atom atom clause-set)
	(incf (dp-atom-number-of-occurrences atom))
	(incf nlits)
	(cond
	  (neg
	   (unless (eq :true (dp-atom-value atom))
             (incf n))
           (collect atom negative-literals)
	   (push cl (dp-atom-contained-negatively-clauses atom)))
	  (t
	   (unless (eq :false (dp-atom-value atom))
             (incf p))
           (collect atom positive-literals)
	   (push cl (dp-atom-contained-positively-clauses atom))))))
    (incf (dp-clause-set-number-of-clauses clause-set))
    (incf (dp-clause-set-number-of-literals clause-set) nlits)
    (when positive-literals
      (setf (dp-clause-number-of-unresolved-positive-literals cl) p)
      (setf (dp-clause-positive-literals cl) positive-literals))
    (when negative-literals
      (setf (dp-clause-number-of-unresolved-negative-literals cl) n)
      (setf (dp-clause-negative-literals cl) negative-literals))
    (cond
     ((null negative-literals)
      (if (dp-clause-set-p-clauses clause-set)
          (let ((temp (dp-clause-set-p-clauses-last clause-set)))
            (setf (dp-clause-next temp)
                  (setf (dp-clause-set-p-clauses-last clause-set) cl)))
          (setf (dp-clause-set-p-clauses clause-set)
                (setf (dp-clause-set-p-clauses-last clause-set) cl))))
     ((null positive-literals)
      (if (dp-clause-set-n-clauses clause-set)
          (let ((temp (dp-clause-set-n-clauses-last clause-set)))
            (setf (dp-clause-next temp)
                  (setf (dp-clause-set-n-clauses-last clause-set) cl)))
          (setf (dp-clause-set-n-clauses clause-set)
                (setf (dp-clause-set-n-clauses-last clause-set) cl))))
     ((null (rest positive-literals))
      (if (dp-clause-set-m1-clauses clause-set)
          (let ((temp (dp-clause-set-m1-clauses-last clause-set)))
            (setf (dp-clause-next temp)
                  (setf (dp-clause-set-m1-clauses-last clause-set) cl)))
          (setf (dp-clause-set-m1-clauses clause-set)
                (setf (dp-clause-set-m1-clauses-last clause-set) cl))))
     (t
      (if (dp-clause-set-m2-clauses clause-set)
          (let ((temp (dp-clause-set-m2-clauses-last clause-set)))
            (setf (dp-clause-next temp)
                  (setf (dp-clause-set-m2-clauses-last clause-set) cl)))
          (setf (dp-clause-set-m2-clauses clause-set)
                (setf (dp-clause-set-m2-clauses-last clause-set) cl))))))
  clause-set)

(defun dp-insert-sorted (clause clause-set &optional (print-warnings *default-print-warnings*))
  ;; clauses are not required to be sorted, so unsorted clause is inserted
  (dp-insert clause clause-set print-warnings))

(defun dp-insert-wff (wff clause-set &optional (print-warnings *default-print-warnings*))
  ;; convert a wff to clause form and insert the clauses
  (if clause-set
      (assert-dp-clause-set-p clause-set)
      (setq clause-set (make-dp-clause-set)))
  (wff-clauses wff (lambda (clause)
                     (dp-insert-sorted clause clause-set print-warnings)))
  clause-set)

(defvar *dp-read-string*)
(defvar *dp-read-index*)

(defun dp-read (s dimacs-cnf-format print-warnings)
  ;; reads a single clause if dimacs-cnf-format = nil
  ;; reads a single literal if dimacs-cnf-format = t
  (loop
    (cond
     (dimacs-cnf-format
      (multiple-value-bind (x i)
	  (read-from-string *dp-read-string* nil :eof :start *dp-read-index*)
        (cond
         ((eq :eof x)
          (if (eq :eof (setq *dp-read-string* (read-line s nil :eof)))
              (return :eof)
              (setq *dp-read-index* 0)))
         ((integerp x)
          (setq *dp-read-index* i)
          (return x))
         ((eql 0 *dp-read-index*)		;ignore DIMACS problem/comment line
          (when print-warnings
            (warn "Skipping line ~A" *dp-read-string*))
          (if (eq :eof (setq *dp-read-string* (read-line s nil :eof)))
              (return :eof)
              (setq *dp-read-index* 0)))
         (t
          (when print-warnings
            (warn "Skipping noninteger ~A" x))
          (setq *dp-read-index* i)))))
     (t
      (let ((x (read s nil :eof)))
        (cond
         ((or (eq :eof x) (consp x))
          (return x))			;no syntax checking
         (print-warnings
          (warn "Skipping nonclause ~A" x))))))))

(defun dp-insert-file (filename clause-set
		       &key
		       (convert-to-clauses *default-convert-to-clauses*)
		       (dimacs-cnf-format *default-dimacs-cnf-format*)
		       (print-summary *default-print-summary*)
		       (print-warnings *default-print-warnings*))
  (let ((start-time (run-time-since 0.0)) (nclauses 0) (nlits 0))
    (declare (type integer nclauses nlits))
    (if clause-set
	(assert-dp-clause-set-p clause-set)
	(setq clause-set (make-dp-clause-set)))
    (when print-summary
      (format t "~2%Problem from file ~A:" filename))
    (with-open-file (s filename :direction :input)
      (cond
	(dimacs-cnf-format
	 (let ((*dp-read-string* "") (*dp-read-index* 0) (lits nil))
           (loop
             (let ((x (dp-read s t print-warnings)))
               (cond
                ((eq :eof x)
                 (return))
                ((eql 0 x)
                 (when lits
                   (incf nclauses)
                   (incf nlits (length lits))
                   (dp-insert-sorted (nreverse lits) clause-set print-warnings)
                   (setq lits nil)))
                (t
                 (push x lits)))))
           (when lits
             (setq lits (nreverse lits))
             (when print-warnings
               (warn "Last clause ~A in file not followed by 0." lits))
             (incf nclauses)
             (incf nlits (length lits))
             (dp-insert-sorted lits clause-set print-warnings))))
	(t
         (loop
           (let ((x (dp-read s nil print-warnings)))
             (cond
              ((eq :eof x)
               (return))
              (convert-to-clauses
               (dp-insert-wff x clause-set print-warnings))	;nclauses, nlits not incremented as they should be
              (t
               (incf nclauses)
               (incf nlits (length x))
               (dp-insert-sorted x clause-set print-warnings))))))))
    (when print-summary
      (format t "~&Input from file     ~D clauses with ~D literals in ~,1F seconds."
	      nclauses
	      nlits
	      (run-time-since start-time)))
    clause-set))

(defmacro clause-contains-true-positive-literal (clause)
  (let ((atom (gensym)))
    `(dolist (,atom (dp-clause-positive-literals ,clause) nil)
       (when (eq :true (dp-atom-value ,atom))
         (return t)))))

(defmacro clause-contains-true-negative-literal (clause)
  (let ((atom (gensym)))
    `(dolist (,atom (dp-clause-negative-literals ,clause))
       (when (eq :false (dp-atom-value ,atom))
         (return t)))))

(defun dp-horn-clause-set-p (clause-set)
  ;; never more than one positive literal in a clause
  ;; (unless the clause is true in the current truth assignment)
  (and (do ((clause (dp-clause-set-p-clauses clause-set) (dp-clause-next clause)))
           ((null clause)
            t)
         (when (and (< 1 (dp-clause-number-of-unresolved-positive-literals clause))
                    (not (clause-contains-true-positive-literal clause)))
           (return nil)))
       (do ((clause (dp-clause-set-m2-clauses clause-set) (dp-clause-next clause)))
           ((null clause)
            t)
         (when (and (< 1 (dp-clause-number-of-unresolved-positive-literals clause))
                    (not (clause-contains-true-positive-literal clause))
                    (not (clause-contains-true-negative-literal clause)))
           (return nil)))))

(defun dp-count (clause-set &optional print-p)
  ;; (dp-count clause-set) returns and optionally prints the
  ;; clause and literal count of clauses stored in clause-set
  (let ((nclauses 0) (nliterals 0) (natoms 0) (assigned nil))
    (when clause-set
      (dolist (atom (dp-clause-set-atoms clause-set))
	(when (or (dp-atom-contained-positively-clauses atom)	;atom appears in clause-set
		  (dp-atom-contained-negatively-clauses atom))
	  (if (dp-atom-value atom)
	      (setq assigned t)
	      (incf natoms))))
      (cond
	((not assigned)
	 (setq nclauses (dp-clause-set-number-of-clauses clause-set))
	 (setq nliterals (dp-clause-set-number-of-literals clause-set)))
	(t
         (do ((clause (dp-clause-set-p-clauses clause-set) (dp-clause-next clause)))
             ((null clause))
           (unless (clause-contains-true-positive-literal clause)
             (incf nclauses)
             (incf nliterals (dp-clause-number-of-unresolved-positive-literals clause))))
         (do ((clause (dp-clause-set-n-clauses clause-set) (dp-clause-next clause)))
             ((null clause))
           (unless (clause-contains-true-negative-literal clause)
             (incf nclauses)
             (incf nliterals (dp-clause-number-of-unresolved-negative-literals clause))))
         (do ((clause (dp-clause-set-m1-clauses clause-set) (dp-clause-next clause)))
             ((null clause))
           (unless (or (clause-contains-true-positive-literal clause)
                       (clause-contains-true-negative-literal clause))
             (incf nclauses)
             (incf nliterals (dp-clause-number-of-unresolved-positive-literals clause))
             (incf nliterals (dp-clause-number-of-unresolved-negative-literals clause))))
         (do ((clause (dp-clause-set-m2-clauses clause-set) (dp-clause-next clause)))
             ((null clause))
           (unless (or (clause-contains-true-positive-literal clause)
                       (clause-contains-true-negative-literal clause))
             (incf nclauses)
             (incf nliterals (dp-clause-number-of-unresolved-positive-literals clause))
             (incf nliterals (dp-clause-number-of-unresolved-negative-literals clause)))))))
    (when print-p
      (format t "~&Clause set contains ~D clauses with ~D literals formed from ~D atoms~A."
	      nclauses nliterals natoms (if (stringp print-p) print-p "")))
    (values nclauses nliterals natoms)))

(defun dp-clauses (map-fun clause-set &optional decode-fun)
  ;; either return or apply map-fun to all clauses in clause-set
  (when clause-set
    (cond
      (map-fun
       (do ((clause (dp-clause-set-p-clauses clause-set) (dp-clause-next clause)))
           ((null clause))
         (unless (clause-contains-true-positive-literal clause)
           (funcall map-fun (decode-dp-clause clause decode-fun))))
       (do ((clause (dp-clause-set-n-clauses clause-set) (dp-clause-next clause)))
           ((null clause))
         (unless (clause-contains-true-negative-literal clause)
           (funcall map-fun (decode-dp-clause clause decode-fun))))
       (do ((clause (dp-clause-set-m1-clauses clause-set) (dp-clause-next clause)))
           ((null clause))
         (unless (or (clause-contains-true-positive-literal clause)
                     (clause-contains-true-negative-literal clause))
           (funcall map-fun (decode-dp-clause clause decode-fun))))
       (do ((clause (dp-clause-set-m2-clauses clause-set) (dp-clause-next clause)))
           ((null clause))
         (unless (or (clause-contains-true-positive-literal clause)
                     (clause-contains-true-negative-literal clause))
           (funcall map-fun (decode-dp-clause clause decode-fun)))))
      (t
       (let ((result nil) result-last)
         (do ((clause (dp-clause-set-p-clauses clause-set) (dp-clause-next clause)))
             ((null clause))
           (unless (clause-contains-true-positive-literal clause)
             (collect (decode-dp-clause clause decode-fun) result)))
	 (do ((clause (dp-clause-set-n-clauses clause-set) (dp-clause-next clause)))
             ((null clause))
           (unless (clause-contains-true-negative-literal clause)
             (collect (decode-dp-clause clause decode-fun) result)))
	 (do ((clause (dp-clause-set-m1-clauses clause-set) (dp-clause-next clause)))
             ((null clause))
           (unless (or (clause-contains-true-positive-literal clause)
                       (clause-contains-true-negative-literal clause))
             (collect (decode-dp-clause clause decode-fun) result)))
	 (do ((clause (dp-clause-set-m2-clauses clause-set) (dp-clause-next clause)))
             ((null clause))
           (unless (or (clause-contains-true-positive-literal clause)
                       (clause-contains-true-negative-literal clause))
             (collect (decode-dp-clause clause decode-fun) result)))
         result)))))

(defun dp-output-clauses-to-file (filename clause-set &key (dimacs-cnf-format *default-dimacs-cnf-format*))
  ;; write clauses in clause-set to a file
  (with-open-file (s filename :direction :output :if-exists :new-version)
    (cond
      (dimacs-cnf-format
       (when (eq :p dimacs-cnf-format)
         (format s "p cnf ~D ~D~%" (dp-clause-set-number-of-atoms clause-set) (dp-count clause-set)))
       (dp-clauses (lambda (clause)
                     (dolist (lit clause)
                       (princ lit s)
                       (princ " " s))
                     (princ 0 s)
                     (terpri s))
		   clause-set
		   (if (dolist (atom (dp-clause-set-atoms clause-set) t)
                         (unless (and (integerp (dp-atom-name atom))
                                      (plusp (dp-atom-name atom)))
                           (return nil)))
		       nil
		       #'dp-atom-number)))
      (t
       (dp-clauses (lambda (clause)
                     (prin1 clause s)
                     (terpri s))
		   clause-set))))
  nil)

(defun assert-dp-clause-set-p (clause-set)
  (cl:assert (dp-clause-set-p clause-set) ()
	     "~S is not a dp-clause-set." clause-set))

(defun assert-unvalued-dp-clause-set-p (clause-set)
  (assert-dp-clause-set-p clause-set)
  (cl:assert (dolist (atom (dp-clause-set-atoms clause-set) t)
               (when (dp-atom-value atom)
                 (return nil)))))

(defun add-model-constraint (clause-set)
  ;; for nonredundant generation of minimal models,
  ;; add clause of negations of atoms true in model
  (let ((cl (make-dp-clause))
        (nlits 0)
        (negative-literals nil)
        negative-literals-last)
    (dolist (atom (dp-clause-set-atoms clause-set))
      (when (eq :true (dp-atom-value atom))
	(checkpoint-dp-atom atom clause-set)
	(incf (dp-atom-number-of-occurrences atom))
	(incf nlits)
	(collect atom negative-literals)
	(push cl (dp-atom-contained-negatively-clauses atom))))
    (when negative-literals
      (incf (dp-clause-set-number-of-clauses clause-set))
      (incf (dp-clause-set-number-of-literals clause-set) nlits)
      (setf (dp-clause-negative-literals cl) negative-literals)
      (if (dp-clause-set-n-clauses clause-set)
          (let ((temp (dp-clause-set-n-clauses-last clause-set)))
            (setf (dp-clause-next temp)
                  (setf (dp-clause-set-n-clauses-last clause-set) cl)))
          (setf (dp-clause-set-n-clauses clause-set)
                (setf (dp-clause-set-n-clauses-last clause-set) cl))))))

(defun true-atoms (clause-set)
  (let ((result nil) result-last)
    (dolist (atom (dp-clause-set-atoms clause-set))
      (when (and (eq :true (dp-atom-value atom))
                 (or (dp-atom-contained-positively-clauses atom)	;atom appears in clause-set
                     (dp-atom-contained-negatively-clauses atom)))
        (collect (dp-atom-name atom) result)))
    result))

(defun valued-atoms (clause-set)
  (let ((result nil) result-last)
    (dolist (atom (dp-clause-set-atoms clause-set))
      (let ((value (dp-atom-value atom)))
	(when (and value
		   (or (dp-atom-contained-positively-clauses atom)	;atom appears in clause-set
		       (dp-atom-contained-negatively-clauses atom)))
	  (collect (if (eq :true value)
		       (dp-atom-name atom)
		       (complementary-literal (dp-atom-name atom)))
                   result))))
    result))

(defun atom-named (x clause-set &key (if-does-not-exist :error))
  (cl:assert (and (not (null x)) (not (eql 0 x))) ()
	     "~A cannot be used as an atomic formula." x)
  (let ((table (dp-clause-set-atom-hash-table clause-set)))
    (or (gethash x table)
	(ecase if-does-not-exist
	  (:create
	    (let ((atom (make-dp-atom
			  :name x
			  :number (cond
                                   ((integerp x)
                                    (incf (dp-clause-set-number-of-atoms clause-set))
                                    (cl:assert (null (gethash x (dp-clause-set-number-to-atom-hash-table clause-set))) ()
                                               "Atom named ~A cannot be atom number ~A." x x)
                                    x)
                                   (t
                                    (incf (dp-clause-set-number-of-atoms clause-set)))))))
	      (collect atom (dp-clause-set-atoms clause-set))
	      (setf (gethash (dp-atom-number atom) (dp-clause-set-number-to-atom-hash-table clause-set)) atom)
	      (setf (gethash x table) atom)))
	  (:error
	    (error "Unknown atom ~A." x))
	  ((nil)
	   nil)))))

(defun negative-literal-p (lit)
  ;; if 'lit' is a negative literal, return its atom
  ;; if 'lit' is a positive literal, return 'nil'
  (cond
   ((numberp lit)				;positive number is atomic formula
    (and (minusp lit) (- lit)))			;negative number is its negation
   ((consp lit)
    (and (eq 'not (car lit)) (cadr lit)))	;(not x) is negation of atomic formula x
   (t
    nil)))					;everything else is an atomic formula

(defun complementary-literal (lit)
  (cond
    ((numberp lit)
     (- lit))
    ((and (consp lit) (eq 'not (first lit)))
     (second lit))
    (t
     (list 'not lit))))

(defun clause-contains-repeated-atom (clause)
  (do* ((dup nil)
        (lits clause (rest lits))
        (lit (first lits) (first lits))
        (clit (complementary-literal lit) (complementary-literal lit)))
       ((null (rest lits))
        dup)
    (dolist (lit2 (rest lits))
      (cond
       ((equal lit lit2)
        (setq dup t))
       ((equal clit lit2)
        (return-from clause-contains-repeated-atom
          :tautology))))))

(defun print-dp-clause-set3 (clause-set &optional (stream *standard-output*) depth)
  (declare (ignore depth))
  (print-unreadable-object (clause-set stream :type t :identity t)
    (princ (dp-clause-set-number-of-atoms clause-set) stream)
    (princ " atoms " stream)
    (princ (dp-clause-set-number-of-clauses clause-set) stream)
    (princ " clauses" stream)))

(defun decode-dp-clause (clause &optional decode-fun)
  (let ((result nil) result-last)
    (dolist (atom (dp-clause-negative-literals clause))
      (unless (dp-atom-value atom)
        (collect (let ((atom (if decode-fun
                                 (funcall decode-fun atom)
                                 (dp-atom-name atom))))
                   (cond
                    ((numberp atom)
                     (- atom))
                    (t
                     (list 'not atom))))
                 result)))
    (dolist (atom (dp-clause-positive-literals clause))
      (unless (dp-atom-value atom)
        (collect (if decode-fun
                     (funcall decode-fun atom)
                     (dp-atom-name atom))
                 result)))
    result))

(defun print-dp-clause (clause &optional stream depth)
  (declare (ignore depth))
  (prin1 (decode-dp-clause clause) stream)
  clause)

(defun print-dp-atom (atom &optional stream depth)
  (declare (ignore depth))
  (prin1 (dp-atom-name atom) stream)
  atom)

(defun integer-width (n)
  (let (w)
    (cond
     ((minusp n)
      (setq n (- n))
      (setq w 1))
     (t
      (setq w 0)))
    (loop
      (cond
       ((eql 0 n)
        (return w))
       (t
        (setq n (truncate n 10))
        (incf w))))))

(defun print-dp-trace-line (depth atom value branch-count xp chosen-clause)
  (fresh-line)
  (cond
    (branch-count
     (princ branch-count)
     (dotimes (i (- 12 (integer-width branch-count)))
       (declare (ignorable i))
       (princ " ")))
    (t
     (princ "            ")))
  (dotimes (i depth)
    (princ (if (eql 4 (rem i 5)) "| " ": ")))
  (princ (dp-atom-name atom))
  (princ (if (eq :true value) "=true" "=false"))
  (princ (if xp "! " " "))
  (when chosen-clause
    (princ "for clause ")
    (princ chosen-clause)
    (princ " ")))

(defun print-dp-choice-points (clause-set time)
  (let ((atoms nil))
    (dolist (atom (dp-clause-set-atoms clause-set))
      (when (dp-atom-choice-point atom)
        (push atom atoms)))
    (fresh-line)
    (terpri)
    (cond
     ((null atoms)
      (princ "--- no current choice points "))
     (t
      (format t "--- ~D current choice point~:P:" (length atoms))
      (let ((depth 0))
        (dolist (atom (sort atoms #'< :key #'dp-atom-choice-point))
          (print-dp-trace-line
           depth atom (dp-atom-value atom) (dp-atom-choice-point atom) nil nil)
          (incf depth)))))
    (format t "~%--- after ~,1F seconds " time)))

#-SNARK (defvar float-internal-time-units-per-second (float internal-time-units-per-second))

(defun run-time-since (start-time)
  (- (/ (get-internal-run-time) float-internal-time-units-per-second) start-time))

(defmacro first-nontrue-atom (atoms)
  `(dolist (atom ,atoms)
     (unless (eq :true (dp-atom-value atom))
       (return atom))))

(defmacro first-nonfalse-atom (atoms)
  `(dolist (atom ,atoms)
     (unless (eq :false (dp-atom-value atom))
       (return atom))))

(defmacro first-unassigned-atom (atoms)
  `(dolist (atom ,atoms)
     (unless (dp-atom-value atom)
       (return atom))))

(defmacro nth-unassigned-atom (n atoms)
  `(let ((k ,n))
     (dolist (atom ,atoms)
       (unless (dp-atom-value atom)
         (if (eql 0 k)
             (return atom)
             (decf k))))))

(defun mark-used-atoms (clause)
  (let (c)
    (dolist (atom (dp-clause-positive-literals clause))
      (unless (dp-atom-used-in-refutation-p atom)
	(setf (dp-atom-used-in-refutation-p atom) t)
	(when (setq c (dp-atom-derived-from-clause atom))
	  (mark-used-atoms c))))
    (dolist (atom (dp-clause-negative-literals clause))
      (unless (dp-atom-used-in-refutation-p atom)
	(setf (dp-atom-used-in-refutation-p atom) t)
	(when (setq c (dp-atom-derived-from-clause atom))
	  (mark-used-atoms c))))))

(defvar *last-tried-atom*)

(defun assign-atoms (assignments)
  ;; apply assigments and do all resulting unit propagation
  ;; if result is unsatisfiable, undo all changes and return :unsatisfiable
  ;; otherwise return list of assignments made; unassign-atoms can undo
  ;; the assignments
  (let ((compute-more-units *more-units-function*))
    (macrolet
      ((undo-assignments-and-exit (&optional no-assignments-for-this-atom)
	 `(progn
	    ,@(unless no-assignments-for-this-atom
		(list `(unassign-atom atom clause)))
	    (unassign-atoms assignments-done)
	    (if *dependency-check*
                (do ((a assignments (dp-atom-next a)))
                    ((null a))
                  (setf (dp-atom-value a) nil)
                  (setf (dp-atom-derived-from-clause a) nil)
                  (setf (dp-atom-used-in-refutation-p a) nil))
                (do ((a assignments (dp-atom-next a)))
                    ((null a))
                  (setf (dp-atom-value a) nil)))
	    #+ignore
	    (incf *assignment-count* assignment-count)
	    (return-from assign-atoms :unsatisfiable)))
       (new-unit-clause (val)
	 `(let ((at ,(if (eq :true val)
			 `(first-nonfalse-atom
			    (dp-clause-positive-literals clause))
			 `(first-nontrue-atom
			    (dp-clause-negative-literals clause)))))
	    (cond
	      ((null at)
	       (when *dependency-check*
		 (mark-used-atoms clause))
	       (undo-assignments-and-exit))
	      ((null (dp-atom-value at))
	       (setq compute-more-units *more-units-function*)
	       (setf (dp-atom-value at) ,val)
	       (when *dependency-check*
		 (setf (dp-atom-derived-from-clause at) clause))
	       ,@(if (eq :true val)		;true assignments at front, false at end
		     `((setf (dp-atom-next at) assignments)
		       (when (null assignments)
			 (setq last-assignment at))
		       (setq assignments at))
		     `((setf (dp-atom-next at) nil)
		       (if (null assignments)
			   (setq assignments at)
			   (setf (dp-atom-next last-assignment) at))
		       (setq last-assignment at)))))))
       (resolve (val)
	 `(dolist (clause ,(if (eq :true val)
                               `(dp-atom-contained-negatively-clauses atom)
                               `(dp-atom-contained-positively-clauses atom)))
            (cond
             ((eql 0
                   (setq k1 (decf ,(if (eq :true val)
                                       `(dp-clause-number-of-unresolved-negative-literals
                                         clause)
                                       `(dp-clause-number-of-unresolved-positive-literals
                                         clause)))))
              (cond
               ((eql 0
                     (setq k2 ,(if (eq :true val)
                                   `(dp-clause-number-of-unresolved-positive-literals
                                     clause)
                                   `(dp-clause-number-of-unresolved-negative-literals
                                     clause))))
                (when *dependency-check*
                  (mark-used-atoms clause))
                (undo-assignments-and-exit))
               ((eql 1 k2)
                (new-unit-clause ,(if (eq :true val) :true :false)))))
             ((and (eql 1 k1)
                   (eql 0
                        ,(if (eq :true val)
                             `(dp-clause-number-of-unresolved-positive-literals clause)
                             `(dp-clause-number-of-unresolved-negative-literals clause))))
              (new-unit-clause ,(if (eq :true val) :false :true)))))))
      (let ((k1 0) (k2 0) #+ignore (assignment-count 0) (assignments-done nil)
	    (*last-tried-atom* nil)		;used by lookahead
	    atom value last-assignment)
	(declare (fixnum k1 k2 #+ignore assignment-count))
	(loop
          (when assignments			;find last assignment
            (do ((a assignments next)
                 (next (dp-atom-next assignments) (dp-atom-next next)))
                ((null next)
                 (setq last-assignment a))))
          (loop
            (when (null assignments)
              (return))
            (setq atom assignments)
            (setq assignments (dp-atom-next atom))
            (setq value (dp-atom-value atom))
            #+ignore
            (incf assignment-count)
            (if (eq value :true)
                (resolve :true)
                (resolve :false))
            (setf (dp-atom-next atom) assignments-done)
            (setq assignments-done atom))
          (cond				;find more assignments?
           ((and compute-more-units
                 (multiple-value-bind (result call-again)
			              (funcall compute-more-units *clause-set*)
                   (cond
                    ((eq result :unsatisfiable)
                     (undo-assignments-and-exit t))
                    (t
                     (unless call-again
                       (setq compute-more-units nil))
                     (setq assignments result)))))
            )				;make the new assignments
           (t
            (return))))			;no more assignments
	#+ignore
	(incf *assignment-count* assignment-count)
	assignments-done))))

(defun unassign-atom (atom stop-clause)
  (when *dependency-check*
    (setf (dp-atom-derived-from-clause atom) nil)
    (setf (dp-atom-used-in-refutation-p atom) nil))
  (if (eq :true (dp-atom-value atom))
      (dolist (clause (dp-atom-contained-negatively-clauses atom))
        (incf (dp-clause-number-of-unresolved-negative-literals clause))
        (when (eq stop-clause clause)
          (return)))
      (dolist (clause (dp-atom-contained-positively-clauses atom))
        (incf (dp-clause-number-of-unresolved-positive-literals clause))
        (when (eq stop-clause clause)
          (return))))
  (setf (dp-atom-value atom) nil))

(defun unassign-atoms (assignments)
  (do ((atom assignments (dp-atom-next atom)))
      ((null atom))
    (when *dependency-check*
      (setf (dp-atom-derived-from-clause atom) nil)
      (setf (dp-atom-used-in-refutation-p atom) nil))
    (if (eq :true (dp-atom-value atom))
        (dolist (clause (dp-atom-contained-negatively-clauses atom))
          (incf (dp-clause-number-of-unresolved-negative-literals clause)))
        (dolist (clause (dp-atom-contained-positively-clauses atom))
          (incf (dp-clause-number-of-unresolved-positive-literals clause))))
    (setf (dp-atom-value atom) nil)))

(defun find-unit-clauses (clause-set)
  ;; this is only used to find unit clauses in the initial set of clauses,
  ;; assign-atoms detects and simplifies by derived unit clauses
  (let ((assignments nil))
    (macrolet
      ((add-assignment (atom value)
	 `(let ((atom ,atom))
	    (cond
             ((null atom)
              (do ((a assignments (dp-atom-next a)))
                  ((null a))
                (setf (dp-atom-value a) nil)
                (setf (dp-atom-derived-from-clause a) nil))
              (return-from find-unit-clauses :unsatisfiable))
             ((null (dp-atom-value atom))
              (setf (dp-atom-value atom) ,value)
              (setf (dp-atom-derived-from-clause atom) clause)
              (setf (dp-atom-next atom) assignments)
              (setq assignments atom))))))
      (do ((clause (dp-clause-set-p-clauses clause-set) (dp-clause-next clause)))
          ((null clause))
        (when (eql 1 (dp-clause-number-of-unresolved-positive-literals clause))
          (add-assignment (first-nonfalse-atom (dp-clause-positive-literals clause)) :true)))
      (do ((clause (dp-clause-set-n-clauses clause-set) (dp-clause-next clause)))
          ((null clause))
        (when (eql 1 (dp-clause-number-of-unresolved-negative-literals clause))
          (add-assignment (first-nontrue-atom (dp-clause-negative-literals clause)) :false))))
    assignments))

(defun choose-an-atom-of-a-shortest-clause* (clause-set positive option randomly)
  ;; assume every clause has at least two literals
  ;; return :satisfiable if there are no more (positive) clauses
  (let ((shortest-length 10000) (length 0) (chosen-clause nil)
	(chosen-atom nil) (nfound 0) (noccurrences 0))
    (declare (fixnum shortest-length length))
    (macrolet
      ((check-clause ()
	 `(progn
	    (setq length (if positive
			     (dp-clause-number-of-unresolved-positive-literals
			       clause)
			     (+ (dp-clause-number-of-unresolved-positive-literals
				  clause)
				(dp-clause-number-of-unresolved-negative-literals
				  clause))))
	    (when (and (if (and (eq :none option) (not randomly))
                           (> shortest-length length 1)
                           (>= shortest-length length 2))
		       (not (clause-contains-true-positive-literal clause))
		       (or positive (not (clause-contains-true-negative-literal clause))))
	      (ecase option
		(:none
		  (if randomly
		      (cond
			((eql length shortest-length)
			 (when (eql 0 (random (incf nfound)))
			   (setq chosen-clause clause)))
			(t
			 (setq chosen-clause clause)
			 (setq shortest-length length)
			 (setq nfound 1)))
		      (cond
			((eql 2 length)
			 (return-from choose-an-atom-of-a-shortest-clause*
			   (cond
			     ((setq chosen-atom (first-unassigned-atom
						  (dp-clause-positive-literals clause)))
			      (values chosen-atom :true :false clause))
			     (t
			      (setq chosen-atom (first-unassigned-atom
						  (dp-clause-negative-literals clause)))
			      (values chosen-atom :false :true clause)))))
			(t
			 (setq chosen-clause clause)
			 (setq shortest-length length)))))
		(:with-most-occurrences
		  (unless (eql length shortest-length)
		    (setq shortest-length length)
		    (setq noccurrences 0))
		  (dolist (atom (dp-clause-positive-literals clause))
		    (when (null (dp-atom-value atom))
		      (let ((c (dp-atom-number-of-occurrences atom)))
			(cond
			  ((and randomly (eql c noccurrences))
			   (when (eql 0 (random (incf nfound)))
			     (setq chosen-clause clause)
			     (setq chosen-atom atom)))
			  ((> c noccurrences)
			   (setq chosen-clause clause)
			   (setq chosen-atom atom)
			   (setq noccurrences c)
			   (setq nfound 1))))))
		  (unless positive
		    (dolist (atom (dp-clause-negative-literals clause))
		      (when (null (dp-atom-value atom))
			(let ((c (dp-atom-number-of-occurrences atom)))
			  (cond
			    ((eql c noccurrences)
			     (when (eql 0 (random (incf nfound)))
			       (setq chosen-clause clause)
			       (setq chosen-atom atom)))
			    ((> c noccurrences)
			     (setq chosen-clause clause)
			     (setq chosen-atom atom)
			     (setq noccurrences c)
			     (setq nfound 1)))))))))))))
      (do ((clause (dp-clause-set-p-clauses clause-set) (dp-clause-next clause)))
          ((null clause))
        (check-clause))
      (do ((clause (dp-clause-set-m2-clauses clause-set) (dp-clause-next clause)))
          ((null clause))
        (when (or (not positive) (eql 0 (dp-clause-number-of-unresolved-negative-literals clause)))
          (check-clause)))
      (unless positive
        (do ((clause (dp-clause-set-m1-clauses clause-set) (dp-clause-next clause)))
            ((null clause))
          (check-clause))
        (do ((clause (dp-clause-set-n-clauses clause-set) (dp-clause-next clause)))
            ((null clause))
          (check-clause)))
      (cond
	(chosen-clause
	 (case option
	   (:none
	     (if randomly
		 (let ((n (random shortest-length)))
		   (if positive
		       (values (nth-unassigned-atom
				 n (dp-clause-positive-literals chosen-clause))
			       :true :false chosen-clause)
		       (let ((m (dp-clause-number-of-unresolved-positive-literals chosen-clause)))
			 (if (< n m)
			     (values (nth-unassigned-atom
				       n (dp-clause-positive-literals chosen-clause))
				     :true :false chosen-clause)
			     (values (nth-unassigned-atom
				       (- n m) (dp-clause-negative-literals chosen-clause))
				     :false :true chosen-clause)))))
		 (cond
		   ((setq chosen-atom (first-unassigned-atom
					(dp-clause-positive-literals chosen-clause)))
		    (values chosen-atom :true :false chosen-clause))
		   (t
		    (setq chosen-atom (first-unassigned-atom
					(dp-clause-negative-literals chosen-clause)))
		    (values chosen-atom :false :true chosen-clause)))))
	   (:with-most-occurrences
	     (if (or positive
		     (member chosen-atom
			     (dp-clause-positive-literals chosen-clause)))
		 (values chosen-atom :true :false chosen-clause)
		 (values chosen-atom :false :true chosen-clause)))))
	((and positive (not *minimal-models-suffice*))
	 (choose-an-atom-of-a-shortest-clause* clause-set nil option randomly))
	(t
	 :satisfiable)))))

(defun choose-an-atom-of-a-shortest-clause (clause-set)
  (choose-an-atom-of-a-shortest-clause* clause-set nil :none nil))

(defun choose-an-atom-of-a-shortest-clause-randomly (clause-set)
  (choose-an-atom-of-a-shortest-clause* clause-set nil :none t))

(defun choose-an-atom-of-a-shortest-clause-with-most-occurrences (clause-set)
  (choose-an-atom-of-a-shortest-clause* clause-set nil :with-most-occurrences nil))

(defun choose-an-atom-of-a-shortest-clause-with-most-occurrences-randomly (clause-set)
  (choose-an-atom-of-a-shortest-clause* clause-set nil :with-most-occurrences t))

(defun choose-an-atom-of-a-shortest-positive-clause (clause-set)
  (choose-an-atom-of-a-shortest-clause* clause-set t :none nil))

(defun choose-an-atom-of-a-shortest-positive-clause-randomly (clause-set)
  (choose-an-atom-of-a-shortest-clause* clause-set t :none t))

(defun choose-an-atom-of-a-shortest-positive-clause-with-most-occurrences (clause-set)
  (choose-an-atom-of-a-shortest-clause* clause-set t :with-most-occurrences nil))

(defun choose-an-atom-of-a-shortest-positive-clause-with-most-occurrences-randomly (clause-set)
  (choose-an-atom-of-a-shortest-clause* clause-set t :with-most-occurrences t))

(defun fix-dp-clause-set (clause-set)
  ;; restores a clause-set to its original state if the user aborts out of dp-satisfiable-p
  (assert-dp-clause-set-p clause-set)
  (dolist (atom (dp-clause-set-atoms clause-set))
    (setf (dp-atom-value atom) nil)
    (setf (dp-atom-derived-from-clause atom) nil)
    (setf (dp-atom-used-in-refutation-p atom) nil)
    (setf (dp-atom-choice-point atom) nil))
  (do ((clause (dp-clause-set-p-clauses clause-set) (dp-clause-next clause)))
      ((null clause))
    (setf (dp-clause-number-of-unresolved-positive-literals clause)
          (length (dp-clause-positive-literals clause))))
  (do ((clause (dp-clause-set-n-clauses clause-set) (dp-clause-next clause)))
      ((null clause))
    (setf (dp-clause-number-of-unresolved-negative-literals clause)
          (length (dp-clause-negative-literals clause))))
  (do ((clause (dp-clause-set-m1-clauses clause-set) (dp-clause-next clause)))
      ((null clause))
    (setf (dp-clause-number-of-unresolved-positive-literals clause) 1)
    (setf (dp-clause-number-of-unresolved-negative-literals clause)
          (length (dp-clause-negative-literals clause))))
  (do ((clause (dp-clause-set-m2-clauses clause-set) (dp-clause-next clause)))
      ((null clause))
    (setf (dp-clause-number-of-unresolved-positive-literals clause)
          (length (dp-clause-positive-literals clause)))
    (setf (dp-clause-number-of-unresolved-negative-literals clause)
          (length (dp-clause-negative-literals clause))))
  nil)

(defun checkpoint-dp-clause-set (clause-set)
  ;; creates a checkpoint record for clause-set to allow later clause insertions to be undone
  ;; and returns the level of the new checkpoint
  (assert-dp-clause-set-p clause-set)
  (push (list nil					;checkpointed atoms
	      (dp-clause-set-number-of-clauses clause-set)
	      (dp-clause-set-number-of-literals clause-set)
	      (dp-clause-set-p-clauses-last clause-set)
	      (dp-clause-set-n-clauses-last clause-set)
	      (dp-clause-set-m1-clauses-last clause-set)
	      (dp-clause-set-m2-clauses-last clause-set))
	(dp-clause-set-checkpoints clause-set))    
  (incf (dp-clause-set-checkpoint-level clause-set)))

(defun restore-dp-clause-set (clause-set)
  ;; restores a clause-set to an earlier state undoing effects of clause insertions
  (assert-dp-clause-set-p clause-set)
  (cl:assert (not (eql 0 (dp-clause-set-checkpoint-level clause-set))) ()
	     "Clause set has no checkpoint.")
  (let ((l (first (dp-clause-set-checkpoints clause-set))))
    (dolist (atom (prog1 (first l) (setf (first l) nil) (setq l (rest l))))
      (restore-dp-atom atom))
    (setf (dp-clause-set-number-of-clauses clause-set) (pop l))
    (setf (dp-clause-set-number-of-literals clause-set) (pop l))
    (let ((v (pop l)))
      (cond
	(v
	 (setf (dp-clause-set-p-clauses-last clause-set) v)
	 (setf (dp-clause-next v) nil))
	(t
	 (setf (dp-clause-set-p-clauses clause-set) nil)
	 (setf (dp-clause-set-p-clauses-last clause-set) nil))))
    (let ((v (pop l)))
      (cond
	(v
	 (setf (dp-clause-set-n-clauses-last clause-set) v)
	 (setf (dp-clause-next v) nil))
	(t
	 (setf (dp-clause-set-n-clauses clause-set) nil)
	 (setf (dp-clause-set-n-clauses-last clause-set) nil))))
    (let ((v (pop l)))
      (cond
	(v
	 (setf (dp-clause-set-m1-clauses-last clause-set) v)
	 (setf (dp-clause-next v) nil))
	(t
	 (setf (dp-clause-set-m1-clauses clause-set) nil)
	 (setf (dp-clause-set-m1-clauses-last clause-set) nil))))
    (let ((v (first l)))
      (cond
	(v
	 (setf (dp-clause-set-m2-clauses-last clause-set) v)
	 (setf (dp-clause-next v) nil))
	(t
	 (setf (dp-clause-set-m2-clauses clause-set) nil)
	 (setf (dp-clause-set-m2-clauses-last clause-set) nil)))))
  nil)

(defun uncheckpoint-dp-clause-set (clause-set)
  ;; removes most recent checkpoint record
  ;; and returns the level of the removed checkpoint
  (assert-dp-clause-set-p clause-set)
  (let ((level (dp-clause-set-checkpoint-level clause-set)))
    (cl:assert (not (eql 0 level)) ()
	       "Clause set has no checkpoint.")
    (let* ((level2 (1- level))
           (checkpoint2 (dp-clause-set-checkpoints clause-set))
           (checkpoint (first checkpoint2)))
      (setq checkpoint2 (first (setf (dp-clause-set-checkpoints clause-set) (rest checkpoint2))))
      (dolist (atom (first checkpoint))
        (let ((acps (dp-atom-checkpoints atom)))
          (cond
           ((null checkpoint2)
            (setf (dp-atom-checkpoints atom) nil))
           ((eql level2 (first (second acps)))
            (setf (dp-atom-checkpoints atom) (rest acps)))
           (t
            (push atom (first checkpoint2))
            (setf (first (first acps)) level2)))))
      (setf (dp-clause-set-checkpoint-level clause-set) level2))
    level))

(defun checkpoint-dp-atom (atom clause-set)
  (let ((level (dp-clause-set-checkpoint-level clause-set)))
    (unless (eql 0 level)
      (let ((checkpoints (dp-atom-checkpoints atom)))
	(unless (eql level (first (first checkpoints)))	;already checkpointed
	  (push atom (first (first (dp-clause-set-checkpoints clause-set))))
	  (setf (dp-atom-checkpoints atom)
		(cons (list level
			    (dp-atom-contained-positively-clauses atom)
			    (dp-atom-contained-negatively-clauses atom)
			    (dp-atom-number-of-occurrences atom))
		      checkpoints)))))))

(defun restore-dp-atom (atom)
  (let ((l (rest (pop (dp-atom-checkpoints atom)))))
    (setf (dp-atom-contained-positively-clauses atom) (pop l))
    (setf (dp-atom-contained-negatively-clauses atom) (pop l))
    (setf (dp-atom-number-of-occurrences atom) (first l))))

;;; lookahead-true, lookahead-false, 
;;; lookahead-true-false, lookahead-false-true
;;; can be used as more-units-function argument to dp-satisfiable-p
;;; in LDPP' to constrain search by lookahead
;;;
;;; they make trial assignments of truth values to each atom;
;;; if unit propagation demonstrates that the assignment yields an
;;; unsatisfiable set of clauses, the opposite truth value is assigned

(defvar *verbose-lookahead* nil)
(defvar *verbose-lookahead-show-count* nil)

(defun lookahead-true (clause-set)
  ;; lookahead with true trial assignments
  (lookahead* clause-set :true *verbose-lookahead*))

(defun lookahead-false (clause-set)
  ;; lookahead with false trial assignments
  (lookahead* clause-set :false *verbose-lookahead*))

(defun lookahead-true-false (clause-set)
  ;; lookahead with true trial assignments,
  ;; then lookahead with false trial assignments
  (lookahead* clause-set :true-false *verbose-lookahead*))

(defun lookahead-false-true (clause-set)
  ;; lookahead with false trial assignments,
  ;; then lookahead with true trial assignments
  (lookahead* clause-set :false-true *verbose-lookahead*))

(defun lookahead* (clause-set lookahead-values verbose)
  (let ((*more-units-function* nil)		;don't apply lookahead recursively
	(ntrials 0))
    (when verbose
      (if (null *last-tried-atom*)
	  (format t "~%LOOKAHEAD call ")
	  (format t "~%          call "))
      (format t "with ~D unassigned atoms "
	      (count-if-not #'dp-atom-value (dp-clause-set-atoms clause-set))))
    ;; initialize triable-atom slots
    (ecase lookahead-values
      (:true
	(dolist (atom (dp-clause-set-atoms clause-set))
	  (setf (dp-atom-true-triable atom) (null (dp-atom-value atom)))))
      (:false
	(dolist (atom (dp-clause-set-atoms clause-set))
	  (setf (dp-atom-false-triable atom) (null (dp-atom-value atom)))))
      ((:true-false :false-true)
       (dolist (atom (dp-clause-set-atoms clause-set))
	 (setf (dp-atom-true-triable atom)
	       (setf (dp-atom-false-triable atom) (null (dp-atom-value atom)))))))
    ;; continue trying assignments in order after the last successful one in *last-tried-atom*
    (dolist (value-and-pass
	      (if *last-tried-atom*
		  (case lookahead-values
		    (:true
		      '((:true  . :after-last-tried-atom)
			(:true  . :before-last-tried-atom)))
		    (:false
		      '((:false . :after-last-tried-atom)
			(:false . :before-last-tried-atom)))
		    (otherwise
		      (ecase (dp-atom-value *last-tried-atom*)
			(:false			;trying true assignments
			  '((:true  . :after-last-tried-atom)
			    (:true  . :before-last-tried-atom)
			    (:false . :atoms-in-order)))
			(:true			;trying false assignments
			  '((:false . :after-last-tried-atom)
			    (:false . :before-last-tried-atom)
			    (:true  . :atoms-in-order))))))
		  (case lookahead-values
		    (:true
		      '((:true  . :atoms-in-order)))
		    (:false
		      '((:false . :atoms-in-order)))
		    (:true-false
		      '((:true  . :atoms-in-order)
			(:false . :atoms-in-order)))
		    (otherwise
		      '((:false . :atoms-in-order)
			(:true  . :atoms-in-order))))))
      (let* ((value (car value-and-pass))
	     (pass (cdr value-and-pass))
	     (try-it (not (eq pass :after-last-tried-atom))))
	(dolist (atom (dp-clause-set-atoms clause-set))
	  (cond
	    ((and (not (eq pass :atoms-in-order))
		  (eq atom *last-tried-atom*))
	     (if try-it
		 (return)
		 (setq try-it t)))
	    ((and try-it
		  (if (eq value :true)
		      (dp-atom-true-triable atom)
		      (dp-atom-false-triable atom)))
	     (setf (dp-atom-value atom) value)
	     (setf (dp-atom-next atom) nil)
	     (let ((v (assign-atoms atom)))
	       (cond
		 ((eq v :unsatisfiable)
		  (when verbose
                    (when *verbose-lookahead-show-count*
		      (show-count (incf ntrials) t))
		    (format t "derived ~A."
			    (if (eq value :true)
				(complementary-literal (dp-atom-name atom))
				(dp-atom-name atom))))
		  (setf (dp-atom-value atom) (if (eq value :true) :false :true))
		  (setf (dp-atom-next atom) nil)
		  (setq *last-tried-atom* atom)
		  (return-from lookahead* (values atom t)))
		 (t
		  (when (and verbose *verbose-lookahead-show-count*)
		    (show-count (incf ntrials)))
		  (case lookahead-values
		    (:true
		      (do ((atom v (dp-atom-next atom)))
                          ((null atom))
                        (when (eq :true (dp-atom-value atom))
                          (setf (dp-atom-true-triable atom) nil))))
		    (:false
		      (do ((atom v (dp-atom-next atom)))
                          ((null atom))
                        (when (eq :false (dp-atom-value atom))
                          (setf (dp-atom-false-triable atom) nil))))
		    (otherwise
		      (do ((atom v (dp-atom-next atom)))
                          ((null atom))
                        (if (eq :true (dp-atom-value atom))
                            (setf (dp-atom-true-triable atom) nil)
                            (setf (dp-atom-false-triable atom) nil)))))
		  (unassign-atoms v)))))))))
    (when verbose
      (when *verbose-lookahead-show-count*
        (show-count ntrials nil t))
      (format t "failed to derive a unit clause."))
    nil))

(defun show-count-p (n)
  (dolist (v '(100000 10000 1000 100 10) t)
    (when (>= n v)
      (return (eql 0 (mod n v))))))

(defun show-count (n &optional always neg)
  (when (or always (if neg (not (show-count-p n)) (show-count-p n)))
    (princ n)
    (princ " ")))

;;; routines for translating well-formed formulas (wffs) to clause form

(defun variable-and-range-p (x)
  (and (consp x)
       (symbolp (first x))
       (not (null (first x)))
       (variable-range (rest x))))

(defun variables-and-ranges-p (x)
  (and (consp x)
       (if (consp (first x))
	   (every #'variable-and-range-p x)
	   (variable-and-range-p x))))

(defun variable-range (x &optional (range-term-values 'syntax-check))
  (cond
   ((not (consp x))
    nil)
   (t
    (case (first x)
      (=					;e.g., N = 10 or COLORS = (RED YELLOW GREEN)
       (if (eq range-term-values 'syntax-check)
           (and (or (integerp (second x)) (consp (second x)))
                (null (cddr x)))
           (list (second x))))
      (FROM					;e.g., J FROM 1 TO N EXCEPT I AND N
       (if (eq range-term-values 'syntax-check)
           (and (or (integerp (second x)) (symbolp (second x)))
                (eq 'TO (third x))
                (or (integerp (fourth x)) (symbolp (fourth x)))
                (do ((l (cddddr x) (cddr l)))
                    ((null l)
                     t)
                  (unless (and (eq (if (eq l (cddddr x)) 'EXCEPT 'AND) (first l))
                               (rest l)
                               (or (integerp (second l)) (symbolp (second l))))
                    (return nil))))
           (do ((to (range-term-value (fourth x) range-term-values x))
                (i (range-term-value (second x) range-term-values x) (1+ i))
                (result nil) result-last)
               ((> i to)
                result)
             (do ((l (cddddr x) (cddr l)))
                 ((null l)
                  (collect i result))
               (when (eql (range-term-value (second l) range-term-values x) i)
                 (return nil))))))
      (IN					;e.g., COLOR2 IN COLORS EXCEPT COLOR1
       (if (eq range-term-values 'syntax-check)	;or    COLOR2 IN COLORS AFTER COLOR1
           (and (or (consp (second x)) (symbolp (second x)))
                (or (do ((l (cddr x) (cddr l)))
                        ((null l)
                         t)
                      (unless (and (eq (if (eq l (cddr x)) 'EXCEPT 'AND) (first l))
                                   (rest l)
                                   (symbolp (second l)))
                        (return nil)))
                    (and (eq 'AFTER (first (cddr x)))
                         (rest (cddr x))
                         (symbolp (second (cddr x)))
                         (null (cddddr x)))))
           (cond
            ((null (cddr x))
             (if (consp (second x)) (second x) (range-term-value (second x) range-term-values x)))
            ((eq 'AFTER (first (cddr x)))
             (rest (member (range-term-value (second (cddr x)) range-term-values x)
                           (if (consp (second x)) (second x) (range-term-value (second x) range-term-values x))
                           :test #'equal)))
            (t
             (let ((result nil) result-last)
               (dolist (i (if (consp (second x)) (second x) (range-term-value (second x) range-term-values x)))
                 (do ((l (cddr x) (cddr l)))
                     ((null l)
                      (collect i result))
                   (when (equal (range-term-value (second l) range-term-values x) i)
                     (return nil))))
               result)))))
      (otherwise
       nil)))))

(defun range-term-value (x range-term-values range)
  (cond
    ((integerp x)
     x)
    (t
     (let ((v (assoc x range-term-values)))
       (cond
	 (v
	  (cdr v))
	 (t
	  (error "Variable ~A has no value in range ~A." x range)))))))

(defun expand-range-form (ranges wff range-term-values)
  (let ((var (first (first ranges)))
        (result nil) result-last)
    (if (null (rest ranges))
	(dolist (value (variable-range (rest (first ranges)) range-term-values))
          (collect (replace-variable-by-value-in-term var value wff) result))
	(dolist (value (variable-range (rest (first ranges)) range-term-values))
          (ncollect (expand-range-form
                     (rest ranges)
                     (replace-variable-by-value-in-term var value wff)
                     (acons var value range-term-values))
                    result)))
    result))

(defun replace-variable-by-value-in-term (var value term)
  (cond
    ((consp term)
     (let* ((u (car term))
	    (u* (replace-variable-by-value-in-term var value u))
	    (v (cdr term)))
       (if (null v)
	   (if (eq u u*)
	       term
	       (list u*))
	   (let ((v* (replace-variable-by-value-in-term var value v)))
	     (if (and (eq v v*) (eq u u*))
		 term
		 (cons u* v*))))))
    ((eq var term)
     value)
    (t	     
     term)))

#+snark (declaim (special *input-sort-wff*))

(defun wff-clauses (wff &optional map-fun)
  ;; apply map-fun to each clause in the clause form of wff
  (let ((clauses nil))
    (labels
      ((wff-kind (wff)
         (cond
          ((consp wff)
           (let ((head (first wff)))
             (case head
               (not
                (cl:assert (eql 1 (length (rest wff))) ()
                           "Wff ~A should have one argument." wff)
                head)
               ((and or)
                (cl:assert (<= 2 (length (rest wff))) ()
                           "Wff ~A should have two or more arguments." wff)
                head)
               ((implies implied-by iff xor)
                (cl:assert (eql 2 (length (rest wff))) ()
                           "Wff ~A should have two arguments." wff)
                head)
               (if
                 (cl:assert (eql 3 (length (rest wff))) ()
                            "Wff ~A should have three arguments." wff)
                 head)
               ((and-over or-over)
                (cl:assert (eql 2 (length (rest wff))) ()
                           "Wff ~A should have two arguments." wff)
                (cl:assert (variables-and-ranges-p (second wff)))
                head)
               (otherwise
                :literal))))
          (t
           :literal)))
       (wff-clauses* (wff pos lits map-fun)
	 (case (wff-kind wff)
	   (:literal
	     (let ((-wff (complementary-literal wff)))
               #+snark
               (when *input-sort-wff*
                 (declare-sort* wff))
               (unless (eq (if pos 'true 'false) wff)
	         (dolist (lit lits (funcall map-fun (if (eq (if pos 'false 'true) wff)
                                                        lits
                                                        (cons (if pos wff -wff) lits))))
		   (cond
		    ((equal lit wff)
		     (when pos
		       (funcall map-fun lits))
		     (return))
		    ((equal lit -wff)
		     (unless pos
		       (funcall map-fun lits))
		     (return)))))))
	   (not
	     (wff-clauses* (second wff) (not pos) lits map-fun))
	   (and
	     (if pos
		 (if (and lits
			  (some (lambda (arg) (member arg lits :test #'equal))
				(rest wff)))
		     (funcall map-fun lits)
		     (dolist (arg (rest wff))
		       (wff-clauses* arg t lits map-fun)))
		 (wff-clauses* (second wff) nil lits
			       (lambda (l)
                                 (wff-clauses* (if (rest (rest (rest wff)))
                                                   `(and ,@(rest (rest wff)))
                                                   (third wff))
                                               nil l map-fun)))))
	   (or
	     (if pos
		 (wff-clauses* (second wff) t lits
			       (lambda (l)
                                 (wff-clauses* (if (rest (rest (rest wff)))
                                                   `(or ,@(rest (rest wff)))
                                                   (third wff))
                                               t l map-fun)))
		 (if (and lits
			  (some (lambda (arg) (member (complementary-literal arg) lits :test #'equal))
				(rest wff)))
		     (funcall map-fun lits)
		     (dolist (arg (rest wff))
		       (wff-clauses* arg nil lits map-fun)))))
	   (implies
	     (if pos
		 (wff-clauses* (second wff) nil lits
			       (lambda (l) (wff-clauses* (third wff) t l map-fun)))
		 (progn
		   (wff-clauses* (second wff) t lits map-fun)
		   (wff-clauses* (third wff) nil lits map-fun))))
	   (implied-by
	     (if pos
		 (wff-clauses* (third wff) nil lits
			       (lambda (l) (wff-clauses* (second wff) t l map-fun)))
		 (progn
		   (wff-clauses* (third wff) t lits map-fun)
		   (wff-clauses* (second wff) nil lits map-fun))))
	   (iff
	     (if pos
		 (progn
		   (wff-clauses* (second wff) nil lits
				 (lambda (l) (wff-clauses* (third wff) t l map-fun)))
		   (wff-clauses* (second wff) t lits
				 (lambda (l) (wff-clauses* (third wff) nil l map-fun))))
		 (progn
		   (wff-clauses* (second wff) nil lits
				 (lambda (l) (wff-clauses* (third wff) nil l map-fun)))
		   (wff-clauses* (second wff) t lits
				 (lambda (l) (wff-clauses* (third wff) t l map-fun))))))
	   (xor
	     (if pos
		 (progn
		   (wff-clauses* (second wff) nil lits
				 (lambda (l) (wff-clauses* (third wff) nil l map-fun)))
		   (wff-clauses* (second wff) t lits
				 (lambda (l) (wff-clauses* (third wff) t l map-fun))))
		 (progn
		   (wff-clauses* (second wff) nil lits
				 (lambda (l) (wff-clauses* (third wff) t l map-fun)))
		   (wff-clauses* (second wff) t lits
				 (lambda (l) (wff-clauses* (third wff) nil l map-fun))))))
           (if 
             (wff-clauses* (second wff) nil lits
                           (lambda (l) (wff-clauses* (third wff) pos l map-fun)))
             (wff-clauses* (second wff) t lits
                           (lambda (l) (wff-clauses* (fourth wff) pos l map-fun))))
	   (and-over
	     (let ((wffs (expand-range-form
			   (if (consp (first (second wff))) (second wff) (list (second wff)))
			   (third wff)
			   nil)))
	       (cl:assert (not (null wffs)) ()
			  "Wff ~A expands into empty conjunction." wff)
	       (wff-clauses* (if (null (rest wffs)) (first wffs) `(and ,@wffs)) pos lits map-fun)))
	   (or-over
	     (let ((wffs (expand-range-form
			   (if (consp (first (second wff))) (second wff) (list (second wff)))
			   (third wff)
			   nil)))
	       (cl:assert (not (null wffs)) ()
			  "Wff ~A expands into empty disjunction." wff)
	       (wff-clauses* (if (null (rest wffs)) (first wffs) `(or ,@wffs)) pos lits map-fun))))))
      (wff-clauses* wff t nil
		    (lambda (lits)
                      (if map-fun
                          (funcall map-fun (reverse lits))
                          (push (reverse lits) clauses))))
      (nreverse clauses))))

(defvar *verbose-subsumption* nil)
(defvar *subsumption-show-count* nil)

(defun dp-subsumption (clause-set &optional print-summary)
  ;; eliminate subsumed clauses
  ;; also add resolvents when they subsume a parent
  (assert-unvalued-dp-clause-set-p clause-set)
  (cl:assert (eql 0 (dp-clause-set-checkpoint-level clause-set)) ()
	     "Cannot use subsumption on clause set that has a checkpoint.")
  (let ((start-time (run-time-since 0.0))
        (changed nil)
        (candidates nil)
        (count 0))
    (labels
      ((same-literal (clauses)
         (dolist (clause2 clauses)
           (let ((subsumption-mark (dp-clause-subsumption-mark clause2)))
             (cond
              ((null subsumption-mark)
               (push clause2 candidates)
               (setf (dp-clause-subsumption-mark clause2) (cons 1 0)))
              ((not (eq :subsumed subsumption-mark))
               (incf (car subsumption-mark)))))))
       (comp-literal (clauses)
         (dolist (clause2 clauses)
           (let ((subsumption-mark (dp-clause-subsumption-mark clause2)))
             (cond
              ((null subsumption-mark)
               (push clause2 candidates)
               (setf (dp-clause-subsumption-mark clause2) (cons 0 1)))
              ((not (eq :subsumed subsumption-mark))
               (incf (cdr subsumption-mark)))))))
       (resolve (clause clause2 &optional subsume-both)
         (setq changed t)
         (when *verbose-subsumption*
           (if subsume-both
             (format t "~%Resolve ~A with ~A subsuming both" clause clause2)
             (format t "~%Resolve ~A with ~A subsuming it" clause clause2)))
         (setf (dp-clause-subsumption-mark clause2) :subsumed)
         (when subsume-both
           (setf (dp-clause-subsumption-mark clause) :subsumed))
         (let ((poslits (dp-clause-positive-literals clause))
               (neglits (dp-clause-negative-literals clause))
               (poslits2 (dp-clause-positive-literals clause2))
               (neglits2 (dp-clause-negative-literals clause2))
               (resolvent-poslits nil)
               (resolvent-neglits nil))
           (when (or (null neglits2) (null (cdr poslits)))
             (psetq poslits poslits2
                    neglits neglits2
                    poslits2 poslits
                    neglits2 neglits))
           (dolist (atom poslits)
             (unless (member atom neglits2)
               (push atom resolvent-poslits)))
           (dolist (atom poslits2)
             (unless (member atom neglits)
               (pushnew atom resolvent-poslits)))
           (dolist (atom neglits)
             (unless (member atom poslits2)
               (push (list 'not atom) resolvent-neglits)))
           (dolist (atom neglits2)
             (unless (member atom poslits)
               (pushnew (list 'not atom) resolvent-neglits :key #'second)))
           (dp-insert (nconc (nreverse resolvent-poslits)
                             (nreverse resolvent-neglits))
                      clause-set)))
       (delete-clauses (first)
         (let ((nclauses 0) (nliterals 0))
           (loop
             (cond
              ((null first)
               (decf (dp-clause-set-number-of-clauses clause-set) nclauses)
               (decf (dp-clause-set-number-of-literals clause-set) nliterals)
               (return-from delete-clauses
                 (values nil nil)))
              ((eq :subsumed (dp-clause-subsumption-mark first))
               (incf nclauses)
               (incf nliterals (+ (length (dp-clause-positive-literals first))
                                  (length (dp-clause-negative-literals first))))
               (setq first (dp-clause-next first)))
              (t
               (return))))
           (let* ((last first)
                  (next (dp-clause-next last)))
             (loop
               (cond
                ((null next)
                 (decf (dp-clause-set-number-of-clauses clause-set) nclauses)
                 (decf (dp-clause-set-number-of-literals clause-set) nliterals)
                 (return-from delete-clauses
                   (values first last)))
                ((eq :subsumed (dp-clause-subsumption-mark next))
                 (incf nclauses)
                 (incf nliterals (+ (length (dp-clause-positive-literals next))
                                    (length (dp-clause-negative-literals next))))
                 (setq next (setf (dp-clause-next last) (dp-clause-next next))))
                (t
                 (setq next (dp-clause-next (setq last next)))))))))
       (subsumption (clause)
         (when *subsumption-show-count*
           (show-count (incf count)))
         (unless (eq :subsumed (dp-clause-subsumption-mark clause))
           (dolist (atom (dp-clause-positive-literals clause))
             (same-literal (rest (member clause (dp-atom-contained-positively-clauses atom))))
             (comp-literal (dp-atom-contained-negatively-clauses atom)))
           (dolist (atom (dp-clause-negative-literals clause))
             (same-literal (rest (member clause (dp-atom-contained-negatively-clauses atom))))
             (comp-literal (dp-atom-contained-positively-clauses atom)))
           (let ((length (+ (dp-clause-number-of-unresolved-positive-literals clause)
                            (dp-clause-number-of-unresolved-negative-literals clause))))
             (dolist (clause2 candidates)
               (let ((same-count (car (dp-clause-subsumption-mark clause2))))
                 (cond
                  ((eql same-count length)
                   (setq changed t)
                   (when *verbose-subsumption*
                     (format t "~%Subsume ~A by ~A" clause2 clause))
                   (setf (dp-clause-subsumption-mark clause2) :subsumed))
                  ((eql same-count (+ (dp-clause-number-of-unresolved-positive-literals clause2)
                                      (dp-clause-number-of-unresolved-negative-literals clause2)))
                   (setq changed t)
                   (when *verbose-subsumption*
                     (format t "~%Subsume ~A by ~A" clause clause2))
                   (setf (dp-clause-subsumption-mark clause) :subsumed)))))
             (decf length)
             (dolist (clause2 candidates)
               (let ((subsumption-mark (dp-clause-subsumption-mark clause2)))
                 (unless (eq :subsumed subsumption-mark)
                   (setf (dp-clause-subsumption-mark clause2) nil)
                   (unless (or (not (eql 1 (cdr subsumption-mark)))
                               (eq :subsumed (dp-clause-subsumption-mark clause)))
                     (let ((length2 (+ (dp-clause-number-of-unresolved-positive-literals clause2)
                                       (dp-clause-number-of-unresolved-negative-literals clause2)
                                       -1)))
                       (cond
                        ((and (eql 0 length) (eql 0 length2))
                         )				;don't make empty resolvent
                        ((eql (car subsumption-mark) length)
                         (resolve clause clause2 (eql (car subsumption-mark) length2)))
                        ((eql (car subsumption-mark) length2)
                         (resolve clause2 clause))))))))
             (setq candidates nil)))))
      (when print-summary
        (format t "~&Clause set subsumption "))
      (let ((p-clauses (make-dp-clause :next (dp-clause-set-p-clauses clause-set)))
            (n-clauses (make-dp-clause :next (dp-clause-set-n-clauses clause-set)))
            (m1-clauses (make-dp-clause :next (dp-clause-set-m1-clauses clause-set)))
            (m2-clauses (make-dp-clause :next (dp-clause-set-m2-clauses clause-set))))
        (let (next)
          (loop
            (if (setq next (dp-clause-next m1-clauses))
                (subsumption (setq m1-clauses next))
                (if (setq next (dp-clause-next n-clauses))
                    (subsumption (setq n-clauses next))
                    (if (setq next (dp-clause-next m2-clauses))
                        (subsumption (setq m2-clauses next))
                        (if (setq next (dp-clause-next p-clauses))
                            (subsumption (setq p-clauses next))
                            (return))))))))
      (when *subsumption-show-count*
        (show-count count nil t))
      (when changed
        (dolist (atom (dp-clause-set-atoms clause-set))
          (let ((n 0))
            (setf (dp-atom-contained-positively-clauses atom)
                  (delete-if (lambda (clause)
                               (when (eq :subsumed (dp-clause-subsumption-mark clause))
                                 (incf n)))
                             (dp-atom-contained-positively-clauses atom)))
            (setf (dp-atom-contained-negatively-clauses atom)
                  (delete-if (lambda (clause)
                               (when (eq :subsumed (dp-clause-subsumption-mark clause))
                                 (incf n)))
                             (dp-atom-contained-negatively-clauses atom)))
            (decf (dp-atom-number-of-occurrences atom) n)))
        (multiple-value-bind (first last)
            (delete-clauses (dp-clause-set-p-clauses clause-set))
          (setf (dp-clause-set-p-clauses clause-set) first)
          (setf (dp-clause-set-p-clauses-last clause-set) last))
        (multiple-value-bind (first last)
            (delete-clauses (dp-clause-set-n-clauses clause-set))
          (setf (dp-clause-set-n-clauses clause-set) first)
          (setf (dp-clause-set-n-clauses-last clause-set) last))
        (multiple-value-bind (first last)
            (delete-clauses (dp-clause-set-m1-clauses clause-set))
          (setf (dp-clause-set-m1-clauses clause-set) first)
          (setf (dp-clause-set-m1-clauses-last clause-set) last))
        (multiple-value-bind (first last)
            (delete-clauses (dp-clause-set-m2-clauses clause-set))
          (setf (dp-clause-set-m2-clauses clause-set) first)
          (setf (dp-clause-set-m2-clauses-last clause-set) last)))
      (when print-summary
        (format t "took ~,1F seconds"
                (run-time-since start-time))
        (cond
         (changed
          (princ ".")
          (dp-count clause-set t))
         (t
          (princ " - no change."))))
      nil)))

;;; Examples.
;;; Clauses are represented by lists of literals.
;;; Atomic formulas can be represented by numbers > 0 or S-expressions.
;;; Example literals and their negations include
;;;   3                -3
;;;   P                (NOT P)
;;;   (SUBSET A B)     (NOT (SUBSET A B))
;;; Clauses are added to a set of clauses by DP-INSERT.
;;; Tautologies and duplicate literals are automatically eliminated.
;;;
;;; Formulas can be converted to clause form and inserted by DP-INSERT-WFF.
;;;
;;; DP-SATISFIABLE-P is the main function used to test a set of clauses
;;; for satisfiability.  Its input is created by calls on DP-INSERT that
;;; add single clauses to a set of clauses.
;;;
;;; DP-OUTPUT-CLAUSES-TO-FILE can be used to write a set of clauses to a file.
;;; DP-SATISFIABLE-FILE-P can then be used.
;;;
;;; An alternate file format that can be specified by the :dimacs-cnf-format
;;; flag represents literals by positive or negative integers and clauses by
;;; a sequence of integers separated by zeros.  For example, a file might contain
;;; 1 2 0 1 -2 0 -1 2 0 -1 -2 0 to represent the clauses (1 2) (1 -2) (-1 2) (-1 -2).
;;; This is the form used by McCune's ANL-DP for propositional problems
;;; and is also the CNF format for SAT problems suggested by DIMACS.

(defun allways-3-problem (&rest options)
  ;; all signed combinations of three propositions
  ;; this is not satisfiable
  ;; you can omit some of the clauses to make the set
  ;; satisfiable and observe dp-satisfiable-p's behavior
  (let ((clause-set (make-dp-clause-set)))
    (dp-insert '(1 2 3) clause-set)
    (dp-insert '(1 2 -3) clause-set)
    (dp-insert '(1 -2 3) clause-set)
    (dp-insert '(1 -2 -3) clause-set)
    (dp-insert '(-1 2 3) clause-set)
    (dp-insert '(-1 2 -3) clause-set)
    (dp-insert '(-1 -2 3) clause-set)
    (dp-insert '(-1 -2 -3) clause-set)
;;  could have been inserted as one or more wffs instead:
;;  (dp-insert-wff '(or 1
;;			(and (or 2 3)
;;			     (implies 3 2)
;;			     (implies 2 3)
;;			     (or (not 2) (not 3))))
;;		   clause-set)
;;  (dp-insert-wff '(or -1
;;			(and (or 2 3)
;;			     (iff 2 3)
;;			     (not (and 2 3))))
;;		   clause-set)
;;  (dp-count clause-set t)
;;  (dp-clauses #'print clause-set)
    (apply #'dp-satisfiable-p clause-set options)))

(defun pigeonhole-problem (nholes &rest options)
  (apply #'dp-satisfiable-p
	 (pigeonhole-problem-clauses nholes (if (numberp (first options)) (first options) (1+ nholes)))
	 (append (if (numberp (first options)) (rest options) options) (list :dependency-check nil))))

(defun queens-problem (n &rest options)
  (apply #'dp-satisfiable-p
	 (queens-problem-clauses n)
	 (append options (list :atom-choice-function #'choose-an-atom-of-a-shortest-positive-clause-with-most-occurrences))))

(defun graph-coloring-problem (colors n &rest options)
  (apply #'dp-satisfiable-p
	 (graph-coloring-problem-clauses colors n)
	 options))

(defun pigeonhole-problem-clauses (nholes &optional (nobjects (1+ nholes)))
  (let ((clause-set (make-dp-clause-set)))
    #|
    (loop for i from 1 to nobjects
	  do (dp-insert (loop for j from 1 to nholes
			      collect `(p ,i ,j))
		        clause-set))
    (loop for j from 1 to nholes
	  do (loop for i1 from 1 to (1- nobjects)
		   do (loop for i2 from (1+ i1) to nobjects
		            do (dp-insert (list `(not (p ,i1 ,j))
				                `(not (p ,i2 ,j)))
				          clause-set))))
    |#
    ;; the methods above and below yield the same set of clauses
    (dp-insert-wff `(and
		      (and-over (i from 1 to ,nobjects)
			(or-over (j from 1 to ,nholes)
			  (p i j)))
		      (and-over ((j from 1 to ,nholes)
				 (i1 from 1 to ,nobjects except ,nobjects)
				 (i2 from i1 to ,nobjects except i1))
			(or (not (p i1 j)) (not (p i2 j)))))
		   clause-set)
    clause-set))

(defun queens-problem-clauses (n)
  (let ((clause-set (make-dp-clause-set)))
    (loop for i from 1 to n
	  do (dp-insert (loop for j from 1 to n
			      collect `(q ,i ,j))
		        clause-set))
    (loop for j from 1 to n
          do (dp-insert (loop for i from 1 to n
                              collect `(q ,i ,j))
                        clause-set))
    (loop for i from 1 to n
	  do (loop for j from 1 to (1- n)
		   do (loop for k from (1+ j) to n
		            do (dp-insert (list `(not (q ,i ,j))
				                `(not (q ,i ,k)))
				          clause-set)
                               (dp-insert (list `(not (q ,j ,i))
				                `(not (q ,k ,i)))
				          clause-set))))
    (loop for i1 from 1 to (1- n)
	  do (loop for i2 from (1+ i1) to n
		   as d = (- i2 i1)
		   do (loop for j1 from 1 to n
		            when (>= (- j1 d) 1)
			      do (dp-insert (list `(not (q ,i1 ,j1))
					          `(not (q ,i2 ,(- j1 d))))
				            clause-set)
		            when (<= (+ j1 d) n)
			      do (dp-insert (list `(not (q ,i1 ,j1))
					          `(not (q ,i2 ,(+ j1 d))))
				            clause-set))))
    clause-set))

(defun graph-coloring-problem-clauses (colors n)
  ;; a Ramsey problem:
  ;; can the edges of a complete graph with n nodes be colored
  ;; with colors so that there is no isochromatic triangle?
  ;;
  ;; (graph-coloring-problem '(red green) 5) is solvable but
  ;; (graph-coloring-problem '(red green) 6) is not
  ;;
  ;; (graph-coloring-problem '(red green blue) 16) is solvable but
  ;; (graph-coloring-problem '(red green blue) 17) is not
  ;; but this is hard to show (symmetry elimination would help)
  (let ((clause-set (make-dp-clause-set)))
    (dp-insert-wff `(and-over ((i from 1 to ,n)
			       (j from i to ,n except i))
			      (or-over (c in ,colors) (c i j)))
		   clause-set)
    (dp-insert-wff `(and-over ((i from 1 to ,n)
			       (j from i to ,n except i)
			       (c1 in ,colors)
			       (c2 in ,colors after c1))
			      (not (and (c1 i j) (c2 i j))))
		   clause-set)
    (dp-insert-wff `(and-over ((i from 1 to ,n)
			       (j from i to ,n except i)
			       (k from j to ,n except j)
			       (c in ,colors))
			      (not (and (c i j) (c i k) (c j k))))
		   clause-set)
;;  (dp-clauses #'print clause-set)
    clause-set))

;;; davis-putnam3.lisp EOF
