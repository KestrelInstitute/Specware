;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: main.lisp
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
;;; Portions created by the Initial Developer are Copyright (C) 1981-2003.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :snark)

(declaim
  (special
    ordering-is-total
    *printing-deleted-messages*
    *agenda*
    *agendas*
    ))

(defvar options-print-mode t)

(defvar *snark-is-running* nil)
(defvar *agenda-of-false-wffs-to-process*)
(defvar *agenda-of-new-embeddings-to-process*)
(defvar *agenda-of-input-wffs-to-process*)
(defvar *agenda-of-backward-simplifiable-wffs-to-process*)
(defvar *agenda-of-other-wffs-to-process*)

(defvar time-mark)
(defvar *manual-ordering-results*)

(defvar critique-options t)

(defvar *break-snark?* nil)			;ttp

(defvar *interactive? nil			;ttp
  "When T, an inference rule has been called interactively, so typically
   it is not supposed to form all consequences; just with the one in *ROW2*.")

(defvar *row2* nil				;ttp
  "the second argument to an interactive inference rule.")

(defvar *propositional-abstraction-of-input-wffs*)

(defvar *negative-hyperresolution*)

(defvar *find-else-substitution* nil)

(defvar *processing-row* nil)

(declaim
  (special
    rewrite-strategy
    clause-subsumption
    subsumption-mark
    *rewrites-used*
    *symbols-in-symbol-table*
    *skolem-function-alist*
    ))

(defvar recursive-unstore nil)

(defun critique-options ()
  (unless options-have-been-critiqued
    (when (print-options-when-starting?)
      (print-options))
    (unless (or (use-resolution?)
                (use-hyperresolution?)
                (use-negative-hyperresolution?)
                (use-ur-resolution?)
                (use-paramodulation?)
                (use-ur-pttp?)
                (use-resolve-code?))
      (warn "Neither resolution nor paramodulation are specified."))
    (setq options-have-been-critiqued t))
  nil)

(defvar *number-of-given-rows* 0)
(defvar *number-of-backward-eliminated-rows* 0)
(defvar *number-of-agenda-full-deleted-rows* 0)
(defvar *number-of-rewrites* 0)
(declaim (type integer *number-of-given-rows* *number-of-backward-eliminated-rows*)
         (type integer *number-of-agenda-full-deleted-rows* *number-of-rewrites*))

(defun clear-statistics ()
  (setq *row-count* 0)
  (setq *number-of-rows* 0)
  (setq *number-of-given-rows* 0)
  (setq *number-of-backward-eliminated-rows* 0)
  (setq *number-of-agenda-full-deleted-rows* 0)
  (setq *number-of-rewrites* 0)
  nil)

(defun print-summary ()
  (terpri-comment)
  (format t "Summary of computation:")
  (let ((total-number-of-rows *row-count*))
    (terpri-comment)
    (format t "~9D formulas have been input or derived (from ~D formulas)."
	    total-number-of-rows
	    *number-of-given-rows*)
    (when (< 0 total-number-of-rows)
      (terpri-comment)
      (format t "~9D (~2D%) were retained."
	      *number-of-rows*
	      (percentage *number-of-rows* total-number-of-rows))
      (when (< 0 *number-of-rows*)
	(let ((number-of-still-kept-wffs (- *number-of-rows* *number-of-backward-eliminated-rows*))
	      (number-of-reduced-wffs (- *number-of-backward-eliminated-rows* *number-of-agenda-full-deleted-rows*)))
	  (format t "  Of these,")
          (unless (eql 0 number-of-reduced-wffs)
	    (terpri-comment)
	    (format t "~12D (~2D%) were simplified or subsumed later,"
		    number-of-reduced-wffs
		    (percentage number-of-reduced-wffs *number-of-rows*)))
          (unless (eql 0 *number-of-agenda-full-deleted-rows*)
	    (terpri-comment)
	    (format t "~12D (~2D%) were deleted later because the agenda was full,"
		    *number-of-agenda-full-deleted-rows*
		    (percentage *number-of-agenda-full-deleted-rows* *number-of-rows*)))
	  (terpri-comment)
	  (format t "~12D (~2D%) are still being kept."
		  number-of-still-kept-wffs
		  (percentage number-of-still-kept-wffs *number-of-rows*)))))
    nil))

(defun print-rewrites (&key ancestry (test (print-rows-test?)))
  (let ((rowset (make-rowset)))
    (prog->
      (retrieve-all-entries #'tme-rewrites ->* e rewrites)
      (declare (ignore e))
      (dolist rewrites ->* rewrite)
      (unless (or (null (rewrite-row rewrite))
		  (null (rewrite-condition rewrite)))
	(rowset-insert (rewrite-row rewrite) rowset)))
    (let ((*rows* rowset))
      (print-rows :ancestry ancestry :test test))))

(defvar rewrites-initialized)

(defparameter initialization-functions
  (list 'clear-statistics
        'initialize-row-contexts
        'initialize-term-hash
        'initialize-simplification-ordering-compare-equality-arguments-hash-table
        'initialize-sort-theory
        'initialize-symbol-ordering
        'initialize-symbol-table
        'initialize-propositional-abstraction-of-input-wffs
        'initialize-backward-compatibility
        'initialize-assertion-analysis
        'initialize-kif
        'clear-rewrite-cache
        'finalize-options
		))

(defun initialize (&key (verbose t))
  (cond
    (*snark-is-running*
     (error "SNARK is already running."))
    (t
     (setq time-mark (get-internal-run-time))
     (when verbose
       (format t "~&; Running on ~A at " (machine-instance)) (print-current-time))
     (initialize-numberings)
     (setq *using-sorts* nil)
     (setq *tics* nil)
     (initialize-options)
     (initialize-clocks)
     (nocomment)
     (initialize-rows)
     (initialize-constants)
     (initialize-variables)
     (setf *number-of-new-symbols* 0)
     (setf *new-symbol-prefix* (newsym-prefix))

     (setq clause-subsumption t)
     (setq subsumption-mark 0)

     (setq *manual-ordering-results* nil)
;;       (dolist (modality modalatomsigns) (intensional (car modality)))
;;       (INTENSIONAL 'ANSWER)				; ???

     (make-term-memory :indexing-method :path)
     (initialize-agendas)
     (setq rewrites-initialized nil)
;;       (store-boolean-ring-rewrites)
     (setq ordering-is-total nil)
     (setq *proof* nil)
     (dolist (fn initialization-functions)
       (funcall fn))
     nil)))

(defmacro with-input-functions-disabled (symbols &body body)
  (let ((symbol-temps (mapcar (lambda (x) (declare (ignore x)) (gensym)) symbols))
	(value-temps1 (mapcar (lambda (x) (declare (ignore x)) (gensym)) symbols))
        (value-temps2 (mapcar (lambda (x) (declare (ignore x)) (gensym)) symbols)))
    `(let ,(mapcar (lambda (symbol symbol-temp) `(,symbol-temp ,symbol)) symbols symbol-temps)
       (let (,@(mapcan (lambda (symbol-temp value-temp1 value-temp2)
                           (declare (ignorable value-temp2))
			   (list `(,value-temp1 (function-input-function ,symbol-temp))
;;                               `(,value-temp2 (function-logical-symbol-p ,symbol-temp))
                                 ))
		     symbol-temps value-temps1 value-temps2))
	 (unwind-protect
	     (progn
	       ,@(mapcan (lambda (symbol-temp)
			     (list `(setf (function-input-function ,symbol-temp) nil)
;;                                 `(setf (function-logical-symbol-p ,symbol-temp) nil)
                                   ))
			 symbol-temps)
	       ,@body)
	   ,@(mapcan (lambda (symbol-temp value-temp1 value-temp2)
                         (declare (ignorable value-temp2))
			 (list `(setf (function-input-function ,symbol-temp) ,value-temp1)
;;                             `(setf (function-logical-symbol-p ,symbol-temp) ,value-temp2)
                               ))
		     symbol-temps value-temps1 value-temps2))))))

(defun initialize-agendas ()
  (setq *agendas*
	(list
	  (setq *agenda-of-false-wffs-to-process* 
		(make-agenda :name "false wffs to process"
			     :same-item-p #'same-agenda-item-p))
	  (setq *agenda-of-new-embeddings-to-process*
		(make-agenda :name "new embeddings to process"
			     :same-item-p #'same-agenda-item-p))
	  (setq *agenda-of-input-wffs-to-process*
		(make-agenda :name "input wffs to process"
			     :same-item-p #'same-agenda-item-p))
	  (setq *agenda-of-backward-simplifiable-wffs-to-process*
		(make-agenda :name "backward simplifiable wffs to process"
			     :same-item-p #'same-agenda-item-p))
	  (setq *agenda-of-other-wffs-to-process*
		(make-agenda :name "other wffs to process"
			     :length-limit (agenda-length-before-simplification-limit?)
			     :same-item-p #'same-agenda-item-p))
	  (setq *agenda*
		(make-agenda :name "everything else"
			     :length-limit (agenda-length-limit?)
			     :length-limit-deletion-action #'unstore-agenda-item
			     :same-item-p #'same-agenda-item-p)))))

(defun initialize-rewrites ()
  (dolist (symbol *symbols-in-symbol-table*)
    (when (function-symbol-p symbol)
      (dolist (rewrite (function-rewrites symbol))
	(assert-rewrite rewrite))))
  (when (use-clausification-rewrites?)
    (declare-logical-symbol '%rewrite)
    (dolist (rewrite '((%rewrite (iff ?x ?y) (and (implies ?x ?y) (implied-by ?x ?y)))
		       (%rewrite (xor ?x ?y) (or (and ?x (not ?y)) (and (not ?x) ?y)))
		       (%rewrite (if ?x ?y ?z) (and (implies ?x ?y) (implies (not ?x) ?z)))
		       (%rewrite (implies ?x ?y) (or (not ?x) ?y))
                       (%rewrite (implied-by ?y ?x) (or ?y (not ?x)))
		       (%rewrite (or ?x (and ?y ?z)) (and (or ?x ?y) (or ?x ?z)))
		       (%rewrite (not (implies ?x ?y)) (and ?x (not ?y)))
                       (%rewrite (not (implied-by ?y ?x)) (and (not ?y) ?x))
		       (%rewrite (not (and ?x ?y)) (or (not ?x) (not ?y)))
		       (%rewrite (not (or ?x ?y)) (and (not ?x) (not ?y)))
		       (%rewrite (not (not ?x)) ?x)
		       ))
      (store-rewrite
	(renumber
	  (with-input-functions-disabled
            (*and* *or* *not* *implies* *implied-by* *iff* *xor* *if*)
            (let ((*input-proposition-variables* t))
	      (input-wff rewrite))))
	'>))))

(defun store-boolean-ring-rewrites ()
  (declare-logical-symbol '%rewrite)
  (dolist (rewrite '((%rewrite (or ?x ?y) (xor (and ?x ?y) ?x ?y))	;translate OR
		     (%rewrite (implies ?x ?y) (xor (and ?x ?y) ?x true))	;translate IMPLIES
                     (%rewrite (implied-by ?y ?x) (xor (and ?x ?y) ?x true))
		     (%rewrite (iff ?x ?y) (xor ?x ?y true))	;translate IFF
		     (%rewrite (not ?x) (xor ?x true))
;;		     (%rewrite (xor ?x false) ?x)
;;		     (%rewrite (xor ?x ?x) false)
;;		     (%rewrite (xor ?y ?x ?x) ?y)			;embedding of above
;;		     (%rewrite (and ?x true) ?x)
;;		     (%rewrite (and ?x false) false)
;;		     (%rewrite (and ?x ?x) ?x)
;;		     (%rewrite (and ?y ?x ?x) (and ?x ?y))		;embedding of above
		     (%rewrite (and ?x (xor ?y ?z)) (xor (and ?x ?y) (and ?x ?z)))
		     ))
    (store-rewrite
     (renumber
      (with-input-functions-disabled
        (*and* *or* *not* *implies* *implied-by* *iff* *xor* *if*)
        (let ((*input-proposition-variables* t))
          (input-wff rewrite))))
     '>)))

(defun renumber-row (row)
  (let ((rsubst nil))
    (let ((wff (row-wff row)))
      (multiple-value-setq (wff rsubst) (renumber wff nil rsubst))
      (setf (row-wff row) wff))
    (let ((constraint-alist (row-constraints row)))
      (when constraint-alist
	(multiple-value-setq (constraint-alist rsubst) (renumber constraint-alist nil rsubst))
	(setf (row-constraints row) constraint-alist)))
    (let ((answer (row-answer row)))
      (unless (eq false answer)
	(multiple-value-setq (answer rsubst) (renumber answer nil rsubst))
	(setf (row-answer row) answer)))
    rsubst))

(defvar *embedding-variables* nil)		;list of embedding variables

(defun embedding-variable-p (x)
  (let ((l *embedding-variables*))
    (and l (member x l :test #'eq))))

(defvar *assert-rewrite-polarity* NIL)

(defun assert-rewrite-check (wff)
  (declare (ignore wff))
;;(cl:assert (member (instantiating-direction (arg1 wff) (arg2 wff) nil) '(> <>)))
  )

(defun assert-rewrite (wff &key name (input t) (partitions (use-partitions?)))
  (cl:assert (symbolp name))
  (macrolet 
    ((make-row1 (wff)
       `(if name
            (make-row :wff ,wff
                      :number (incf *number-of-rows*)
                      :name name
                      :context (input-row-context 1 partitions)
                      :reason 'assertion
                      :input-wff input-wff)
            nil)))
  (prog->
    (if input (input-wff wff) (values wff nil (term-to-lisp wff)) -> wff dp-alist input-wff)
    (declare (ignore dp-alist))
    (cond
     ((or (equality-p wff) (and (equivalence-p wff) (atom-p (arg1 wff))))
      (renumber wff -> wff rsubst)
      (declare (ignore rsubst))
      (assert-rewrite-check wff)
      (store-rewrite wff '> (make-row1 wff)))
     ((and (implication-p wff)
           (atom-p (arg1 wff)))
      (prog->
        (make-compound *iff* (arg1 wff) (arg2 wff) -> wff1)
        (renumber wff1 -> wff1 rsubst)
        (declare (ignore rsubst))
        (quote :pos -> *assert-rewrite-polarity*)
        (assert-rewrite-check wff1)
        (store-rewrite wff1 '> (make-row1 wff))))
     ((and (implication-p wff)
           (negation-p (arg1 wff))
           (atom-p (arg1 (arg1 wff))))
      (prog->
        (make-compound *iff* (arg1 (arg1 wff)) (negate (arg2 wff)) -> wff1)
        (renumber wff1 -> wff1 rsubst)
        (declare (ignore rsubst))
        (quote :neg -> *assert-rewrite-polarity*)
        (assert-rewrite-check wff1)
        (store-rewrite wff1 '> (make-row1 wff))))
     ((and (reverse-implication-p wff)
           (atom-p (arg1 wff)))
      (prog->
        (make-compound *iff* (arg1 wff) (arg2 wff) -> wff1)
        (renumber wff1 -> wff1 rsubst)
        (declare (ignore rsubst))
        (quote :neg -> *assert-rewrite-polarity*)
        (assert-rewrite-check wff1)
        (store-rewrite wff1 '> (make-row1 wff))))
     ((and (reverse-implication-p wff)
           (negation-p (arg1 wff))
           (atom-p (arg1 (arg1 wff))))
      (prog->
        (make-compound *iff* (arg1 (arg1 wff)) (negate (arg2 wff)) -> wff1)
        (renumber wff1 -> wff1 rsubst)
        (declare (ignore rsubst))
        (quote :pos -> *assert-rewrite-polarity*)
        (assert-rewrite-check wff1)
        (store-rewrite wff1 '> (make-row1 wff))))
     ((and (conjunction-p wff)
           (implication-p (arg1 wff))
           (implication-p (arg2 wff))
           (equal-p (arg1 (arg1 wff)) (arg2 (arg2 wff)))
           (atom-p (arg1 (arg1 wff))))
      (prog->
        (make-compound *iff* (arg1 (arg1 wff)) (arg2 (arg1 wff)) -> wff1)
        (renumber wff1 -> wff1 rsubst)
        (declare (ignore rsubst))
        (quote :pos -> *assert-rewrite-polarity*)
        (assert-rewrite-check wff1)
        (store-rewrite wff1 '> (make-row1 (arg1 wff))))
      (prog->
        (make-compound *iff* (arg2 (arg2 wff)) (arg1 (arg2 wff)) -> wff2)
        (renumber wff2 -> wff2 rsubst)
        (declare (ignore rsubst))
        (quote :neg -> *assert-rewrite-polarity*)
        (assert-rewrite-check wff2)
        (store-rewrite wff2 '> (make-row1 (arg2 wff)))))	;same name?
     (t
      (error "Improper form for assert-rewrite."))))
  nil))

(defmacro assertion (wff &rest keys-and-values)
  (cond
   ((getf keys-and-values :ignore)
    nil)
   (t
    `(assertionfun ',wff ',keys-and-values))))			;don't evaluate wff or options

(declare-snark-option2 use-kif-assertion nil)

(defun assertionfun (wff keys-and-values)
  (cond
   ((use-kif-assertion?)
    (let ((*kif-assertion-options* keys-and-values))
      (kif-assert-sentence wff)))
   (t
    (apply 'assert wff keys-and-values))))

(defun assert (wff
	       &key
	       name
	       conc-name
	       (answer false)
               constraint-alist			;dotted-pairs of theory name and wff (OBSOLETE)
               constraints			;2-lists of theory name and wff
               (reason (assert-reason?))
               context
	       (partitions (use-partitions?))
               (supported (assert-supported?))
               (sequential (assert-sequential?))
	       documentation
               author				;for KIF
               source				;for KIF
               (input-wff none)
               (magic (use-magic-transformation?))
               closure)
  (cl:assert (symbolp name))
  (cl:assert (member supported '(nil t :uninherited)))
  (cl:assert (member sequential '(nil t :uninherited)))
  (cond
   ((eq :current context)
    (setf context (first (current-row-context))))
   (context
    (cl:assert (member context (current-row-context))))
   ((or (neq 'assertion reason) (eq :current (assert-context?)))
    (setf context (first (current-row-context))))
   (t
    (setf context (assert-context?))
    (cl:assert (member context (current-row-context)))))
  (let ((*print-pretty* nil) (*print-radix* nil) (*print-base* 10.) (n 0))
    (prog->
      (not (use-well-sorting?) -> *%check-for-well-sorted-atom%*)
      (input-wff wff :clausify (use-clausification?) -> wff dp-alist input-wff1 input-wff-subst)
      (when *find-else-substitution*
        (setq wff (instantiate wff *find-else-substitution*)))
      (mapcar (lambda (x) (cons (first x) (input-wff (second x) :*input-wff-substitution* input-wff-subst)))
              (or constraints (mapcar (lambda (x) (list (car x) (cdr x))) constraint-alist))
              -> constraint-alist)
      (input-wff answer :*input-wff-substitution* input-wff-subst -> answer)
      (if (use-equality-elimination?) (equality-eliminate-wff wff) wff -> wff)
      (if magic (magic-transform-wff wff :transform-negative-clauses supported) wff -> wff)
      (well-sort-wffs (list* wff answer (mapcar #'cdr constraint-alist)) ->* subst)
      (incf n)
      (map-conjuncts wff ->* wff)
      (catch 'fail
        (let* ((wff (fail-when-true (instantiate wff subst)))
               (row (make-row :wff wff
                              :constraints (fail-when-constraint-false (instantiate constraint-alist subst))
                              :answer (if (and magic (magic-goal-occurs-p wff))
                                          false
                                          (fail-when-disallowed (instantiate answer subst)))
                              :context (input-row-context context partitions)
                              :reason reason
                              :supported supported
                              :sequential sequential
                              :conc-name (and conc-name
                                              (if (stringp conc-name)
                                                  conc-name
                                                  (funcall conc-name wff)))
                              :documentation documentation
                              :author author
                              :source source
                              :input-wff (if (neq none input-wff) input-wff input-wff1)
                              :name name)))
          (when (use-assertion-analysis?)
            (assertion-analysis row))
          (record-new-input-wff row))))
    (unless (eql 1 n)
      (warn "Input wff ~A has ~D well-sorted instances." wff n)))
  (when closure
    (closure)))

(defun assume (wff &rest keys-and-values)
  (apply #'assert wff (append keys-and-values
                              (list :reason 'assumption
                                    :supported (assume-supported?)
                                    :sequential (assume-sequential?)))))

(defun prove (wff &rest keys-and-values)
  (apply #'assert `(not ,wff) (append keys-and-values
                                      (list :reason '~conclusion
                                            :supported (prove-supported?)
                                            :sequential (prove-sequential?)
                                            :closure (prove-closure?)))))

(defun print-incremental-time-used ()
  (let ((time (get-internal-run-time)))
    (format t "     ;~,2Fsec" (/ (- time time-mark) float-internal-time-units-per-second))
    (setq time-mark time)))

(defun fail ()
  (throw 'fail nil))

(defun fail-when-nil (x)
  (if (null x)
      (throw 'fail nil)
      x))

(defun fail-when-true (x)
  (if (eq true x)
      (throw 'fail nil)
      x))

(defun fail-when-false (x)
  (if (eq false x)
      (throw 'fail nil)
      x))

(defun fail-when-constraint-false (constraint-alist)
  (dolist (x constraint-alist constraint-alist)
    (when (eq false (cdr x))
      (throw 'fail nil))))

(defun fail-when-disallowed (answer)
  (if (answer-disallowed-p answer)
      (throw 'fail nil)
    answer))

(defun fail-when-disallowed-conditional (answer)
  (if (answer-conditional-disallowed-p answer)
      (throw 'fail nil)
      answer))

(defvar *check-for-disallowed-answer* nil)

(defun answer-disallowed-p (answer)
  (if (and (rewrite-answers?) (not *check-for-disallowed-answer*))
      nil
    (disallowed-symbol-occurs-in-answer-p answer nil)))

(defun answer-conditional-disallowed-p (answer)
  (if (and (rewrite-answers?) (not *check-for-disallowed-answer*))
      nil
      (disallowed-symbol-occurs-in-answer-conditional-p answer nil)))

(defun make-demodulant (row1 row2 wff2* context1 context2)
  (cond
   ((eq true wff2*)
    :tautology)
   (t
    (prog->
      (context-intersection-p context1 context2 ->nonnil context)
      (make-row :wff (instantiate wff2* 1)
	        :constraints (instantiate (row-constraints row2) 1)
	        :answer (instantiate (row-answer row2) 1)
	        :supported (row-supported row2)
                :sequential (row-sequential row2)
                :context context
	        :reason `(rewrite ,row2)
	        :rewrites-used (list row1))))))

(defun make-answer2 (row1 row2 subst cond swap)
  (let ((answer1 (instantiate (row-answer row1) 1 subst))
	(answer2 (instantiate (row-answer row2) 2 subst)))
    (fail-when-disallowed
      (cond
	((eq false answer1)
	 answer2)
	((eq false answer2)
	 answer1)
	((equal-p answer1 answer2)
	 answer1)
	((use-conditional-answer-creation?)
	 (if swap
	     (make-conditional (instantiate cond subst) answer2 answer1 nil *answer-if*)
	     (make-conditional (instantiate cond subst) answer1 answer2 nil *answer-if*)))
	(t
	 (disjoin answer1 answer2))))))

(defmacro make-resolvent-part (rown atomn atomn* truthvaluen n subst)
  (let ((wffn (gensym))
	(atom (gensym))
	(polarity (gensym))
	(atom* (gensym)))
    `(prog->
       (row-wff ,rown -> ,wffn)
       (cond
	 ((eq ,wffn ,atomn)
	  ,truthvaluen)
	 (t
	  (map-atoms-in-wff-and-compose-result ,wffn ->* ,atom ,polarity)
	  (declare (ignore ,polarity))
	  (cond
	    ((eq ,atom ,atomn)
	     ,truthvaluen)
	    (t
	     (instantiate ,atom ,n ,subst -> ,atom*)
	     (cond
	       ((equal-p ,atom* ,atomn* subst)
		,truthvaluen)
	       (t
		,atom*)))))))))

(defun make-resolvent1 (row1 atom1 truthvalue1 row2 atom2 truthvalue2 subst context1 context2)
  (prog->
    (context-intersection-p context1 context2 ->nonnil context)
    (instantiate atom1 1 -> atom1*)
    (instantiate atom2 2 -> atom2*)
    (disjoin
     (make-resolvent-part row1 atom1 atom1* truthvalue1 1 subst)
     (make-resolvent-part row2 atom2 atom2* truthvalue2 2 subst)
     -> wff)
    (cond
     ((eq true wff)
      :tautology)
     (t
      (make-row :wff wff
                :constraints (conjoin-alists
                              (instantiate (row-constraints row1) 1 subst)
                              (instantiate (row-constraints row2) 2 subst))
                :answer (make-answer2 row1 row2 subst atom1* (eq false truthvalue1))
                :supported (or (row-supported-inheritably row1) (row-supported-inheritably row2))
                :sequential (or (row-sequential-inheritably row1) (row-sequential-inheritably row2))
                :context context
                :reason (if (eq true truthvalue1)
                            `(resolve ,row1 ,row2)
                            `(resolve ,row2 ,row1)))))))

(defun make-resolvent (row1 atom1 atom1* truthvalue1 row2 atom2 atom2* truthvalue2 subst
                       context1 context2)
  (let ((made nil))
    (prog->
      (context-intersection-p context1 context2 ->nonnil context)
      (catch 'fail
        (record-new-derived-row
         (make-row :wff (fail-when-true
                         (if (eq true truthvalue1)
                             (disjoin
                              (make-resolvent-part row2 atom2 atom2* truthvalue2 2 subst)
                              (make-resolvent-part row1 atom1 atom1* truthvalue1 1 subst))
                             (disjoin
                              (make-resolvent-part row1 atom1 atom1* truthvalue1 1 subst)
                              (make-resolvent-part row2 atom2 atom2* truthvalue2 2 subst))))
                   :constraints (fail-when-constraint-false
				      (conjoin-alists
                                       (instantiate (row-constraints row1) 1 subst)
                                       (instantiate (row-constraints row2) 2 subst)))
                   :answer (make-answer2 row1 row2 subst atom1* (eq false truthvalue1))
                   :supported (or (row-supported-inheritably row1) (row-supported-inheritably row2))
                   :sequential (or (row-sequential-inheritably row1) (row-sequential-inheritably row2))
                   :context context
                   :reason (if (eq true truthvalue1)
                               `(resolve ,row1 ,row2)
                               `(resolve ,row2 ,row1))))
        (setq made t)))
    made))

(defun make-resolventa (row1 atom1 atom1* truthvalue1 subst context1 &optional residue)
  (prog->
   (catch 'fail
     (record-new-derived-row
      (make-row :wff (fail-when-true
                      (let ((wff (make-resolvent-part row1 atom1 atom1* truthvalue1 1 subst)))
                        (if residue (disjoin (instantiate residue subst) wff) wff)))
		:constraints (fail-when-constraint-false (instantiate (row-constraints row1) 1 subst))
		:answer (fail-when-disallowed (instantiate (row-answer row1) 1 subst))
		:supported (row-supported row1)
		:sequential (row-sequential row1)
                :context context1
		:reason `(resolve ,row1 ,(function-code-name (head atom1*))))))))

(defun make-resolventb (row1 residue subst context1)
  (prog->
   (catch 'fail
     (record-new-derived-row
      (make-row :wff (fail-when-true
                      (instantiate residue subst))
                :constraints (fail-when-constraint-false (instantiate (row-constraints row1) 1 subst))
                :answer (fail-when-disallowed (instantiate (row-answer row1) 1 subst))
                :supported (row-supported row1)
                :sequential (row-sequential row1)
                :context context1
                :reason `(resolve ,row1 :resolve-code))))))

(defun make-hyperresolvent-nucleus-part (nucleus subst)
  (prog->
    (hyperresolution-nucleus-polarity -> nucleus-polarity)
    (if (eq :pos nucleus-polarity) false true -> truthvalue)
    (map-atoms-in-wff-and-compose-result (row-wff nucleus) ->* atom polarity)
    (cond
     ((eq nucleus-polarity polarity)
      truthvalue)
     (t
      (instantiate atom 1 subst)))))

(defvar *resolve-functions-used* nil)

(defun make-hyperresolvent (nucleus electrons residues subst)
  (prog->
    (row-present-in-context-p nucleus ->nonnil context)
    (catch 'fail
      (let ((k (1+ (length electrons)))
	    (wff (fail-when-true (make-hyperresolvent-nucleus-part nucleus subst)))
	    (constraint-alist (fail-when-constraint-false (instantiate (row-constraints nucleus) 1 subst)))
	    (answer (fail-when-disallowed (instantiate (row-answer nucleus) 1 subst)))
	    (supported (row-supported-inheritably nucleus))
            (sequential (row-sequential-inheritably nucleus))
	    parents)
	(dolist (residue residues)
          (setf wff (fail-when-true (disjoin (instantiate residue subst) wff))))
        (dolist (x electrons)
          (mvlet (((:list electron+ atom atom*) x))
	    (setq wff (fail-when-true
			(disjoin
			  (make-resolvent-part electron+ atom atom* (if *negative-hyperresolution* true false) k subst)
			  wff)))
	    (when (row-constraints electron+)
	      (setq constraint-alist (fail-when-constraint-false
				 (conjoin-alists
				   (instantiate (row-constraints electron+) k subst)
				   constraint-alist))))
	    (unless (eq false (row-answer electron+))
	      (setq answer (cond
			     ((eq false answer)
			      (fail-when-disallowed (instantiate (row-answer electron+) k subst)))
			     ((not (use-conditional-answer-creation?))
			      (disjoin
				(fail-when-disallowed (instantiate (row-answer electron+) k subst))
				answer))
			     (*negative-hyperresolution*
			      (make-conditional
				(fail-when-disallowed-conditional (instantiate atom* k subst))
				(fail-when-disallowed (instantiate (row-answer electron+) k subst))
				answer
				nil
				*answer-if*))
			     (t
			      (make-conditional
				(fail-when-disallowed-conditional (instantiate atom* k subst))
				answer
				(fail-when-disallowed (instantiate (row-answer electron+) k subst))
				nil
				*answer-if*)))))
            (setq context (fail-when-nil (context-intersection-p
                                          context (row-present-in-context-p electron+))))
	    (unless supported
	      (setq supported (row-supported-inheritably electron+)))
            (unless sequential
              (setq sequential (row-sequential-inheritably electron+)))
	    (push electron+ parents)
	    (decf k)))
	(push nucleus parents)
	(record-new-derived-row
	  (make-row :wff wff
		    :constraints constraint-alist
		    :answer answer
		    :supported supported
                    :sequential sequential
                    :context context
		    :reason (if *negative-hyperresolution*
				`(negative-hyperresolve ,@parents ,@*resolve-functions-used*)
				`(hyperresolve ,@parents ,@*resolve-functions-used*))))))))

(defun make-ur-resolvent (nucleus electrons target-atom target-polarity subst)
  (prog->
    (row-present-in-context-p nucleus ->nonnil context)
    (catch 'fail
      (let ((k (1+ (length electrons)))
            (constraint-alist (fail-when-constraint-false (instantiate (row-constraints nucleus) 1 subst)))
            (answer (fail-when-disallowed (instantiate (row-answer nucleus) 1 subst)))
            (supported (row-supported-inheritably nucleus))
            (sequential (row-sequential-inheritably nucleus))
            parents)
        (dolist (electron electrons)
          (when (row-constraints electron)
            (setq constraint-alist (fail-when-constraint-false
                                    (conjoin-alists
                                     (instantiate (row-constraints electron) k subst)
                                     constraint-alist))))
          (unless (eq false (row-answer electron))
            (setq answer (cond
                          ((eq false answer)
                           (fail-when-disallowed (instantiate (row-answer electron) k subst)))
                          ((not (use-conditional-answer-creation?))
                           (disjoin
                            (fail-when-disallowed (instantiate (row-answer electron) k subst))
                            answer))
                          (t
                           (make-conditional
                            (fail-when-disallowed-conditional (instantiate (row-wff electron) k subst))
                            answer
                            (fail-when-disallowed (instantiate (row-answer electron) k subst))
                            nil
                            *answer-if*)))))
          (setq context (fail-when-nil (context-intersection-p
                                        context (row-present-in-context-p electron))))
          (unless supported
            (setq supported (row-supported-inheritably electron)))
          (unless sequential
            (setq sequential (row-sequential-inheritably electron)))
          (push electron parents)
          (decf k))
        (push nucleus parents)
        (record-new-derived-row
         (make-row :wff (if target-atom
                            (if (eq :pos target-polarity)
                                (instantiate target-atom subst)
                                (make-compound *not* (instantiate target-atom subst)))
                            false)
                   :constraints constraint-alist
                   :answer answer
                   :supported supported
                   :sequential sequential
                   :context context
                   :reason `(ur-resolve ,@parents ,@*resolve-functions-used*)))))))

(defun make-paramodulant-form (cc value1* term2* wff2* subst)
  (cond
    ((not (term-subsort-p value1* term2* subst))
     )
    ((use-single-replacement-paramodulation?)
     (substitute-once cc value1* term2* wff2* subst))
    (t
     (funcall cc (substitute value1* term2* wff2* subst)))))

(defun make-paramodulant (row1 equality1 value1* row2 term2* subst context1 context2)
  (prog->
    (context-intersection-p context1 context2 ->nonnil context)
    (catch 'fail
      (fail-when-constraint-false
       (conjoin-alists
        (instantiate (row-constraints row2) 2 subst)
        (instantiate (row-constraints row1) 1 subst))
       -> constraint)
      (instantiate equality1 1 subst -> equality1*)
      (make-answer2 row1 row2 subst equality1* t -> answer)
      (or (row-supported-inheritably row1) (row-supported-inheritably row2) -> supported)
      (or (row-sequential-inheritably row1) (row-sequential-inheritably row2) -> sequential)
      (list 'paramodulate row2 row1 -> reason)
      (make-resolvent-part row1 equality1 equality1* false 1 subst -> w1)
      (instantiate value1* subst -> value1*)
      (instantiate (row-wff row2) 2 subst -> wff2*)
      (make-paramodulant-form value1* term2* wff2* subst ->* w2)
      (catch 'fail
        (record-new-derived-row
         (make-row :wff (fail-when-true (disjoin w1 w2))
                   :constraints constraint
                   :answer answer
                   :supported supported
                   :sequential sequential
                   :context context
                   :reason reason))))))

(defun make-paramodulanta (value1* row2 term2* subst context2)
  (prog->
    (catch 'fail
      (fail-when-constraint-false (instantiate (row-constraints row2) 2 subst) -> constraint)
      (fail-when-disallowed (instantiate (row-answer row2) 2 subst) -> answer)
      (row-supported-inheritably row2 -> supported)
      (row-sequential-inheritably row2 -> sequential)
      (list 'paramodulate row2 (function-code-name (head term2*)) -> reason)
      (make-paramodulant-form
       (instantiate value1* subst) term2* (instantiate (row-wff row2) 2 subst) subst ->* w2)
      (catch 'fail
        (record-new-derived-row
         (make-row :wff (fail-when-true w2)
                   :constraints constraint
                   :answer answer
                   :supported supported
                   :sequential sequential
                   :context context2
                   :reason reason))))))

(defun canonicalize-wff (wff)
  (prog->
    (map-atoms-in-wff-and-compose-result wff ->* atom polarity)
    (unless (variable-p atom)			;shouldn't be variable atom
      (setq atom (hash-term atom))
      (map-terms-in-atom atom nil polarity ->* term polarity)
      (declare (ignore polarity))
      (unless (variable-p term)
	(tm-store term)))
    atom))

(defun index-terms-in-atom-of-derived-wff (atom polarity row)
  (setq atom (hash-term atom))
  (prog->
    (map-terms-in-atom atom nil polarity ->* term polarity)
    (declare (ignore polarity))
    (unless (variable-p term)
      (tm-store term)
      (insert-into-rows-containing-term row term)))
  atom)

(defun dont-make-embedding-p (a b)
  (declare (ignore b))
  ;; don't make embedding if ac lhs has a single-occurrence top-level variable
  (let ((head (head a)))
    (and
     (function-associative head)
     (function-commutative head)
     (let ((terms-and-counts (count-arguments head (args a) nil)))
       (loop for tc1 in terms-and-counts
             thereis (and
                      (eql 1 (tc-count tc1))
                      (variable-p (tc-term tc1))
                      (implies *using-sorts* (same-sort-p (associative-function-argument-sort head)
                                                          (variable-sort (tc-term tc1))))
                      (loop for tc2 in terms-and-counts
                            never (and (neq tc1 tc2) (variable-occurs-p (tc-term tc1) (tc-term tc2) nil)))))))))

(defun embedding-types (pattern value)
  (let ((head (head pattern)))
    (when (function-associative head)
      (unless (dont-make-embedding-p pattern value)
	(cond
	  ((function-commutative head)
	   :l)
	  (t
	   :l&r))))))

(defun store-rewrite2 (pattern value row conditional)
  (cond
    ((VARIABLE-P PATTERN)
     NIL)
    (t
     (prog->
       (make-rewrite row
		     pattern
		     value
		     (if conditional 'simplification-ordering-greaterp t)
		     (symbol-count pattern)
		     (new-variables value nil (variables pattern))
                     *assert-rewrite-polarity*
		     -> rewrite)
       (setq pattern (hash-term pattern))
       (tm-store pattern)
       (when (compound-p pattern)
	 (setf (function-rewritable-p (head pattern)) t)
	 (setf (rewrite-embeddings rewrite) (embedding-types pattern value)))
       (push rewrite (rewrites pattern))
       (when row
	 (push rewrite (row-rewrites row))))
     t)))

(defun store-rewrite (equality-or-equivalence &optional dir row)
  (let ((args (args equality-or-equivalence)) stored)
    (unless dir
      (setq dir (simplification-ordering-compare-equality-arguments equality-or-equivalence nil t)))
    (when (and (or (eq '> dir) (eq '>? dir) (eq '<>? dir))
	       (store-rewrite2 (first args) (second args) row (neq '> dir)))
      (setq stored t))
    (when (and (or (eq dir '<) (eq dir '<?) (eq dir '<>?))
	       (store-rewrite2 (second args) (first args) row (neq '< dir)))
      (setq stored t))
    (cond
      (stored
       (incf *number-of-rewrites*)
       (clear-rewrite-cache))
      ((member dir '(> >? < <? <>?))
       (warn "Cannot use equality or equivalence ~A as rewrite."
	     (print-term equality-or-equivalence nil :string)))
      (t
       (when (print-unorientable-rows?)
	 (print-unorientable-wff equality-or-equivalence))))))

(defun maybe-store-atom-rewrite (atom truth-value row)
  (when (use-simplification-by-units?)
    (store-rewrite (make-compound *iff* atom truth-value) '> row)))

(defun store-given-row (row)
  (unless (row-given-p row)
    (prog->
      (map-atoms-in-wff (row-wff row) ->* atom polarity)
      (when (and (eq :pos polarity) (equality-p atom))
	(args atom -> args)
	(first args -> arg1)
	(second args -> arg2)
        (unless (equal-p arg1 arg2)
	  (simplification-ordering-compare-equality-arguments atom nil -> dir)
	  (unless (eq '< dir)
	    (store-given-row-equality row arg1 arg2))
	  (unless (eq '> dir)
	    (store-given-row-equality row arg2 arg1)))))
    (setf (row-status row) :given))
  row)

(defun store-given-row-equality (row pattern value)
  (unless (variable-p pattern)
    (prog->
      (setq pattern (hash-term pattern))
      (tm-store pattern)
      (pushnew (cons row value)
	       (rows-containing-paramodulatable-equality pattern)
	       :test (lambda (x y) (and (eq (car x) (car y)) (eq (cdr x) (cdr y)))))
      )))

(defun store-derived-wff (row)
  ;; indexes atomic formulas of row so they can be retrieved for subsumption
  ;; indexes terms of row so they can be retrieved for demodulation
  ;; make rewrite from row if possible
  (let* ((wff (row-wff row))
	 (answer (row-answer row))
	 (potential-rewrite (and (row-bare-unit-p row) (not (row-embedding-p row)))))
    (setq wff (map-atoms-in-wff-and-compose-result
               (lambda (atom polarity)
                 (setq atom (index-terms-in-atom-of-derived-wff atom polarity row))
                 (prog->
                   (setq atom (hash-term atom))
                   (tm-store atom)
                   (unless (eq :neg polarity)
                     (insert-into-rows-containing-atom-positively row atom))
                   (unless (eq :pos polarity)
                     (insert-into-rows-containing-atom-negatively row atom))
                   (INSERT-INTO-ROWS-CONTAINING-TERM ROW ATOM)
                   (when potential-rewrite
                     (cond
                      ((and (use-simplification-by-equalities?) (eq :pos polarity) (equality-p atom))
                       (let ((args (args atom)))
                         (ecase (simplification-ordering-compare-equality-arguments atom nil T row)
                           (<
                            (store-rewrite atom '< row))
                           (>
                            (store-rewrite atom '> row))
                           (=
                            (unless (and (not (variable-p (first args)))
                                         (equal-p (first args) (second args)))
                              (maybe-store-atom-rewrite atom true row)))
                           (?
                            (case (instantiating-direction (first args) (second args) nil)
                              (>
                               (store-rewrite atom '>? row))
                              (<
                               (store-rewrite atom '<? row))
                              (<>
                               (IF (VARIANT-P (FIRST ARGS) (instantiate (SECOND ARGS) 1))
                                   (STORE-REWRITE atom '>? ROW)
                                   (store-rewrite atom '<>? row))))
                            (maybe-store-atom-rewrite atom true row)))))
                      (t
                       (maybe-store-atom-rewrite atom (if (eq :pos polarity) true false) row))))
                   atom))
		wff))
    (unless (OR (eq false answer) (VARIABLE-P ANSWER))
      (setq answer (canonicalize-wff answer)))
    (setf (row-wff row) wff)
    (setf (row-answer row) answer)
    (dolist (parent (row-parents row))
      (rowset-insert row (or (row-children parent)
                             (setf (row-children parent) (make-rowset)))))))

(defun recursively-unstore-wff (row msg stop-predicate)
  (unless (funcall stop-predicate row)
    (prog->
      (map-rows :rowset (row-children row) :reverse t ->* child)
      (recursively-unstore-wff child "Deleted descendant" stop-predicate))
    (unstore-wff row msg)))

(defun unstore-wff (row msg)
  (unless (row-deleted-p row)
    (delete-wff-from-agenda row *agenda*)
    (when (row-number row)
      (rowset-delete row *rows*)
      (when (eq false (row-wff row))
        (if (row-constrained-p2 row)
            (rowset-delete row *constraint-rows*)
            (rowset-delete row *false-rows*))))
    (let ((rewrites (row-rewrites row)))
      (when rewrites
	(clear-rewrite-cache)
	(dolist (rewrite rewrites)
	  (setf (rewrite-condition rewrite) nil)
	  (let ((e (the-term-memory-entry (rewrite-pattern rewrite))))
	    (setf (tme-rewrites e) (delete rewrite (tme-rewrites e) :count 1))))
	(setf (row-rewrites row) nil)))
    (prog->
      (dolist (row-parents row) ->* parent)
      (rowset-delete row (row-children parent)))
    (prog->
      (map-terms-in-term (row-wff row) ->* term polarity)
      (declare (ignore polarity))
      (unless (variable-p term)
	(some-term-memory-entry term -> e)
	(when e
	  (rowset-delete row (tme-rows-containing-atom-positively e))
	  (rowset-delete row (tme-rows-containing-atom-negatively e))
	  (rowset-delete row (tme-rows-containing-term e))
	  (let ((l (tme-rows-containing-paramodulatable-equality e)))
	    (when l
	      (setf (tme-rows-containing-paramodulatable-equality e) (delete row l :key #'car))))
	  (when (use-term-memory-deletion?)
	    (when (tme-useless-p e)
	      (tm-remove-entry e))))))		;reinstated deletion 1997-08-16
    (setf (row-status row) :deleted)
    (when (row-number row)
      (incf *number-of-backward-eliminated-rows*)
      (when (print-rows-when-derived?)
	(print-deleted-wff row msg))
      (prog->
        (map-rows :rowset (row-children row) :reverse t ->* child)
        (when (row-embedding-p child)
          (unstore-wff child "Deleted embedding")))
      (setf (row-children row) nil))))

(defun delete-row (name-or-number)
  (prog->
    (quote nil -> *printing-deleted-messages*)
    (row name-or-number 'warn ->nonnil row)
    (unstore-wff row "Deleted")))

(defun delete-rows (&rest map-rows-options)
  (prog->
    (quote nil -> *printing-deleted-messages*)
    (apply 'map-rows map-rows-options ->* row)
    (unstore-wff row "Deleted")))

(defun delete-row-if (test)
  (delete-rows :test test)
  (prog->
    (dolist *agendas* ->* agenda)
    (agenda-delete-if agenda ->* item)
    (funcall test (agenda-item-row item))))

(defun make-split (row wff answer polarity)
  (let* ((constraint-alist (row-constraints row))
	 (suppress-answer (let ((vars (variables answer)))
			    (and vars
				 (dolist (var vars t)
				   (when (or (variable-occurs-p var wff nil)
					     (variable-occurs-p var constraint-alist nil))
				     (return nil)))))))
    (make-row :wff (if (eq :pos polarity)
		       wff
		       (make-compound *not* wff))
	      :constraints constraint-alist
	      :answer (if suppress-answer false answer)
	      :supported (row-supported row)
	      :sequential (row-sequential row)
              :context (row-context row)
	      :reason (row-reason row)
	      :rewrites-used (row-rewrites-used row)
              :conc-name (or (row-conc-name row)
                             (let ((name (row-name row)))
                               (and name (format nil "~A-" name))))
              :documentation (row-documentation row)
              :author (row-author row)
              :source (row-source row)
              :input-wff (row-input-wff row))))

(defun and-split (cc row wff answer polarity splitting)
  (cond
    ((or (eq true wff) (eq false wff))
     (when splitting
       (funcall cc (make-split row wff answer polarity))))
    (t
     (let ((kind (and (compound-p wff) (function-logical-symbol-p (head wff)))))
       (ecase kind
	 (not
	   (and-split cc row (arg1 wff) answer (opposite-polarity polarity) splitting))
	 ((and or)
	  (cond
	    ((if (eq 'and kind) (eq :pos polarity) (eq :neg polarity))
	     (dolist (arg (args wff))
	       (and-split cc row arg answer polarity t))
	     t)
	    (splitting
	     (funcall cc (make-split row wff answer polarity)))))
	 (implies
	   (cond
	     ((eq :neg polarity)
	      (let ((args (args wff)))
		(and-split cc row (first args) answer :pos t)
		(and-split cc row (second args) answer :neg t))
	      t)
	     (splitting
	      (funcall cc (make-split row wff answer polarity)))))
	 (implied-by
	   (cond
	     ((eq :neg polarity)
	      (let ((args (args wff)))
		(and-split cc row (second args) answer :pos t)
		(and-split cc row (first args) answer :neg t))
	      t)
	     (splitting
	      (funcall cc (make-split row wff answer polarity)))))
	 ((iff xor)
	  (let ((args (args wff)))
	    (cond
	      ((if (eq 'iff kind) (eq :pos polarity) (eq :neg polarity))
	       (and-split cc row (make-compound *or*
					      (make-compound *not* (first args))
					      (second args))
			  answer polarity t)		 
	       (and-split cc row (make-compound *or*
					      (first args)
					      (make-compound *not* (second args)))
			  answer polarity t))
	      (t
	       (and-split cc row (make-compound *or*
					      (first args)
					      (second args))
			  answer polarity t)		 
	       (and-split cc row (make-compound *or*
					      (make-compound *not* (first args))
					      (make-compound *not* (second args)))
			  answer polarity t))))
	  t)
	 (if
	   (let ((args (args wff)))
	     (cond
	       ((eq :pos polarity)
		(and-split cc row (make-compound *implies*
					       (first args)
					       (second args))
			   answer polarity t)		 
		(and-split cc row (make-compound *implies*
					       (make-compound *not* (first args))
					       (third args))
			   answer polarity t))
	       (t
		(and-split cc row (make-compound *implies*
					       (first args)
					       (make-compound *not* (second args)))
			   answer polarity t)		 
		(and-split cc row (make-compound *implies*
					       (make-compound *not* (first args))
					       (make-compound *not* (third args)))
			   answer polarity t))))
	   t)
	 ((nil)
	  (when splitting
	    (funcall cc (make-split row wff answer polarity)))))))))

(defun factorer (row)
  (prog->
    (row-present-in-context-p row ->nonnil context)
    (dopairs (atoms-in-wff2 (row-wff row) nil :pos 1) ->* x y)
    (when (and (or (eq (second x) (second y)) (eq :both (second x)) (eq :both (second y)))
               (implies (row-sequential row)
                        (or (atom-satisfies-sequential-restriction-p (first x) (row-wff row))
                            (atom-satisfies-sequential-restriction-p (first y) (row-wff row)))))
      (unify (first x) (first y) ->* subst)
      (catch 'fail
        (record-new-derived-row
         (make-row :wff (fail-when-true (instantiate (row-wff row) 1 subst))
                   :constraints (fail-when-constraint-false (instantiate (row-constraints row) 1 subst))
                   :answer (fail-when-disallowed (instantiate (row-answer row) 1 subst))
                   :supported (row-supported row)
                   :sequential (row-sequential row)
                   :context context
                   :reason `(factor ,row)))))))

(defun resolve-with-x=x (row)
  (prog->
    (row-present-in-context-p row ->nonnil context)
    (when (row-supported row)
      (map-atoms-in-wff (row-wff row) ->* atom polarity)
      (when (and (eq :neg polarity) (equality-p atom))
        (args atom -> args)
        (when (or (variable-p (first args)) (variable-p (second args)))
          (instantiate atom 1 -> atom*)
          (args atom* -> args*)
          (unify (first args*) (second args*) ->* subst)
          (when (make-resolventa row atom atom* true subst context)
            (return-from resolve-with-x=x t))))))
  nil)

(defun resolver (row1)
  (prog->
    (row-present-in-context-p row1 ->nonnil context1)
    (use-literal-ordering-with-resolution? -> orderfun)
    (selected-atoms-in-row row1 orderfun -> selected-atoms-in-row1)
    (flet ((resolver1 (atom1 truthvalue1 truthvalue2 polarity1 polarity2)
             (prog->
               (quote nil -> atom1*)
               ;; apply resolve-code procedural attachments:
               (when (row-supported row1)
                 (dolist (and (compound-p atom1) (function-resolve-code (head atom1) truthvalue1))
                   ->* fun)
                 (funcall fun (setq-once atom1* (instantiate atom1 1)) nil ->* subst &optional residue)
                 (when (selected-atom-p atom1 polarity1 selected-atoms-in-row1 orderfun
                                        subst 1 atom1*)
                   (make-resolventa row1 atom1 atom1* truthvalue1 subst context1 residue)))
               ;; resolve row1 with other rows:
               (retrieve-unifiable-terms
                atom1
                nil
                (if (eq false truthvalue2)
                    #'tme-rows-containing-atom-positively
                    #'tme-rows-containing-atom-negatively)
                ->* atom2 row2s)
               (quote nil -> atom2*)
               (map-rows :rowset row2s :reverse t ->* row2)
               (row-present-in-context-p row2 ->nonnil context2)
               (selected-atoms-in-row row2 orderfun -> selected-atoms-in-row2)
               (when (and (if *interactive?
                              (implies *row2* (eq row2 *row2*))
                              (row-given-p row2))
                          (OR (AND (ROW-UNIT-P ROW1) (ROW-UNIT-P ROW2))
                              (meets-binary-restrictions-p row1 row2))
                          (selected-atom-p atom2 polarity2 selected-atoms-in-row2 orderfun))
                 (setq-once atom1* (instantiate atom1 1))
                 (setq-once atom2* (instantiate atom2 2))
                 (unify atom1* atom2* nil ->* subst)
                 (when (and (selected-atom-p atom1 polarity1 selected-atoms-in-row1 orderfun
                                             subst 1 atom1*)
                            (selected-atom-p atom2 polarity2 selected-atoms-in-row2 orderfun
                                             subst 2 atom2*))
                   (make-resolvent row1 atom1 atom1* truthvalue1 
                                   row2 atom2 atom2* truthvalue2
                                   subst context1 context2))))))
      (prog->
        (dolist selected-atoms-in-row1 ->* x)
        (values-list x -> atom1 polarity1)
        (unless (eq :neg polarity1)
          (resolver1 atom1 false true :pos :neg))
        (unless (eq :pos polarity1)
          (resolver1 atom1 true false :neg :pos))))))

(defun code-resolver (row1)
  (prog->
    (when (row-supported row1)
      (row-present-in-context-p row1 ->nonnil context1)
      (instantiate (row-wff row1) 1 -> wff1)
      (dolist (use-resolve-code?) ->* fun)
      (funcall fun wff1 nil ->* subst &optional wff1*)
      (make-resolventb row1 (or wff1* false) subst context1))))

(definline hyperresolution-electron-polarity ()
  ;; every atom in an electron has this polarity
  (if *negative-hyperresolution* :neg :pos))

(definline hyperresolution-nucleus-polarity ()
  ;; some atom in a nucleus has this polarity
  (if *negative-hyperresolution* :pos :neg))

(definline row-hyperresolution-electron-p (row)
  (if *negative-hyperresolution* (row-negative-p row) (row-positive-p row)))

(definline hyperresolution-orderfun ()
  (if *negative-hyperresolution*
      (use-literal-ordering-with-negative-hyperresolution?)
      (use-literal-ordering-with-hyperresolution?)))

(defun hyperresolver (row)
  (prog->
    (cond
      ((row-hyperresolution-electron-p row)
       (hyperresolution-orderfun -> orderfun)
       (dolist (selected-atoms-in-row row orderfun) ->* x)	;row is electron
       (values-list x -> atom2 polarity2)
       (if (eq :pos polarity2) false true -> truthvalue2)
       (prog->					;use procedural attachment as unit nucleus
         (row-present-in-context-p row ->nonnil context)
         (when (row-supported row)
           (quote nil -> atom2*)
           (dolist (and (compound-p atom2) (function-resolve-code (head atom2) polarity2)) ->* fun)
           (funcall fun (setq-once atom2* (instantiate atom2 1)) nil ->* subst &optional residue)
           (selected-atoms-in-row row orderfun -> selected-atoms-in-row)
           (when (selected-atom-p atom2 polarity2 selected-atoms-in-row orderfun subst 1 atom2*)
             (make-resolventa row atom2 atom2* truthvalue2 subst context residue))))
       (prog->
       (quote nil -> atom2*)
       (retrieve-unifiable-terms
	 atom2
	 nil
	 (if *negative-hyperresolution*
             #'tme-rows-containing-atom-positively
             #'tme-rows-containing-atom-negatively)
	 ->* atom1 row1s)
       (quote nil -> atom1*)
       (map-rows :rowset row1s :reverse t ->* row1)
       (when (or *interactive? (row-given-p row1))
	 (setq-once atom1* (instantiate atom1 1))
	 (setq-once atom2* (instantiate atom2 2))
	 (unify atom1* atom2* nil ->* subst)
	 (hyperresolver1 row1 atom1 row atom2 atom2* subst))))
      (t					;row is nucleus
       (let ((atoms nil) (atoms* nil))
	 (prog->
	  (map-atoms-in-wff (row-wff row) ->* atom polarity)
	  (when (and (eq (hyperresolution-nucleus-polarity) polarity)
		     (not (member atom atoms)))	;equal-p => eq for canonical terms
	    (push atom atoms)
	    (push (instantiate atom 1) atoms*)))
	 (when atoms*
	   (hyperresolver2 row nil (nreverse atoms*) 2 nil nil)))))))

(defun hyperresolver1 (nucleus atom1 electron atom2 atom2* subst)
  (let ((atoms nil) (atoms* nil))
    (prog->
      (map-atoms-in-wff (row-wff nucleus) ->* atom polarity)
      (when (and (neq atom atom1)		;equal-p => eq for canonical terms
		 (eq (hyperresolution-nucleus-polarity) polarity)
		 (not (member atom atoms)))	;equal-p => eq for canonical terms
	(push atom atoms)
	(push (instantiate atom 1) atoms*)))	;no dereferencing needed
    (hyperresolver2 nucleus (list (list electron atom2 atom2*)) (NREVERSE atoms*) 3 nil subst)))

(defun hyperresolver2 (nucleus electrons atoms* n residues subst)
  (declare (type fixnum n))
  (prog->
    (hyperresolution-orderfun -> orderfun)
    (cond
     ((null atoms*)
      (when (and (implies *interactive? (submultisetp *row2* (mapcar #'first electrons)))
		 (or (row-supported nucleus)
		     (some (lambda (x) (row-supported (first x))) electrons))
		 (selected-atoms-in-hyperresolution-electrons-p electrons subst))
	(make-hyperresolvent nucleus electrons residues subst)))
     (t
      (first atoms* -> atom*)
      (when (test-option9?)
        (let ((atom** (rewriter atom* subst)))
          ;; should record what rewrites are used
          (when (neq none atom*)
            (cond
             ((eq true atom**)
              (return-from hyperresolver2
                (unless *negative-hyperresolution*
                  (hyperresolver2 nucleus electrons (rest atoms*) n residues subst))))
             ((eq false atom**)
              (return-from hyperresolver2
                (when *negative-hyperresolution*
                  (hyperresolver2 nucleus electrons (rest atoms*) n residues subst))))
             (t
              (setf atom* atom**))))))
      (prog->
        (dolist (and (compound-p atom*)
                     (function-resolve-code (head atom*) (if *negative-hyperresolution* false true)))
          ->* fun)
        (funcall fun atom* subst ->* subst &optional residue)
        (cons (function-code-name (head atom*)) *resolve-functions-used* -> *resolve-functions-used*)
        (hyperresolver2 nucleus electrons (rest atoms*) n (cons-unless-nil residue residues) subst))
      (retrieve-unifiable-terms
       atom*
       subst
       (if *negative-hyperresolution* #'tme-rows-containing-atom-negatively #'tme-rows-containing-atom-positively)
       ->* atomn rowns)
      (quote nil -> atomn*)
      (map-rows :rowset rowns :reverse t ->* rown)
      (selected-atoms-in-row rown orderfun -> selected-atoms-in-rown)
      (when (and (or *interactive? (row-given-p rown))
		 (row-hyperresolution-electron-p rown))
	(when (selected-atom-p
               atomn
               (hyperresolution-electron-polarity)
               selected-atoms-in-rown
               orderfun)
	  (unify (first atoms*) (setq-once atomn* (instantiate atomn n)) subst ->* subst)
	  (hyperresolver2 nucleus (cons (list rown atomn atomn*) electrons) (rest atoms*) (1+ n) residues subst)))))))

(defun ur-resolver (row)
  (when (row-clause-p row)				;nucleus
    (ur-resolver1 row))
  (when (row-unit-p row)				;electron
    (prog->
      (map-atoms-in-wff (row-wff row) ->* atom2 polarity2)
      (setq atom2 (instantiate atom2 2))
      (retrieve-unifiable-terms
       atom2
       nil
       (if (eq :pos polarity2) #'tme-rows-containing-atom-negatively #'tme-rows-containing-atom-positively)
       ->* atom1 row1s)
      (quote nil -> atom1*)
      (map-rows :rowset row1s :reverse t ->* row1)		;nucleus
      (when (and (or *interactive? (row-given-p row1))
                 (row-clause-p row1)
                 (not (row-unit-p row1)))
        (setq-once atom1* (instantiate atom1 1))
        (unify atom1* atom2 ->* subst)
        (ur-resolve1 row1 (list row) nil nil subst (atoms-in-clause2 (row-wff row1) atom1) 3))))
  nil)

(defun ur-resolver1 (nucleus)
  (ur-resolve1 nucleus nil nil nil nil (atoms-in-clause2 (row-wff nucleus)) 2))

(defun ur-resolve1 (nucleus electrons target-atom target-polarity subst l k)
  (declare (type fixnum k))
  (cond
   ((null l)
    (when (and (implies *interactive? (submultisetp *row2* electrons))
               (or (row-supported nucleus)
                   (some #'row-supported electrons))
               (implies (and target-atom
                             (use-literal-ordering-with-ur-resolution?)
                             (clause-p (row-wff nucleus)))
                        (literal-is-not-dominating-in-clause-p
                         (use-literal-ordering-with-ur-resolution?)
                         target-atom
                         target-polarity
                         (instantiate (row-wff nucleus) 1)
                         subst)))
      (make-ur-resolvent nucleus electrons target-atom target-polarity subst)))
   (t
    (let ((atom1 (instantiate (first (first l)) 1))
          (polarity1 (second (first l))))
      (when (null target-atom)
        (ur-resolve1 nucleus electrons atom1 polarity1 subst (rest l) k))
      (when (eq target-polarity polarity1)
        (prog->
          (unify target-atom atom1 subst ->* subst)
          (ur-resolve1 nucleus electrons target-atom target-polarity subst (rest l) k)))
      (prog->
        (dolist (and (compound-p atom1) (function-resolve-code (heada atom1) polarity1)) ->* fun)
        (funcall fun atom1 subst ->* subst &optional residue)
        (unless residue
          (cons (function-code-name (head atom1)) *resolve-functions-used* -> *resolve-functions-used*)
          (ur-resolve1 nucleus electrons target-atom target-polarity subst (rest l) k)))
      (prog->
        (retrieve-unifiable-terms
         atom1
         subst
         (if (eq :pos polarity1) #'tme-rows-containing-atom-negatively #'tme-rows-containing-atom-positively)
         ->* atomk rowks)
        (quote nil -> atomk*)
        (map-rows :rowset rowks :reverse t ->* rowk)
        (when (and (or *interactive? (row-given-p rowk))
                   (row-unit-p rowk))
          (setq-once atomk* (instantiate atomk k))
          (unify atom1 atomk* subst ->* subst)
          (ur-resolve1 nucleus (cons rowk electrons) target-atom target-polarity subst (rest l) (1+ k))))))))

(defun backward-demodulate-by (row1)
  (loop for rewrite in (row-rewrites row1)
	as pattern = (rewrite-pattern rewrite)
	as value = (rewrite-value rewrite)
	as pattern-symbol-count = (rewrite-pattern-symbol-count rewrite)
	as cond = (rewrite-condition rewrite)
	as embeddings = (rewrite-embeddings rewrite)
	when (IF (OR (EQ TRUE VALUE) (EQ FALSE VALUE))
		 (AND (USE-SIMPLIFICATION-BY-UNITS?)
		      (NEQ :FORWARD (USE-SIMPLIFICATION-BY-UNITS?)))
		 (AND (USE-SIMPLIFICATION-BY-EQUALITIES?)
		      (NEQ :FORWARD (USE-SIMPLIFICATION-BY-EQUALITIES?))))
        do (prog->
             (row-present-in-context-p row1 ->nonnil context1)
             (instantiate pattern 1 -> pattern*)
             (instantiate value 1 -> value*)
             (retrieve-instance-terms pattern* nil ->* e)
             (let ((row2s (rows-containing-term2 e)) e*)	;paramodulatable term?
               (unless (rowset-empty? row2s)
                 (when (block it
                         (prog->
                           (rewrite-patterns-and-values
                            pattern* value* pattern-symbol-count embeddings (symbol-count e) ->* pattern** value**)
                           (subsume pattern** e nil ->* subst)
                           (when (and (or (eq cond t) (funcall cond pattern* value* subst))
                                      (term-subsort-p value** pattern** subst))
                             (setq e* (instantiate value** subst))
                             (return-from it t)))
                         nil)
                   (prog->
                     (map-rows :rowset row2s :reverse t ->* row2)
                     (row-present-in-context-p row2 ->nonnil context2)
                     (unless (or (eq row1 row2)
                                 (row-embedding-p row2)
                                 (row-deleted-p row2)
                                 (not (eq t (context-subsumption-p context1 context2))))
                       (cond
                        ((or (eq true value) (eq false value))
                         (let ((result (make-resolvent1 row1 pattern (if (eq true value) false true)
                                                        row2 e value nil context1 context2)))
                           (when result
                           (unless (eq :tautology result)
                                               (cond
;;						  ((row-input-p row2)
;;						   (setf (row-reason result) (row-reason row2))
;;						   (setf (row-name result) (row-name row2)))
                                                (t
                                                 (setf (row-reason result) `(rewrite ,row2))))
                                               (setf (row-rewrites-used result) (list row1)))
                           result)))
                        (t
                         (make-demodulant row1 row2 (substitute e* e (row-wff row2)) context1 context2))
                        ->nonnil demodulant)
                       (if recursive-unstore
                           (RECURSIVELY-unstore-wff row2 "Simplified" (LAMBDA (X) (EQ ROW1 X)))
                           (unstore-wff row2 "Simplified"))
                       (unless (eq :tautology demodulant)
                         (record-backward-simplifiable-wff demodulant)))))))))
  (setq *printing-deleted-messages* nil))

(defun paramodulater-from (row1)
  (prog->
    (use-literal-ordering-with-paramodulation? -> orderfun)
    (row-wff row1 -> wff1)
    (when (and (implies (and orderfun
                             (not (test-option3?))
                             (clause-p wff1))
                        (positive-equality-wff-p wff1))
	       (implies (use-paramodulation-only-from-units?) (equality-p wff1)))
      (map-atoms-in-wff wff1 ->* atom1 polarity1)
      (when (and (neq polarity1 :neg)
		 (equality-p atom1)
                 (if (row-sequential row1)
                     (atom-satisfies-sequential-restriction-p atom1 wff1)
                     (implies orderfun (literal-satisfies-ordering-restriction-p
                                        orderfun atom1 :pos wff1))))
	(args atom1 -> args)
	(first args -> a)
	(second args -> b)
	(unless (eq a b)			;equal-p => eq for canonical terms
	  (SIMPLIFICATION-ORDERING-COMPARE-EQUALITY-ARGUMENTS ATOM1 nil -> DIR)
	  (setq a (instantiate a 1))
	  (setq b (instantiate b 1))
	  (UNLESS (or (variable-p a) (EQ '< DIR))
	    (PARAMODULATER-FROM1 ROW1 atom1 A B DIR))
	  (UNLESS (or (variable-p b) (EQ '> DIR))
	    (PARAMODULATER-FROM1 ROW1 atom1 B A DIR)))))))

(defun paramodulater-from1 (row1 equality1 pattern1* value1* dir)
  ;; row1 has the equality
  (declare (ignore dir))
  (prog->
    (row-present-in-context-p row1 ->nonnil context1)
    (and (row-embedding-p row1) (embedding-variables row1 1) -> embedding-variables1)
    (retrieve-unifiable-terms pattern1* nil ->* term2)
    (unless (variable-p term2)
      (rows-containing-paramodulatable-term term2 -> row2s)
      (when row2s
        (setq row2s (impose-binary-restrictions row1 (IF (AND *INTERACTIVE? *ROW2*)
                                                         (REMOVE-IF-NOT (LAMBDA (X) (EQ *ROW2* X)) ROW2S)
                                                         ROW2S)))
        (when row2s
          (instantiate term2 2 -> term2*)
          (and embedding-variables1		;unify-bag only cares if both terms are embeddings
               (loop for row2 in row2s
                     always (and (row-embedding-p row2)
                                 (or (equal-p term2 (first (args (row-wff row2))) nil)
                                     (equal-p term2 (second (args (row-wff row2))) nil))))
               (embedding-variables (car row2s) 2)
               -> embedding-variables2)
          (and embedding-variables2 (append embedding-variables1 embedding-variables2) -> *embedding-variables*)
          (when (allowable-embedding-superposition (row-embedding-p row1) (row-embedding-p (car row2s)))
            (unify pattern1* term2* nil ->* subst)
            (unless (or (equal-p pattern1* value1* subst)
;;                      (and (neq dir '>)
;;                           (neq dir '<)
;;                           (eq '< (simplification-ordering-compare-terms pattern1* value1* subst '<)))
                        )
              (dolist row2s ->* row2)
              (row-present-in-context-p row2 ->nonnil context2)
              (make-paramodulant row1 equality1 value1* row2 term2* subst context1 context2))))))))

(defun paramodulater-to (row2)
  (prog-> 
    (quote nil -> done)
    (use-literal-ordering-with-paramodulation? -> orderfun)
    (row-wff row2 -> wff2)
    (implies (and orderfun
                  (not (test-option3?))
                  (clause-p wff2))
             (positive-equality-wff-p wff2)
             -> paramodulate-to-equalities)
    (dolist (selected-atoms-in-row row2 orderfun) ->* x)
    (values-list x -> atom2 polarity2)
    (cond
      ((AND (EQ :POS POLARITY2) (EQUALITY-P atom2))
       (WHEN PARAMODULATE-TO-EQUALITIES
	 (ARGS atom2 -> ARGS)
	 (FIRST ARGS -> A)
	 (SECOND ARGS -> B)
	 (SIMPLIFICATION-ORDERING-COMPARE-EQUALITY-ARGUMENTS ATOM2 NIL -> DIR)
	 (UNLESS (EQ '< DIR)
	   (MAP-TERMS-IN-TERM A nil POLARITY2 ->* TERM2 POLARITY)
	   (DECLARE (IGNORE POLARITY))
	   (UNLESS (OR (EQ TERM2 A) (VARIABLE-P TERM2) (MEMBER TERM2 DONE))
	     (PARAMODULATER-TO1 ROW2 TERM2 (INSTANTIATE TERM2 2) DIR)
	     (PUSH TERM2 DONE)))
	 (UNLESS (EQ '> DIR)
	   (MAP-TERMS-IN-TERM B nil POLARITY2 ->* TERM2 POLARITY)
	   (DECLARE (IGNORE POLARITY))
	   (UNLESS (OR (EQ TERM2 B) (VARIABLE-P TERM2) (MEMBER TERM2 DONE))
	     (PARAMODULATER-TO1 ROW2 TERM2 (INSTANTIATE TERM2 2) DIR)
	     (PUSH TERM2 DONE)))))
      (t
       (map-terms-in-atom atom2 nil :pos ->* term2 polarity)
       (declare (ignore polarity))
       (unless (or (variable-p term2) (member term2 done))
	 (paramodulater-to1 row2 term2 (instantiate term2 2) nil)
	 (push term2 done))))))

(defun paramodulater-to1 (row2 term2 term2* dir)
  (declare (ignore dir))
  (prog->
    (row-present-in-context-p row2 ->nonnil context2)
    (when (row-supported row2)
      (dolist (and (compound-p term2*) (function-paramodulate-code (head term2*))) ->* fun)
      (funcall fun term2* nil ->* value1* subst)
      (make-paramodulanta value1* row2 term2* subst context2))
    (and (row-embedding-p row2)
         (or (equal-p term2 (first (args (row-wff row2))) nil)
             (equal-p term2 (second (args (row-wff row2))) nil))
         (embedding-variables row2 2) -> embedding-variables2)
    (retrieve-unifiable-terms term2* nil #'tme-rows-containing-paramodulatable-equality ->* pattern1 ws)
    (instantiate pattern1 1 -> pattern1*)
    (dolist ws ->* w)
    (car w -> row1)
    (row-present-in-context-p row1 ->nonnil context1)
    (when (meets-binary-restrictions-p row2 row1)
      (cdr w -> value1)
      (unless (eq pattern1 value1)		;equal-p => eq for canonical terms
        (make-compound *=* pattern1 value1 -> equality1)
        (WHEN (OR (TEST-OPTION16?)		;TEST-OPTION16 GIVES PREVIOUS NO-ORDERING BEHAVIOR
                  (if (row-sequential row1)
                      (atom-satisfies-sequential-restriction-p equality1 (row-wff row1))
                      (let ((orderfun (USE-LITERAL-ORDERING-WITH-PARAMODULATION?)))
                        (implies orderfun (LITERAL-SATISFIES-ORDERING-RESTRICTION-P		;MES 2002-02-08
                                           orderfun EQUALITY1 :POS (ROW-WFF ROW1))))))
          (instantiate value1 1 -> value1*)
          (and embedding-variables2		;unify-bag only cares if both terms are embeddings
               (row-embedding-p row1)
               (embedding-variables row1 1)
               -> embedding-variables1)
          (and embedding-variables1 (append embedding-variables1 embedding-variables2) -> *embedding-variables*)
          (when (allowable-embedding-superposition (row-embedding-p row1) (row-embedding-p row2))
            (unify pattern1* term2* nil ->* subst)
            (unless (or (equal-p pattern1* value1* subst)
;;                      (and (neq dir '>)
;;                           (neq dir '<)
;;                           (eq '< (simplification-ordering-compare-terms pattern1* value1* subst '<)))
		        )
              (unless (eql (row-number row1) (row-number row2))
                ;;don't duplicate work (DO THIS IN IMPOSE-BINARY-RESTRICTIONS INSTEAD)
                (make-paramodulant row1 equality1 value1* row2 term2* subst
                                   context1 context2)))))))))

(defun paramodulation-allowable-p (term row)
  (prog->
    (row-wff row -> wff)
    (implies (and (use-literal-ordering-with-paramodulation?)
                  (not (test-option3?))
                  (clause-p wff))
             (positive-equality-wff-p wff)
             -> paramodulate-to-equalities)
    (map-atoms-in-wff wff ->* atom polarity)
    (cond
      ((and (eq :pos polarity) (equality-p atom))
       (when paramodulate-to-equalities
	 (args atom -> args)
	 (simplification-ordering-compare-equality-arguments atom nil -> dir)
	 (when (if (row-embedding-p row) (equal-p term (first args) nil) (occurs-p term (first args) nil))
	   (unless (eq '< dir)
	     (return-from paramodulation-allowable-p t)))
	 (when (if (row-embedding-p row) (equal-p term (second args) nil) (occurs-p term (second args) nil))
	   (unless (eq '> dir)
	     (return-from paramodulation-allowable-p t)))))
      ((occurs-p term atom nil)
       (when (if (row-sequential row)
                 (atom-satisfies-sequential-restriction-p atom (row-wff row))
                 (let ((orderfun (use-literal-ordering-with-paramodulation?)))
                   (implies orderfun (literal-satisfies-ordering-restriction-p orderfun atom polarity wff))))
	 (return-from paramodulation-allowable-p t)))))
  nil)

(defun rows-containing-paramodulatable-term (term)
  (rows :rowset (rows-containing-term term)
        :reverse t
        :test (lambda (row)
                (and (or *interactive? (row-given-p row))
                     (implies (use-paramodulation-only-into-units?) (row-unit-p row))
                     (paramodulation-allowable-p term row)))))

(defun make-embeddings (cc row)
  (unless (row-embedding-p row)
    (let ((wff (row-wff row)))
      (when (equality-p wff)
        (mvlet* (((:list a b) (args wff))
	         (a-associative (and (compound-appl-p a)
				     (function-associative (head a))
				     (function-unify-code (head a))))
	         (b-associative (and (compound-appl-p b)
				     (function-associative (head b))
				     (function-unify-code (head b)))))
	  (when (or a-associative b-associative)
	    (let ((dir (simplification-ordering-compare-terms a b)))
	      (cond
               ((eq '> dir)
                (when a-associative
                  (make-embeddings1 cc row a b)))
               ((eq '< dir)
                (when b-associative
                  (make-embeddings1 cc row b a)))
               ((and (compound-appl-p a) (compound-appl-p b) (eq (head a) (head b)))
                (make-embeddings1 cc row a b))
               (t
                (when a-associative
                  (make-embeddings1 cc row a b))
                (when b-associative
                  (make-embeddings1 cc row b a)))))))))))

(defun make-embeddings1 (cc row a b)
  (let* ((head (head a))
	 (args (args a))
         (sort (associative-function-argument-sort head))
	 (newvar2 (make-variable sort))
	 (temp (append args (list newvar2))))
    (cond
     ((function-commutative head)
      (let ((a* (make-compound* head temp))
            (b* (make-compound head b newvar2)))		;might not be flattened
        (unless (subsumes-p (renumber (cons a b)) (cons a* b*))
          (funcall cc (make-embedding row a* b* t)))))
     (t
      (let ((newvar1 (make-variable sort))
            (abs (list (renumber (cons a b)))))
        (let ((a* (make-compound* head (cons newvar1 args)))
              (b* (make-compound head newvar1 b)))		;might not be flattened
          (unless (dolist (ab abs)
                    (when (subsumes-p ab (cons a* b*))
                      (return t)))
            (push (renumber (cons a* b*)) abs)
            (funcall cc (make-embedding row a* b* :l))))
        (let ((a* (make-compound* head temp))
              (b* (make-compound head b newvar2)))		;might not be flattened
          (unless (dolist (ab abs)
                    (when (subsumes-p ab (cons a* b*))
                      (return t)))
            (push (renumber (cons a* b*)) abs)
            (funcall cc (make-embedding row a* b* :r))))
        (let ((a* (make-compound* head (cons newvar1 temp)))
              (b* (make-compound head newvar1 b newvar2)))	;might not be flattened
          (unless (dolist (ab abs)
                    (when (subsumes-p ab (cons a* b*))
                      (return t)))
            (funcall cc (make-embedding row a* b* :l&r)))))))))

(defun make-embedding (row a1 b1 type)
  (make-row :wff (make-equality a1 b1 nil)
	    :constraints (row-constraints row)
	    :answer (row-answer row)
	    :supported (row-supported row)
            :sequential (row-sequential row)
            :context (row-context row)
	    :reason (if (eq t type) `(embed ,row) `(embed ,row ,type))))

(defun embedding-variables (embedding+ n)
  ;; may not return all embedding-variables because the embedding
  ;; (= (f a ?x) (f b ?x)) might be stored as (= (f a ?x) (f ?x b)) if f is AC
  (mvlet ((vars nil)
          ((:list arg1 arg2) (args (row-wff embedding+))))
    (when (and (compound-appl-p arg1)
               (compound-appl-p arg2)
               (eq (heada arg1) (heada arg2)))
      (let ((type (row-embedding-p embedding+)))
        (when (or (eq :l&r type) (eq :r type) (eq t type))
          (let ((x (first (last (argsa arg1))))
                (y (first (last (argsa arg2)))))
            (when (and (eq x y) (variable-p x))
              (push (instantiate x n) vars))))
        (when (or (eq :l&r type) (eq :l type))
          (let ((x (first (argsa arg1)))
                (y (first (argsa arg2))))
            (when (and (eq x y) (variable-p x))
              (push (instantiate x n) vars))))))
    vars))

(defun allowable-embedding-superposition (type1 type2)
  (or (null type1)
      (null type2)
      (and (eq t type1) (eq t type2))
      (and (eq :l type1) (eq :r type2))
      (and (eq :r type1) (eq :l type2))))

(defun meets-binary-restrictions-p (row1 row2)
  (and (or (row-supported row1) (row-supported row2))
       (implies (use-unit-restriction?) (or (row-unit-p row1) (row-unit-p row2)))
       (implies (use-input-restriction?) (or (row-input-p row1) (row-input-p row2)))))

(defun impose-binary-restrictions (row1 l &key (key #'identity))
  (remove-if-not (lambda (x) (meets-binary-restrictions-p row1 (funcall key x))) l))

(defun process-new-row-msg (string)
  (when (print-rows-when-processed?)
    (with-clock-on printing
      (terpri-comment)
      (format t "~A" string))))

(defun process-new-row (row agenda-value)
  (let ((*processing-row* row)
        (wff (row-wff row))
	(*rewriting-row-context* (row-present-in-context-p row)))
    (unless *rewriting-row-context*
      (return-from process-new-row nil))
    (when (print-rows-when-processed?)
      (print-processed-row row))
    (when (eq true wff)
      (process-new-row-msg "Row wff is true.")
      (return-from process-new-row nil))
    (when (and (or (neq 'assertion (row-reason row))	;throw out t=t, except for equality axioms
		   (not (null (row-rewrites-used row))))
	       (equality-p wff)
	       (let ((args (args wff)))
		 (equal-p (first args) (second args))))
      (process-new-row-msg "Row wff is of form term=term.")
      (return-from process-new-row nil))
    (when (AND (CONSP AGENDA-VALUE)
               (EQL 2 (CAR AGENDA-VALUE))
	       (LOOP FOR PARENT IN (ROW-PARENTS ROW)
		     THEREIS (ROW-DELETED-P PARENT)))
      (process-new-row-msg "Row parent is deleted.")
      (return-from process-new-row nil))
    (when (or (use-and-splitting?) (use-clausification?))
      (when (and-split (lambda (x)		;call another function?  record on parent?
                         (insert-wff-into-agenda x agenda-value *agenda-of-other-wffs-to-process* t))
                       row wff (row-answer row) :pos nil)	
        (process-new-row-msg "Row wff will be and-split.")
        (return-from process-new-row nil)))
    (dolist (fun (pruning-tests-before-simplification?))
      (when (funcall fun row)
	(process-new-row-msg "Row is unacceptable before simplification.")
	(return-from process-new-row nil)))
    (let ((answer (row-answer row))
	  constraint-alist
	  (AND-SPLIT-THIS nil))
      (when (or (use-simplification-by-units?) (use-simplification-by-equalities?))
	(unless (row-embedding-p row)
	  (setq *rewrites-used* (row-rewrites-used row))
	  (with-clock-on forward-simplification
            (setf (row-wff row) (setq wff (rewriter wff nil))))
	  (when (eq true wff)
	    (process-new-row-msg "Simplified row wff is true.")
	    (return-from process-new-row nil))
	  (setf (row-rewrites-used row) *rewrites-used*))
	(when (rewrite-answers?)
	  (setq *rewrites-used* (row-rewrites-used row))
	  (with-clock-on forward-simplification
            (setf (row-answer row) (setq answer (rewriter answer nil))))
	  (setf (row-rewrites-used row) *rewrites-used*))
        (when (rewrite-constraints?)
          ;; inefficient to always rewrite constraints
          ;; can't rewrite constraints already in global data structures
          (setq *rewrites-used* (row-rewrites-used row))
          (with-clock-on forward-simplification
            (setf (row-constraints row) 
                  (rewrite-constraint-alist (row-constraints row))))
          (setf (row-rewrites-used row) *rewrites-used*)))
      (let ((*check-for-disallowed-answer* t))
        (when (answer-disallowed-p answer)
	  (process-new-row-msg "Row answer contains disallowed symbol.")
	  (return-from process-new-row nil)))
      (setq constraint-alist (row-constraints row))
      (when constraint-alist
	(with-clock-off constraint-simplification
	  (setf (row-constraints row)
                (setq constraint-alist (simplify-constraint-alist constraint-alist)))))
      (dolist (x constraint-alist)
        (when (eq false (cdr x))
          (process-new-row-msg "Row constraint is false.")
          (return-from process-new-row nil)))
      (WHEN (AND (USE-FUNCTION-CREATION?) (EQUALITY-P WFF))
	(LET* ((ARGS (ARGS WFF))
	       (VARS1 (VARIABLES (FIRST ARGS)))
	       (VARS2 (VARIABLES (SECOND ARGS))))
;;	(WHEN (AND (SET-DIFFERENCE VARS1 VARS2)
;;		   (SET-DIFFERENCE VARS2 VARS1))
;;	  (LET* ((VARS (INTERSECTION VARS1 VARS2))
;;		 (FN (DECLARE-FUNCTION (NEWSYM) (LENGTH VARS)))
;;		 (VAL (MAKE-COMPOUND* FN VARS)))
	  (when (and vars1 vars2 (null (intersection vars1 vars2)))	;create only constants
	    (let* ((vars nil)
		   (fn (declare-constant (newsym)))
		   (val fn))
	      (IF VARS
		  (SETF (FUNCTION-CREATED-P FN) T)
		  (SETF (CONSTANT-CREATED-P FN) T))
	      (WHEN (EQ :RPO (USE-TERM-ORDERING?))
		(RPO-ADD-CREATED-FUNCTION-SYMBOL FN))
	      (SETF (ROW-WFF ROW) (SETQ WFF (CONJOIN
					      (MAKE-EQUALITY (FIRST ARGS) VAL)
					      (MAKE-EQUALITY (SECOND ARGS) VAL))))
	      (SETQ AND-SPLIT-THIS T)))))
      (when (OR AND-SPLIT-THIS (use-and-splitting?) (use-clausification?))
	(when (and-split (lambda (x)		;call another function?  record on parent?
                           (insert-wff-into-agenda x agenda-value *agenda-of-other-wffs-to-process* t))
			 row wff answer :pos nil)	
	  (process-new-row-msg "Row wff will be and-split.")
	  (return-from process-new-row nil)))
      (when (and (use-condensing?) (row-bare-p row) (not (literal-p wff)) (clause-p wff))
        (with-clock-on condensing
          (let ((wff* (condenser wff)))
            (unless (eq wff wff*)
              (setf (row-wff row) (setf wff wff*))
              (setf (row-reason row) (list 'condense (row-reason row)))))))
      (unless (or (not (use-subsumption?))
		  (and (use-simplification-by-units?) (row-bare-unit-p row))
		  (row-embedding-p row))
	(when (forward-subsumed row)
	  (process-new-row-msg "Row is forward subsumed.")
	  (return-from process-new-row nil)))
      (dolist (fun (pruning-tests?))
	(when (funcall fun row)
	  (process-new-row-msg "Row is unaccepable.")
	  (return-from process-new-row nil)))
      (when (use-embedded-rewrites?)
	(make-embeddings #'record-new-embedding row))
      (prog->
	(SETF (ROW-WFF ROW) (SETQ WFF (FLATTEN-TERM (ROW-WFF ROW) NIL)))
	(renumber-row row)
        (set-row-number row (1+ *number-of-rows*))
	(when (prog1 (record-new-row-to-give row) (setq *printing-deleted-messages* nil))
	  (incf *number-of-rows*)
	  (when (print-rows-when-derived?)
	    (print-derived-row row))
	  (unless (or (not (use-subsumption?))
		      (eq :forward (use-subsumption?))
		      (and (use-simplification-by-units?)
			   (neq :forward (use-simplification-by-units?))
			   (row-bare-unit-p row))
		      (row-embedding-p row))
	    (backward-subsumption
             (lambda (subsumed-row)
               (if recursive-unstore
                   (RECURSIVELY-unstore-wff subsumed-row "Subsumed" (LAMBDA (X) (EQ ROW X)))
                   (unstore-wff subsumed-row "Subsumed")))
             (MAKE-ROW0 :WFF WFF	;NOT RENUMBERED
                        :CONSTRAINTS CONSTRAINT-ALIST
                        :ANSWER ANSWER
                        :CONTEXT (ROW-CONTEXT ROW)
                        :REASON (ROW-REASON ROW)))
            (setq *printing-deleted-messages* nil))
          (rowset-insert row *rows*)
	  (when (eq false wff)
            (if (row-constrained-p2 row)
                (rowset-insert row *constraint-rows*)
                (rowset-insert row *false-rows*)))
	  (store-derived-wff row)
	  (unless (row-embedding-p row)
	    (with-clock-on backward-simplification
	      (backward-demodulate-by row)))))
      nil)))

(defun row-pref (row)
  (funcall (agenda-ordering-function?) row))

(defun agenda-item-row (form)
  (ecase (car form)
    (giver
      (second form))
    (process-new-row
      (second form))))

(defun agenda-item-val (form)
  (ecase (car form)
    (giver
     (third form))
    (process-new-row
     (third form))))

(defun same-agenda-item-p (form1 form2)
  (let ((row1 (agenda-item-row form1))
	(row2 (agenda-item-row form2)))
    (and (iff (row-number row1) (row-number row2))
	 (implies (not (use-subsumption-by-false?))
		  (neq false (row-wff row1)))	;keep other proofs
	 (equal-p (row-wff row1) (row-wff row2))
	 (equal-alist-p (row-constraints row1) (row-constraints row2) nil)
	 (equal-p (row-answer row1) (row-answer row2))
	 ;; something for case
         (equal (row-context row1) (row-context row2))
	 )))

(defun unstore-agenda-item (form)
  (ecase (first form)
    (giver
     (unstore-wff (second form) "Deleted because agenda full")
     (incf *number-of-agenda-full-deleted-rows*))))

(defun insert-wff-into-agenda (row val agenda &optional at-front)
  (let ((v (if (row-number row)
               `(giver ,row ,val)
               `(process-new-row ,row ,val))))
    (push v (row-agenda-value row))
    (agenda-insert v val agenda at-front)))

(defun delete-wff-from-agenda (row agenda)
  (dolist (x (row-agenda-value row))
    (agenda-delete x (agenda-item-val x) agenda))
  (setf (row-agenda-value row) nil))

(defun record-new-embedding (row)
  (insert-wff-into-agenda row 0 *agenda-of-new-embeddings-to-process*))

(defun record-new-input-wff (row)
  (insert-wff-into-agenda row 0 *agenda-of-input-wffs-to-process*))

(defun record-backward-simplifiable-wff (row)
  (cond
   ((eq false (row-wff row))
    (insert-wff-into-agenda row 0 *agenda-of-false-wffs-to-process*))
   (t
    (insert-wff-into-agenda row 0 *agenda-of-backward-simplifiable-wffs-to-process* t))))

(defun record-new-derived-row (row)
  (cond
   ((eq false (row-wff row))
    (insert-wff-into-agenda row 0 *agenda-of-false-wffs-to-process*))
   (t
    (mvlet (((:values row-pref at-front) (row-pref row)))
      (insert-wff-into-agenda row (cons 2 row-pref) *agenda-of-other-wffs-to-process* at-front)))))

(defun record-new-row-to-give (row)
  (cond
   ((eq false (row-wff row))
    (insert-wff-into-agenda row 0 *agenda-of-false-wffs-to-process*))
   (t
    (mvlet (((:values row-pref at-front) (row-pref row)))
      (insert-wff-into-agenda row
			      (cons (if (<= (row-level row) (or (level-pref-for-giving?) 0)) 3 4) row-pref)
                              *agenda*
			      at-front)))))

(defun giver (given-row &optional (agenda-value (row-agenda-value given-row)))
  (declare (ignore agenda-value))
  (unless (row-present-in-context-p given-row)
    (return-from giver nil))
  (incf *number-of-given-rows*)
  (print-given-row given-row)
  (when (use-replacement-resolution-with-x=x?)
    (when (resolve-with-x=x given-row)
      (return-from giver nil)))
  (store-given-row given-row)
  (when (eq false (row-wff given-row))
    (cond
     ((not (row-constrained-p2 given-row))
      (setq *proof* given-row)
      (when (print-final-rows?)
        (print-final-row given-row))
      (return-from giver t))
     (t
      (give-constraint-row given-row)
      (return-from giver nil))))
  (let ((use-factoring? (use-factoring?)))
    (when (and use-factoring?
               (implies (eq :pos use-factoring?) (row-positive-p given-row))
               (implies (eq :neg use-factoring?) (row-negative-p given-row)))
      (with-clock-on factoring
        (factorer given-row))))
  (when (use-resolution?)
    (with-clock-on resolution
      (resolver given-row)))
  (when (use-hyperresolution?)
    (with-clock-on resolution
      (let ((*negative-hyperresolution* nil))
        (hyperresolver given-row))))
  (when (use-negative-hyperresolution?)
    (with-clock-on resolution
      (let ((*negative-hyperresolution* t))
        (hyperresolver given-row))))
  (when (use-ur-resolution?)
    (with-clock-on resolution
      (ur-resolver given-row)))
#+ignore
  (when (use-ur-pttp?)
    (with-clock-on resolution
      (ur-pttp given-row)))
  (when (use-paramodulation?)
    (with-clock-on paramodulation
      (paramodulater-from given-row)
      (unless (row-embedding-p given-row)
        (paramodulater-to given-row))))
  (when (use-resolve-code?)
    (with-clock-on resolution
      (code-resolver given-row)))
  nil)

(defun give-constraint-row (given-row)
  ;; given-row is of of the form 'constraints -> false'
  (WHEN (AND (ROW-FROM-CONCLUSION-P GIVEN-ROW)	;assumed consistent otherwise
             (ROW-CONSTRAINT-COVERAGE (ROWS :ROWSET *CONSTRAINT-ROWS* :REVERSE T)))
    (RECORD-NEW-DERIVED-ROW
     (MAKE-ROW :WFF FALSE
               :ANSWER (LET ((N 0))
                         (DISJOIN*
                          (ROWS :COLLECT (LAMBDA (X) (INSTANTIATE (ROW-ANSWER X) (INCF N)))
                                :ROWSET *CONSTRAINT-ROWS*
                                :REVERSE T)))
;;?            :supported (row-supported row)
;;?            :sequential (row-sequential row)
               :context (row-context given-row)
               :REASON `(COMBINE ,@(ROWS :ROWSET *CONSTRAINT-ROWS* :REVERSE T))))
    (ROWSET-DELETE GIVEN-ROW *CONSTRAINT-ROWS*)))

(defun break-snark ()				;ttp
  (setq *break-snark?* t))

(defun initialize-propositional-abstraction-of-input-wffs ()
  (let ((clause-set (make-dp-clause-set)))
    (dp-insert (list (list (function-name *=*) (function-arity *=*))) clause-set)
    (setf *propositional-abstraction-of-input-wffs* clause-set)))

(defun check-propositional-abstraction-of-input-wffs ()
  ;; clause-set should be checkpointed so that
  ;; assumptions and conclusions can be removed, e.g., by new-row-context
  (with-clock-on satisfiability-testing
    (let ((clause-set *propositional-abstraction-of-input-wffs*))
      (prog->
        (mapnconc-agenda *agenda-of-input-wffs-to-process* ->* x)
        (second x -> row)
        (row-wff row -> wff)
        (quote t -> *propositional-abstraction-term-to-lisp*)
        (term-to-lisp wff -> wff*)
        (cond
         ((eq false wff*)
          (return-from check-propositional-abstraction-of-input-wffs nil))
         ((neq true wff*)
          (dp-insert-wff wff* clause-set nil)))
        nil)
;;    (dp-clauses 'print clause-set)
      (let ((dp-tracing nil)
            (dp-tracing-choices nil))
        (dp-satisfiable-p clause-set
                          :find-all-models nil
                          :print-summary nil
                          :print-warnings nil
                          :branch-limit 10000000)))))

(defun closure-init ()
  (setq *proof* nil)
  (when (use-assertion-analysis?)
    (complete-assertion-analysis))
  (when critique-options
    (with-clock-on printing
      (critique-options)))
  (unless rewrites-initialized
    (initialize-rewrites)
    (setq rewrites-initialized t))
  (unless (use-closure-when-satisfiable?)
    (when (check-propositional-abstraction-of-input-wffs)
      (with-clock-on printing
        (warn "Propositional abstraction of input is satisfiable."))
      (return-from closure-init :satisfiable)))
  nil)

(defun closure (&key
		(number-of-given-rows-limit (number-of-given-rows-limit?))
		(number-of-rows-limit (number-of-rows-limit?))
		(run-time-limit (run-time-limit?))
		(only-unnumbered-rows nil)
		(listen-for-commands (listen-for-commands?)))
  (let ((*print-pretty* nil) (*print-radix* nil) (*print-base* 10.))
    (unwind-protect
      (progn
	(setq *snark-is-running* t)
	(let ((v (closure-init)))
	  (when v
	    (return-from closure v)))
	(when number-of-given-rows-limit
	  (incf number-of-given-rows-limit *number-of-given-rows*))
	(when number-of-rows-limit
	  (incf number-of-rows-limit *number-of-rows*))
	(when run-time-limit
	  (incf run-time-limit (total-run-time)))
        #+lcl5.0
        (when listen-for-commands
          (clear-input))
	(loop
	  (when (and number-of-given-rows-limit
                     (<= number-of-given-rows-limit *number-of-given-rows*))
	    (return :number-of-given-rows-limit))
          (when (and number-of-rows-limit
                     (<= number-of-rows-limit *number-of-rows*))
	    (return :number-of-rows-limit))
          (when (and run-time-limit
                     (<= run-time-limit (total-run-time)))
	    (return :run-time-limit))
          (when *break-snark?*
	    (clear-input)
	    (setq *break-snark?* nil)
	    (break "Break in closure at user request."))
	  (when listen-for-commands
	    (case (read-char-no-hang)
	      ((nil)
	       )
	      ((#\Q #\q)
	       (return :user-quit))
	      ((#\B #\b)
	       (with-clock-on halted
		 (clear-input)
		 (break "Break in closure at user request.")))
	      (otherwise
               (with-clock-on halted
                 (clear-input)
                 (when (yes-or-no-p "Stop now? ")
                   (return :user-quit))))))
	  (when (and only-unnumbered-rows
		     (let ((v (agendas-first *agendas*)))
		       (and v (row-number (second v)))))
	    (return :only-unnumbered-rows))
	  (prog->
	    (pop-agendas *agendas* -> form)
	    (cond
             ((null form)
              (return :agenda-empty))
             ((apply (car form) (cdr form))
              (return :proof-found))))))
      (setq *snark-is-running* nil)
      (when (print-summary-when-finished?)
        (terpri)
        (print-summary)
        (when (print-clocks-when-finished?)
	  (terpri-comment)
	  (print-clocks))
        (when (print-term-memory-when-finished?)
	  (terpri-comment)
	  (print-term-memory))
        (when (print-agenda-when-finished?)
	  (terpri-comment)
	  (print-agendas *agendas*)))
      (nocomment))))

;;; wffs are stored with variables in block 0
;;;  these are used directly for demodulation and subsumption
;;; given wff is renumbered to have variables in block 1
;;; additional inference operation inputs are renumbered to have variables in block 2, 3, ...
;;; result of inference operation will have variables in blocks 1, 2, 3, ... (but not 0)
;;; and possibly "temporary" variables as well

;;; main.lisp EOF
