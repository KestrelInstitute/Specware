;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: globals.lisp
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

(defvar *snark-globals*
	'(
	  mes::*%backward-simplification-time%*
	  mes::*%backward-subsumption-time%*
          mes::*%clause-to-clause-subsumption-tests-time%*
          mes::*%condensing-time%*
	  mes::*%constraint-simplification-time%*
          mes::*%equality-factoring-time%*
	  mes::*%equality-ordering-time%*
	  mes::*%factoring-time%*
	  mes::*%forward-simplification-time%*
	  mes::*%forward-subsumption-time%*
	  mes::*%halted-time%*
          mes::*%satisfiability-testing-time%*
          mes::*%instance-graph-insertion-time%*
          mes::*%kif-input-time%*
	  mes::*%other-time%*
	  mes::*%paramodulation-time%*
	  mes::*%path-indexing-time%*
	  mes::*%printing-time%*
	  mes::*%resolution-time%*
	  mes::*%sortal-reasoning-time%*
          mes::*%temporal-reasoning-time%*
	  mes::*%term-hashing-time%*
	  mes::*%test1-time%*
	  mes::*%test2-time%*
	  mes::*%test3-time%*
	  mes::*clocks*
	  mes::*excluded-clocks*
          mes::*first-time-value*
	  mes::*last-time-value*
          mes::*nonce*
	  mes::*outputting-comment*
	  mes::*running-clocks*
          *standard-eql-numbering*
          *standard-equal-numbering*

          *cons*
	  *=*
	  *not*
	  *and*
	  *or*
	  *implies*
	  *implied-by*
	  *iff*
	  *xor*
	  *if*
	  *forall*
	  *exists*
	  *answer-if*	

	  *agenda*
	  *agenda-of-backward-simplifiable-wffs-to-process*
	  *agenda-of-false-wffs-to-process*
	  *agenda-of-input-wffs-to-process*
	  *agenda-of-new-embeddings-to-process*
	  *agenda-of-other-wffs-to-process*
	  *agendas*
          *allen*
          *assert-rewrite-polarity*
	  *assertion-analysis-function-info*
	  *assertion-analysis-patterns*
	  *assertion-analysis-relation-info*
	  *atom-hash-code*
	  *break-snark?*
	  *check-sorts-nontrivial*
	  *conditional-answer-connective*
	  *constant-info-table*
          *constraint-rows*
          *current-row-context*
          *cycl-data*
          *cycl-read-action-table*
          *cycl-read-actionn-table*
          *date-interval-primitive-relations*
          *date-day-function*
          *date-hour-function*
          *date-minute-function*
          *date-month-function*
          *date-scenario-constant*
          *date-second-function*
          *date-year-function*
          *date-year-function2*
          *default-hash-term-set-count-down-to-hashing*
          *default-path-index-alist-length-limit*
	  *default-path-index-delete-empty-nodes*
	  *default-path-index-size*
	  *dp-sort-intersections*
          *dr-universal-time-function-symbol*
	  *embedding-variables*
	  *extended-variant*
	  *false-rows*
	  *find-else-substitution*
          *finish-time-function-symbol*
          *form-author*
          *form-documentation*
          *form-name*
          *form-source*
	  *frozen-variables*
	  *gensym-variable-alist*
          *input-proposition-variables*
          *input-quote-term*
          *input-sort-wff*
          *input-wff-substitution2*
	  *interactive?
          *kif-assertion-options*
          *kif-def-kind*
          *kif-form*
	  *kif-subclass-declarations*
          *load-kif-file-phase*
          *load-kif-file-print*
          *load-kif-file-verbose*
          *load-kif-forms-to-assert*
          *load-kif-forms-to-eval*
	  *manual-ordering-results*
          *new-symbol-prefix*
	  *next-variable-number*
          *nonce*
          *number-of-new-symbols*
          *number-of-row-contexts*
	  *path-index*
	  *pp-margin*
	  *pp?*
	  *processing-row*
          *proof*
          *propositional-abstraction-of-input-wffs*
          *propositional-abstraction-term-to-lisp*
          *renumber-by-sort*
          *renumber-first-number*
	  *rewrite-count-warning*
	  *rewrites-used*
	  *row-count*
          *row-names*
	  *row2*
	  *rows*
	  *skolem-function-alist*
	  *snark-is-running*
          *sort-info-table*
          *sort-intersection-cache*
	  *sort-theory*
          *subsort-cache*
          *subsuming*
          *symbol-ordering*
	  *symbol-table*
	  *symbols-in-symbol-table*
	  *term-by-hash-array*
	  *term-memory*
	  *terpri-indent*
	  *tics*
	  *trace-rewrites?*
	  *unify-special*
	  *using-sorts*
	  *var-renaming-subst*
	  *variables*
	  *world-path-function-alist*
	  clause-subsumption
	  critique-options
	  it
          *last-row-number-before-interactive-operation*
	  map-atoms-first
	  modal-input-wff
	  *number-of-agenda-full-deleted-rows*
	  *number-of-backward-eliminated-rows*
	  *number-of-given-rows*
	  *number-of-rewrites*
	  *number-of-rows*
          *%checking-well-sorted-p%*
          *%check-for-well-sorted-atom%*
	  options-have-been-critiqued
	  options-print-mode
	  ordering-is-total
	  recursive-unstore
	  *rewrite-cache*
	  *rewrite-cache-hits*
	  *rewrite-cache-misses*
          *%rewrite-count%*
	  rewrite-strategy
	  rewrites-initialized
          *simplification-ordering-compare-equality-arguments-hash-table* 
	  subsumption-mark
	  time-mark


	  ;LDPP'
          dp-tracing
          dp-tracing-choices
          dp-tracing-models
          dp-tracing-state
          *assignment-count*
          *default-atom-choice-function*
          *default-atom-cost-function*
          *default-branch-limit*
          *default-convert-to-clauses*
          *default-cost-bound*
          *default-cost-bound-function*
          *default-dependency-check*
          *default-dimacs-cnf-format*
          *default-find-all-models*
          *default-minimal-models-only*
          *default-minimal-models-suffice*
          *default-model-test-function*
          *default-more-units-function*
          *default-print-summary*
          *default-print-warnings*
          *default-pure-literal-check*
          *default-time-limit*
	  *default-subsumption*
          *subsumption-show-count*
          *verbose-lookahead*
          *verbose-lookahead-show-count*
          *verbose-subsumption*
	  ))

(defvar *snark-nonsave-globals*
	'(
	  mes::*%assoc-cache-special-item%*
          mes::oset-default-key
          mes::oset-default-test
          mes::oset-default-make-element
	  mes::*prog->*-function-second-forms*
	  mes::*prog->-special-forms*

          $number-of-variable-blocks
          $number-of-variables-per-block
	  $number-of-variables-in-blocks

	  *all-both-polarity*
          *can-be-sort-name*		;bound only when creating sorts
          *cycl->kif-constants*
          *cycl->kif-functions*
          *hash-dollar-package*
          *hash-dollar-readtable*
	  *hash-term-not-found-action*
          *hash-term-only-computes-code*
          *hash-term-uses-variable-numbers*
          *input-wff*			;bound only by input-wff
          *kif-assertable-constant-slots*
          *kif-assertable-function-slots*
          *km->cycl-initialized*
          *km->kif-initialized*
          *cycl-aliases*
          *cycl-sort-aliases*
          *cycl-symbols*
          *km-reserved-words*
          *km-reserved-words-table*
	  *printing-deleted-messages*
          *read-assertion-file-commands*
          *read-assertion-file-format*
          *read-assertion-file-if-does-not-exist*
          *read-assertion-file-keywords*
          *read-assertion-file-package*
          *read-assertion-file-verbose*
          *redex-path*			;bound only by rewriter
          *refute-file-if-exists*
          *refute-file-ignore-errors*
          *refute-file-options*
          *refute-file-output-file*
          *refute-file-verbose*
	  *resolve-functions-used*
          *rewriting-row-context*	;bound only for rewriter
          *rpo-cache*			;bound only by rpo-compare-terms-top
          *rpo-cache-numbering*		;bound only by rpo-compare-terms-top
          *ac-rpo-cache*		;bound only by rpo-compare-terms-top
	  *snark-globals*
	  *snark-nonsave-globals*
	  *snark-options*
          *tptp-input-directory*
          *tptp-output-directory*
          *tptp-problem-name-suffix*

          $rcc8-composition-table *rcc8-composition-table*
          $time-iii-composition-table *time-iii-composition-table*
          $time-iip-composition-table
          $time-ipi-composition-table *time-ipi-composition-table*
          $time-ipp-composition-table
          $time-pii-composition-table *time-pii-composition-table*
          $time-pip-composition-table *time-pip-composition-table*
          $time-ppi-composition-table *time-ppi-composition-table*
          $time-ppp-composition-table *time-ppp-composition-table*
          $rcc8-relation-code
          $time-ii-relation-code
          $time-ip-relation-code
          $time-pi-relation-code
          $time-pp-relation-code

          $tip-primitive-relations
          $tip-all-relations
          $tip-ii-relations
          $tip-pp-relations
          $tip-pi-relations
          $tip-ip-relations
          $tip-equality-relations
          $tip-transitivity-table

	  bottom-sort
          constant-and-function-slots
	  constant-slots
          dp-prover
          dp-version
	  empty-subst
	  false
	  false-wff
	  float-internal-time-units-per-second
          function-slots
	  initialization-functions
          none
          sort-slots
	  top-sort
	  true
	  true-wff
	  ))

;;; more than one copy of SNARK can be run alternately
;;; by using SUSPEND-SNARK and RESUME-SNARK
;;;
;;; SUSPEND-SNARK re-initializes SNARK so the run can be continued
;;; only after RESUME-SNARK; a suspended SNARK can only be resumed once
;;;
;;; SUSPEND-SNARK saves the values of SNARK's global variables;
;;; RESUME-SNARK restores them
;;;
;;; SUSPEND-AND-RESUME-SNARK suspends the current SNARK and resumes
;;; another without unnecessarily re-initializing

(defun suspend-snark* ()
  (let ((state (gensym)))
    (setf (symbol-value state)
	  (mapcar (lambda (var)
                    (cons var
                          (if (boundp var)
                              (symbol-value var)
                              '%unbound%)))
		  *snark-globals*))
    state))

(defun resume-snark (state)
  (let ((l (and (boundp state) (symbol-value state))))
    (cond
      ((consp l)
       (setf (symbol-value state) nil)
       (mapc (lambda (x)
               (if (eq '%unbound% (cdr x))
                   (makunbound (car x))
                   (setf (symbol-value (car x)) (cdr x))))
	     l))
      (t
       (error "Cannot resume SNARK from state ~S." state)))
    nil))

(defun suspend-snark ()
  (prog1
    (suspend-snark*)
    (initialize)))

(defun suspend-and-resume-snark (state)
  (prog1
    (suspend-snark*)
    (resume-snark state)))

(defun audit-snark-globals ()
  ;; used for suspend/resume to make sure all necessary values are saved;
  ;; prints names of symbols that might have been overlooked
  (dolist (package-name '(:mes :snark))
    (let ((package (find-package package-name)))
      (do-symbols (x package)
	(when (and (boundp x) (eq package (symbol-package x)))
	  (unless (or (member x *snark-globals*) (member x *snark-nonsave-globals*))
	    (print x)))))))

;;; globals.lisp EOF
