;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: options.lisp
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

(declaim (special *snark-globals* *tics*
		  *agenda* *agenda-of-other-wffs-to-process*))

(defvar *snark-options* nil)

(defmacro declare-snark-option (name &optional (default-value nil) (invisible-value :always-print))
  ;; example:
  ;; (declare-snark-option USE-FOO t)
  ;; yields the functions USE-FOO, DEFAULT-USE-FOO, USE-FOO?
  ;;
  ;; (USE-FOO value)  sets the value of the USE-FOO option
  ;; (USE-FOO)        sets the value of the USE-FOO option to T
  ;;
  ;; (DEFAULT-USE-FOO value)  sets the default value of the USE-FOO option
  ;; (DEFAULT-USE-FOO)        sets the default value of the USE-FOO option to T
  ;;
  ;; (USE-FOO?)          returns the value of the USE-FOO option
  ;; (DEFAULT-USE-FOO?)  returns the default value of the USE-FOO option
  ;;
  ;; (initialize) will initialize options to their default values
  ;;
  ;; DEFAULT-USE-FOO should be used BEFORE initialize to establish a
  ;; default value for foo for all future runs; USE-FOO should be used
  ;; AFTER initialize to change the value of foo for an individual run
  ;;
  ;; (print-options) will print the value of each SNARK option
  ;; whose value differs from its invisible value (:always-print
  ;; or :never-print can be specified instead of an invisible value)
  (cl:assert (or (symbolp name) (stringp name)))
  (setq name (intern (string name) :snark))
  (let ((snark-option-variable-name
         (intern (concatenate 'string "*%" (symbol-name name) "%*") :snark))
        (default-snark-option-variable-name
         (intern (concatenate 'string "*%" "DEFAULT-" (symbol-name name) "%*") :snark))
        (invisible-snark-option-variable-name
         (intern (concatenate 'string "*%" "INVISIBLE-" (symbol-name name) "%*") :snark))
        (snark-option-access-function-name
         (intern (concatenate 'string (symbol-name name) "?") :snark))
        (default-snark-option-function-name
         (intern (concatenate 'string "DEFAULT-" (symbol-name name)) :snark))
        (default-snark-option-access-function-name
         (intern (concatenate 'string "DEFAULT-" (symbol-name name) "?") :snark)))
  `(progn
     (unless (member ',name *snark-options*)
       (setq *snark-options* (nconc *snark-options* (list ',name)))
       (nconc *snark-globals*
              (list ',snark-option-variable-name))
       (nconc *snark-nonsave-globals*
              (list ',default-snark-option-variable-name
                    ',invisible-snark-option-variable-name)))

     (export '(,default-snark-option-access-function-name
               ,default-snark-option-function-name
               ,snark-option-access-function-name
               ,name)
             :snark)
     
     (defparameter ,default-snark-option-variable-name ,default-value)
     
     (defparameter ,invisible-snark-option-variable-name ,invisible-value)
     
     (defvar ,snark-option-variable-name ,default-snark-option-variable-name)
     
     (defun ,default-snark-option-access-function-name ()
       ,default-snark-option-variable-name)

     (defun ,default-snark-option-function-name (&optional (value t))
       (setq ,default-snark-option-variable-name value))	;affects only future runs
     
     (definline ,snark-option-access-function-name ()
       ,snark-option-variable-name)
     
     (defgeneric ,name (&optional value)
       (:method (&optional (value t))
         (setq ,snark-option-variable-name value))))))

(defmacro declare-snark-option2 (name &optional (default-value nil))
  `(declare-snark-option ,name ,default-value :never-print))

(declare-snark-option2 allow-keyword-constant-symbols t)
(declare-snark-option2 allow-keyword-proposition-symbols nil)
(declare-snark-option2 allow-keyword-function-symbols nil)
(declare-snark-option2 allow-keyword-relation-symbols nil)
(declare-snark-option2 allow-keyword-sort-symbols nil)

(declare-snark-option use-resolution nil)
(declare-snark-option use-hyperresolution nil)
(declare-snark-option use-negative-hyperresolution nil)
(declare-snark-option use-ur-resolution nil)
(declare-snark-option use-ur-pttp nil)
(declare-snark-option use-paramodulation nil)
(declare-snark-option use-factoring nil)
(declare-snark-option use-equality-factoring nil)
(declare-snark-option use-condensing t)
(declare-snark-option use-code-for-equality t)

(declare-snark-option use-unit-restriction nil)
(declare-snark-option use-input-restriction nil)
(declare-snark-option use-literal-ordering-with-resolution nil)
(declare-snark-option use-literal-ordering-with-hyperresolution nil)
(declare-snark-option use-literal-ordering-with-negative-hyperresolution nil)
(declare-snark-option use-literal-ordering-with-ur-resolution nil)
(declare-snark-option use-literal-ordering-with-paramodulation nil)

(declare-snark-option use-subsumption t)			;nil, :forward, t
(declare-snark-option use-subsumption-by-false :false)		;nil, :false, :forward, t
(declare-snark-option use-simplification-by-units t)		;nil, :forward, t
(declare-snark-option use-simplification-by-equalities t)	;nil, :forward, t
(declare-snark-option use-term-ordering :recursive-path)	;nil, :manual, :knuth-bendix, :recursive-path
(declare-snark-option use-term-ordering-cache nil nil)
(declare-snark-option use-default-ordering t)			;nil, :arity, :reverse, t
(declare-snark-option recursive-path-ordering-status :multiset)	;default status
(declare-snark-option knuth-bendix-ordering-status :left-to-right)

(declare-snark-option use-indefinite-answers nil)		;nil, :disjunctive, :conditional (UNIMPLEMENTED)
(declare-snark-option use-conditional-answer-creation nil)
(declare-snark-option use-constructive-answer-restriction nil)
(declare-snark-option use-answers-during-subsumption t)
(declare-snark-option use-constraint-solver-in-subsumption nil)
(declare-snark-option rewrite-terms-in-answer nil)
(declare-snark-option rewrite-terms-in-constraint nil)
(declare-snark-option use-embedded-rewrites t)
(declare-snark-option use-function-creation nil)
(declare-snark-option use-replacement-resolution-with-x=x nil)
(declare-snark-option use-paramodulation-only-into-units nil)
(declare-snark-option use-paramodulation-only-from-units nil)
(declare-snark-option use-single-replacement-paramodulation nil)

(declare-snark-option use-partitions nil nil)			;nil or list of partition ids
(declare-snark-option2 partition-communication-table nil)

(declare-snark-option assert-supported t)			;nil, t  :uninherited
(declare-snark-option assume-supported t)			;nil, t, :uninherited
(declare-snark-option prove-supported t)			;nil, t, :uninherited
(declare-snark-option assert-sequential nil)			;nil, t, :uninherited
(declare-snark-option assume-sequential nil)			;nil, t, :uninherited
(declare-snark-option prove-sequential nil)			;nil, t, :uninherited

(declare-snark-option2 assert-reason 'assertion)		;assertion, assumption
(declare-snark-option2 assert-context 1)			;1, :current

(declare-snark-option2 prove-closure t)

(declare-snark-option number-of-given-rows-limit nil)
(declare-snark-option number-of-rows-limit nil)
(declare-snark-option agenda-length-before-simplification-limit 10000)
(declare-snark-option agenda-length-limit 3000)
(declare-snark-option run-time-limit nil)
(declare-snark-option row-argument-count-limit nil nil)
(declare-snark-option row-weight-limit nil)
(declare-snark-option row-weight-before-simplification-limit nil)
(declare-snark-option level-pref-for-giving nil)
(declare-snark-option variable-weight 1)

(declare-snark-option agenda-ordering-function 'row-weight+depth)
(declare-snark-option pruning-tests '(row-weight-limit-exceeded))
(declare-snark-option pruning-tests-before-simplification '(row-weight-before-simplification-limit-exceeded))

(declare-snark-option use-clausification t)
(declare-snark-option use-clausification-rewrites nil)		;turned off 1999-07-30
(declare-snark-option use-equality-elimination nil)
(declare-snark-option use-magic-transformation nil)
(declare-snark-option use-and-splitting nil)
(declare-snark-option use-ac-connectives t)
(declare-snark-option use-kif-rewrites t)
(declare-snark-option use-assertion-analysis t)

(declare-snark-option use-unify-bag-constant-abstraction nil)
(declare-snark-option use-associative-unification nil)
(declare-snark-option use-dp-subsumption nil)
(declare-snark-option unify-bag-basis-size-limit 1000)

(declare-snark-option use-term-memory-deletion t)
(declare-snark-option use-sort-implementation :dp)	;:dp or :bdd or :km
(declare-snark-option use-rewrite-cache nil nil)	;size or nil

(declare-snark-option2 use-variable-name-sorts t)
(declare-snark-option2 use-well-sorting nil)		;nil, t, or :terms
(declare-snark-option2 use-extended-implications 'warn)	;nil, t, or warn
(declare-snark-option2 use-extended-quantifiers 'warn)	;nil, t, or warn
(declare-snark-option2 use-variable-heads 'warn)	;nil, t, or warn
(declare-snark-option2 use-sort-relativization nil)
(declare-snark-option2 use-quantifier-preservation nil)
(declare-snark-option2 use-kif-version :hpkb-with-ansi-kif)	;:hpkb-with-kif-3.0, :hpkb-with-ansi-kif

(declare-snark-option use-lisp-types-as-sorts nil nil)
(declare-snark-option use-numbers-as-constructors nil nil)

(declare-snark-option2 use-closure-when-satisfiable t)

(declare-snark-option2 listen-for-commands nil)

(declare-snark-option2 variable-to-lisp-function 'var-to-lisp2)

(declare-snark-option2 print-rows-when-given nil)
(declare-snark-option2 print-rows-when-derived t)
(declare-snark-option2 print-rows-when-processed nil)
(declare-snark-option2 print-final-rows t)
(declare-snark-option2 print-unorientable-rows t)
(declare-snark-option2 print-rewrite-orientation nil)	;1998-07-29

(declare-snark-option2 print-rows-test nil)

;;; the following options control how a row is printed
(declare-snark-option2 print-rows-shortened nil)
(declare-snark-option2 print-rows-prettily t)
(declare-snark-option2 print-row-answers t)
(declare-snark-option2 print-row-constraints t)
(declare-snark-option2 print-row-reasons t)
(declare-snark-option2 print-row-goals t)
(declare-snark-option2 print-row-partitions t)
(declare-snark-option2 print-row-length-limit nil)
(declare-snark-option2 print-given-row-lines-printing 2)
(declare-snark-option2 print-given-row-lines-signalling 1)

;;; the following options control what is printed when closure finishes
(declare-snark-option2 print-summary-when-finished t)
(declare-snark-option2 print-clocks-when-finished t)
(declare-snark-option2 print-term-memory-when-finished t)
(declare-snark-option2 print-agenda-when-finished t)

(declare-snark-option2 print-options-when-starting t)
(declare-snark-option2 print-assertion-analysis-notes t)
(declare-snark-option2 print-symbol-table-warnings t)
(declare-snark-option2 print-symbol-in-use-warnings t)

;;; the following options are for debugging
(declare-snark-option2 print-time-used nil)
(declare-snark-option2 trace-unify nil)
(declare-snark-option2 meter-unify-bag nil)		;nil, t, or number of seconds
(declare-snark-option2 trace-unify-bag-basis nil)
(declare-snark-option2 trace-unify-bag-bindings nil)
(declare-snark-option2 trace-dp-refute nil)
(declare-snark-option2 trace-rewrite nil)
(declare-snark-option2 trace-optimize-sparse-vector-expression nil)

(declare-snark-option test-option1 nil nil)	;kif-declare-sort
(declare-snark-option test-option2 nil nil)	;simplification-ordering-compare-equality-arguments
(declare-snark-option test-option3 nil nil)	;paramodulater for waldinger
(declare-snark-option test-option4 nil nil)	;temporal-reasoning.lisp
(declare-snark-option test-option5 nil nil)	;bind-variable-to-term
(declare-snark-option test-option6 nil nil)	;clausify
(declare-snark-option test-option7 nil nil)	;term memory test
(declare-snark-option test-option8 nil nil)	;unify-bag
(declare-snark-option test-option9 nil nil)	;rewriting during hyperresolution
(declare-snark-option test-option10 nil nil)	;instance-graph - insert in tm-store
(declare-snark-option test-option11 nil nil)	;instance-graph - insert in retrieve-g/i-terms
(declare-snark-option test-option12 nil nil)	;instance-graph - insert in retrieve-u-terms
(declare-snark-option test-option13 nil nil)	;instance-graph - insert uses bottom-up search
(declare-snark-option test-option14 nil nil)	;sparse-vector-expressions for indexing
(declare-snark-option test-option15 nil nil)	;NOP
(declare-snark-option test-option16 nil nil)	;pre 2002-02-08 paramodulater-to1 behavior
(declare-snark-option test-option17 nil nil)	;revert to nonspecial unification for jepd relation atoms
(declare-snark-option test-option18 nil nil)	;instance-graph - insert uses might-unify-p
(declare-snark-option test-option19 nil nil)	;revert to earlier rpo
(declare-snark-option test-option20 nil nil)	;rpo
(declare-snark-option test-option21 nil nil)	;maximum-intersection-size in optimize-sparse-vector-expression
(declare-snark-option test-option22 nil nil)	;turn off commutativity of equality
(declare-snark-option test-option23 nil nil)
(declare-snark-option test-option24 nil nil)
(declare-snark-option test-option25 nil nil)
(declare-snark-option test-option26 nil nil)
(declare-snark-option test-option27 nil nil)
(declare-snark-option test-option28 nil nil)
(declare-snark-option test-option29 nil nil)
(declare-snark-option test-option30 nil nil)

(defvar options-have-been-critiqued)

(defun initialize-options ()
  (setq options-have-been-critiqued nil)
  (dolist (name *snark-options*)
    (setf (symbol-value
           (intern (concatenate 'string "*%" (symbol-name name) "%*") :snark))
          (symbol-value
           (intern (concatenate 'string "*%" "DEFAULT-" (symbol-name name) "%*") :snark)))))

(defun finalize-options ()
  (dolist (name *snark-options*)
    (funcall name (symbol-value
                   (intern (concatenate 'string "*%" (symbol-name name) "%*") :snark)))))

(defun assert-snark-option-spec-p (x)
  ;; ttp: 5/23/00 18:15 Use ~s instead of ~S so that the package is displayed.
  (cl:assert (if (symbolp x)
                 (member x *snark-options*)
                 (and (listp x)
                      (eql 2 (length x))
                      (member (first x) *snark-options*)))
             ()
             "~S is not a SNARK option."
             x))

(defun assert-snark-option-specs-p (options)
  (dolist (x options)
    (assert-snark-option-spec-p x)))

(defun set-options (options)
  ;; ttp: 5/23/00 18:15 Do funcall instead of setting the symbol value
  ;; of the underlying variable so that "before" methods are invoked,
  ;; e.g. for use-code-for-lists.
  (assert-snark-option-specs-p options)
  (setq options-have-been-critiqued nil)
  (dolist (x options)
    (if (symbolp x)
        (funcall x t)
        (funcall (first x) (second x)))))

(defmacro let-options (options &body forms)
  (assert-snark-option-specs-p options)
  (list*
   'let
   (mapcar
    (lambda (x)
      (let (name value)
        (if (symbolp x)
            (setq name x value t)
            (setq name (first x) value (second x)))
        (list (intern (concatenate 'string "*%" (symbol-name name) "%*") :snark)
              value)))
    options)
   forms))

#+(and mcl (not openmcl)) (progn (pushnew '(let-options  . 1) ccl:*fred-special-indent-alist* :test #'equal) nil)

(defun print-options (&optional all)
  (terpri-comment)
  (format t "The current SNARK option values are")
  (dolist (name *snark-options*)
    (let ((value
	   (symbol-value
	    (intern (concatenate 'string "*%" (symbol-name name) "%*") :snark)))
          (default-value
           (symbol-value
            (intern (concatenate 'string "*%" "DEFAULT-" (symbol-name name) "%*") :snark)))
	  (invisible-value
	   (symbol-value 
	    (intern (concatenate 'string "*%" "INVISIBLE-" (symbol-name name) "%*") :snark))))
      (when (or all
                (and (neq :never-print invisible-value)
                     (or (eq :always-print invisible-value)
                         (neq value invisible-value))))
        (terpri-comment)
        (if (neql value default-value)
            (format t "   (~A ~S)" name value)
            (format t "      (~A ~S)" name value)))))
  (princ " ")
  nil)

(defmethod agenda-length-limit :before (&optional (value t))
  (mes::limit-agenda-length *agenda* value))

(defmethod agenda-length-before-simplification-limit :before (&optional (value t))
  (mes::limit-agenda-length *agenda-of-other-wffs-to-process* value))

;;; options.lisp EOF
