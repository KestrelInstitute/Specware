;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: cycl.lisp
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

;;; Example usage:
;;; (defpackage :cycl)
;;; (defpackage :km)
;;; (initialize-km->cycl)
;;; (initialize)
;;; (use-cycl-symbols)
;;; (let ((data (make-cycl-data)))
;;;   (extract-cycl-data (read-cycl-assertion-file cycl-file1) data)
;;;    :
;;;   (extract-cycl-data (read-cycl-assertion-file cycl-fileN) data)
;;;
;;;   (extract-cycl-data (read-km->cycl-assertion-file km-file1) data)
;;;    :
;;;   (extract-cycl-data (read-km->cycl-assertion-file km-fileN) data)
;;;   (eval-cycl-data data))

;;; some restrictions on CycL input into SNARK
;;;
;;; every CycL symbol X (except #$Thing) that is used as a sort
;;; should be the subject of an axiom of the form (#$genls X Y)
;;; this is how sorts are recognized when reading CycL input into SNARK
;;;
;;; every CycL symbol X that is used as a relation or function
;;; should be the subject of an axiom of the form (#$arity X N)
;;; this is how relations and functions are recognized when reading CycL input into SNARK
;;;
;;; every Cycl symbol X that is used as a function
;;; should be the subject of an axiom of the form (#$resultIsa X Y) or (#$resultGenl X Y)
;;; this is how functions are distinguished from relations when reading CycL input into SNARK

;;; to do:
;;; nonfixed arity relations and functions
;;; handle arg#Genl and resultGenl
;;; special case for #$Thing sort; replace #$Thing by top-sort?
;;; disjointness or partition information
;;; interpret expressions like (#$isa X #$symmetricBinaryPredicate)

(eval-when (:compile-toplevel :load-toplevel)
  ;; the following causes #$Thing etc. in this file
  ;; to be read into the CYCL package
  (setf *hash-dollar-package* cl-user::*cycl-package*))

(defun cycl-package ()
  cl-user::*cycl-package*)

(declare-snark-option use-cycl-symbols nil nil)

(declaim (special *hash-dollar-package* *hash-dollar-readtable*))

(defparameter *cycl-aliases*
  '(
    (true    . #$True)
    (false   . #$False)
    (not     . #$not)
    (and     . #$and)
    (or      . #$or)
    (xor     . #$xor)		;variable arity vs. binary?
    (implies . #$implies)
    (iff     . #$equivalent)	;variable arity vs. binary?
    (forall  . #$forAll)
    (exists  . #$thereExists)
;    (=       . #$equals)
    (instance-of . #$isa)
    (subclass-of . #$genls)
    ))

(defparameter *cycl-sort-aliases*
  '(
    (#$RealNumber         real)
    (#$RationalNumber     rational)
    (#$Integer            integer)
    (#$EvenNumber         even)
    (#$OddNumber          odd)
    (#$PositiveNumber     positive)
    (#$NegativeNumber     negative)
    (#$PositiveInteger    positive-integer)
    (#$NegativeInteger    negative-integer)
    (#$NonNegativeNumber  nonnegative)
    (#$NonNegativeInteger nonnegative-integer)
    ))

(defmethod use-cycl-symbols :before (&optional (value t))
  (cond
   (value
    (unless (use-lisp-types-as-sorts?)
      (use-lisp-types-as-sorts t))
    (dolist (x *cycl-aliases*)
      (create-aliases-for-symbol (cdr x) (input-symbol (car x))))
    (dolist (x *cycl-sort-aliases*)
      (create-aliases-for-sort (first x) (input-sort (second x))))
    (declare-logical-symbol '#$thereExistsExactly
                            :input-function #'input-there-exists-exactly-quantification)
    (declare-logical-symbol '#$thereExistsAtMost
                            :input-function #'input-there-exists-at-most-quantification)
    (declare-logical-symbol '#$thereExistsAtLeast
                            :input-function #'input-there-exists-at-least-quantification)
    (declare-disjoint-subsorts '#$Thing '#$SetOrCollection 'number)
    (declare-function '#$TheSetOf :any :input-function #'input-the-set-of)
    (declare-relation '#$elementOf :any)
    (initialize-cycl-read-action-table))
   (t
    nil)))

(defun input-there-exists-exactly-quantification (head args polarity)
  (declare (ignore head args polarity))
  (unimplemented))

(defun input-there-exists-at-most-quantification (head args polarity)
  (declare (ignore head args polarity))
  (unimplemented))

(defun input-there-exists-at-least-quantification (head args polarity)
  (declare (ignore head args polarity))
  (unimplemented))

(defun input-the-set-of (head args polarity)
  (declare (ignore polarity))
  (assert-n-arguments-p head args 2)
  (assert-can-be-variable-name-p (first args))
  (unimplemented))

(defvar *cycl-read-action-table*)		;for positive assertions
(defvar *cycl-read-actionn-table*)		;for negative assertions
(defvar *cycl-data*)

(defstruct (cycl-symbol
            (:constructor make-cycl-symbol (name)))
  (name nil :read-only t)
  (cached-sort-p none)
  (cached-function-p none)
  (genls-assertions nil) (isa-assertions nil)

  (arg1-genl-assertions nil) (arg1-isa-assertions nil) (arg1-format-assertions nil)
  (arg2-genl-assertions nil) (arg2-isa-assertions nil) (arg2-format-assertions nil)
  (arg3-genl-assertions nil) (arg3-isa-assertions nil) (arg3-format-assertions nil)
  (arg4-genl-assertions nil) (arg4-isa-assertions nil) (arg4-format-assertions nil)
  (arg5-genl-assertions nil) (arg5-isa-assertions nil) (arg5-format-assertions nil)
  (arg6-genl-assertions nil) (arg6-isa-assertions nil) (arg6-format-assertions nil)
  (arg7-genl-assertions nil) (arg7-isa-assertions nil) (arg7-format-assertions nil)
  (arg8-genl-assertions nil) (arg8-isa-assertions nil) (arg8-format-assertions nil)
  (arg9-genl-assertions nil) (arg9-isa-assertions nil) (arg9-format-assertions nil)
  (args-genl-assertions nil) (args-isa-assertions nil)
  (result-genl-assertions nil) (result-isa-assertions nil)
  (not-isa-assertions nil)
  (arity-assertions nil)
  (comment-assertions nil)
  (genl-attributes-assertions nil)
  (genl-inverse-assertions nil)
  (genl-preds-assertions nil)
  (inter-arg-isa1-2-assertions nil)
  (inter-arg-isa1-3-assertions nil)
  (inter-arg-isa1-4-assertions nil)
  (inter-arg-isa1-5-assertions nil)
  (inter-arg-isa2-3-assertions nil)
  (inter-arg-isa2-4-assertions nil)
  (inter-arg-isa2-5-assertions nil)
  (inter-arg-isa3-4-assertions nil)
  (inter-arg-isa3-5-assertions nil)
  (inter-arg-isa4-5-assertions nil)
  )

(defstruct (cycl-data
            (:constructor make-cycl-data0 ()))
  (symbol-table (make-hash-table) :read-only t)
  (unclassified-assertions nil) unclassified-assertions-last)

(defun make-cycl-data ()
  (make-cycl-data0))

(defmacro set-cycl-read-action00 (symbol &optional slot-name)
  (declare (ignore slot-name))
  `(setf (gethash ',symbol *cycl-read-action-table*)
         (lambda (wff assertion)
           (declare (ignore assertion))
           (warn "Ignoring formula ~A." wff)
           t)))

(defmacro set-cycl-read-action01 (symbol slot-name)
  `(setf (gethash ',symbol *cycl-read-action-table*)
         (lambda (wff assertion)
           (cond
            ((and (eql 3 (length wff))
                  (can-be-sort-name-p (second wff))
                  (can-be-sort-name-p (third wff)))
             (pushnew assertion (,slot-name (find-or-create-cycl-symbol-table-entry (second wff)))
                      :test #'equal)
             t)
            (t
             (warn "Formula ~A is not of the form (~A SORT SORT)." wff (first wff))
             nil)))))

(defmacro set-cycl-read-action02 (symbol slot-name)
  `(setf (gethash ',symbol *cycl-read-action-table*)
         (lambda (wff assertion)
           (cond
            ((and (eql 3 (length wff))
                  (can-be-constant-name-p (second wff))
                  (can-be-sort-name-p (third wff)))
             (pushnew assertion (,slot-name (find-or-create-cycl-symbol-table-entry (second wff)))
                      :test #'equal)
             t)
            (t
             (warn "Formula ~A is not of the form (~A CONSTANT SORT)." wff (first wff))
             nil)))))

(defmacro set-cycl-read-action03 (symbol slot-name)
  `(setf (gethash ',symbol *cycl-read-action-table*)
         (lambda (wff assertion)
           (cond
            ((and (eql 3 (length wff))
                  (can-be-constant-name-p (second wff))
                  (stringp (third wff)))
             (pushnew assertion (,slot-name (find-or-create-cycl-symbol-table-entry (second wff)))
                      :test #'equal)
             t)
            (t
             (warn "Formula ~A is not of the form (~A CONSTANT STRING)." wff (first wff))
             nil)))))

(defmacro set-cycl-read-action04 (symbol slot-name)
  `(setf (gethash ',symbol *cycl-read-action-table*)
         (lambda (wff assertion)
           (cond
            ((and (eql 3 (length wff))
                  (can-be-constant-name-p (second wff))
                  (integerp (third wff))
                  (<= 1 (third wff) 5))
             (pushnew assertion (,slot-name (find-or-create-cycl-symbol-table-entry (second wff)))
                      :test #'equal)
             t)
            (t
             (warn "Formula ~A is not of the form (~A CONSTANT (INTEGER 1 5))." wff (first wff))
             nil)))))

(defmacro set-cycl-read-action98 (symbol &optional slot-name)
  (declare (ignorable slot-name))
  `(setf (gethash ',symbol *cycl-read-action-table*)
         (lambda (wff assertion)
           (declare (ignore assertion))
           (warn "Unimplemented formula ~A." wff)
           t)))

(defun initialize-cycl-read-action-table ()
  (setf *cycl-read-action-table* (make-instance '<table>))
  (setf *cycl-read-actionn-table* (make-instance '<table>))
  (setf (gethash '#$and *cycl-read-action-table*)
        (lambda (wff assertion)
          (mapc (lambda (conjunct)
                  (cycl-read-action
                   (list* (first assertion)
                          (if (eq 'assertion (first assertion)) conjunct (kwote conjunct))
                          (rest (rest assertion)))))
                (rest wff))
          t))
  (setf (gethash '#$not *cycl-read-action-table*)
        (lambda (wff assertion)
          (and (eql 2 (length wff))
               (cycl-read-actionn
                (list* (first assertion)
                       (if (eq 'assertion (first assertion)) (second wff) (kwote (second wff)))
                       (rest (rest assertion)))))))
  (setf (gethash '#$not *cycl-read-actionn-table*)
        (lambda (wff assertion)
          (and (eql 2 (length wff))
               (cycl-read-action
                (list* (first assertion)
                       (if (eq 'assertion (first assertion)) (second wff) (kwote (second wff)))
                       (rest (rest assertion)))))))
  (set-cycl-read-action00 #$genlMt)
  (set-cycl-read-action00 #$overlappingExternalConcept)
  (set-cycl-read-action00 #$synonymousExternalConcept)
  (set-cycl-read-action01 #$genls            cycl-symbol-genls-assertions)
  (set-cycl-read-action02 #$isa              cycl-symbol-isa-assertions)
  (set-cycl-read-action02 #$arg1Isa          cycl-symbol-arg1-isa-assertions)
  (set-cycl-read-action02 #$arg2Isa          cycl-symbol-arg2-isa-assertions)
  (set-cycl-read-action02 #$arg3Isa          cycl-symbol-arg3-isa-assertions)
  (set-cycl-read-action02 #$arg4Isa          cycl-symbol-arg4-isa-assertions)
  (set-cycl-read-action02 #$arg5Isa          cycl-symbol-arg5-isa-assertions)
  (set-cycl-read-action02 #$arg6Isa          cycl-symbol-arg6-isa-assertions)
  (set-cycl-read-action02 #$arg7Isa          cycl-symbol-arg7-isa-assertions)
  (set-cycl-read-action02 #$arg8Isa          cycl-symbol-arg8-isa-assertions)
  (set-cycl-read-action02 #$arg9Isa          cycl-symbol-arg9-isa-assertions)
  (set-cycl-read-action02 #$argsIsa          cycl-symbol-args-isa-assertions)
  (set-cycl-read-action02 #$resultIsa        cycl-symbol-result-isa-assertions)
  (set-cycl-read-action02 #$arg1Genl         cycl-symbol-arg1-genl-assertions)
  (set-cycl-read-action02 #$arg2Genl         cycl-symbol-arg2-genl-assertions)
  (set-cycl-read-action02 #$arg3Genl         cycl-symbol-arg3-genl-assertions)
  (set-cycl-read-action02 #$arg4Genl         cycl-symbol-arg4-genl-assertions)
  (set-cycl-read-action02 #$arg5Genl         cycl-symbol-arg5-genl-assertions)
  (set-cycl-read-action02 #$arg6Genl         cycl-symbol-arg6-genl-assertions)
  (set-cycl-read-action02 #$arg7Genl         cycl-symbol-arg7-genl-assertions)
  (set-cycl-read-action02 #$arg8Genl         cycl-symbol-arg8-genl-assertions)
  (set-cycl-read-action02 #$arg9Genl         cycl-symbol-arg9-genl-assertions)
  (set-cycl-read-action02 #$argsGenl         cycl-symbol-args-genl-assertions)
  (set-cycl-read-action02 #$resultGenl       cycl-symbol-result-genl-assertions)
  (set-cycl-read-action03 #$comment          cycl-symbol-comment-assertions)
  (set-cycl-read-action04 #$arity            cycl-symbol-arity-assertions)


  (set-cycl-read-action98 #$arg1Format       cycl-symbol-arg1-format-assertions)
  (set-cycl-read-action98 #$arg2Format       cycl-symbol-arg2-format-assertions)
  (set-cycl-read-action98 #$arg3Format       cycl-symbol-arg3-format-assertions)
  (set-cycl-read-action98 #$arg4Format       cycl-symbol-arg4-format-assertions)
  (set-cycl-read-action98 #$arg5Format       cycl-symbol-arg5-format-assertions)
  (set-cycl-read-action98 #$arg6Format       cycl-symbol-arg6-format-assertions)
  (set-cycl-read-action98 #$arg7Format       cycl-symbol-arg7-format-assertions)
  (set-cycl-read-action98 #$arg8Format       cycl-symbol-arg8-format-assertions)
  (set-cycl-read-action98 #$arg9Format       cycl-symbol-arg9-format-assertions)
  (set-cycl-read-action98 #$genlAttributes   cycl-symbol-genl-attributes-assertions)
  (set-cycl-read-action98 #$genlInverse      cycl-symbol-genl-inverse-assertions)
  (set-cycl-read-action98 #$genlPreds        cycl-symbol-genl-preds-assertions)
#|
  (set-cycl-read-actionn #$isa              cycl-symbol-not-isa-assertions)
|#
  )

(defun find-or-create-cycl-symbol-table-entry (name)
  (let ((table (cycl-data-symbol-table *cycl-data*)))
    (or (gethash name table)
        (setf (gethash name table) (make-cycl-symbol name)))))

(defun cycl-read-action (assertion)
  (let ((wff (assertion-wff assertion)))
    (cond
     ((and (consp wff)
           (let ((fn (gethash (first wff) *cycl-read-action-table*)))
             (and fn (funcall fn wff assertion))))
      t)
     (t
      (collect assertion (cycl-data-unclassified-assertions *cycl-data*))
      t))))

(defun cycl-read-actionn (assertion)
  ;; for negative assertions
  (let ((wff (assertion-wff assertion)))
    (cond
     ((and (consp wff)
           (let ((fn (gethash (first wff) *cycl-read-actionn-table*)))
             (and fn (funcall fn wff assertion))))
      t)
     (t
      nil))))

(defun extract-cycl-data (assertions &optional cycl-data)
  (unless cycl-data
    (setf cycl-data (make-cycl-data)))
  (unless (use-cycl-symbols?)
    (use-cycl-symbols t))
  (let ((*cycl-data* cycl-data))
    (mapc #'cycl-read-action assertions))
  cycl-data)

(defun map-cycl-data (fun cycl-data)
  (let ((*cycl-data* cycl-data)
        (symbols nil))
    (prog->
      (maphash (cycl-data-symbol-table cycl-data) ->* key symbol)
      (declare (ignore key))
      (push symbol symbols))
    (setf symbols (sort symbols #'constant-name-lessp :key #'cycl-symbol-name))
    (funcall fun '(declare-relation 'instance-of 2
                   :satisfy-code 'instance-of-satisfier
                   :rewrite-code 'instance-of-rewriter))
    (prog->
      (mapc symbols ->* symbol)
      (cycl-symbol-name symbol -> name)
      (when (cycl-symbol-sort-p symbol)
        (funcall fun `(DECLARE-SORT ',name))))
    (prog->
      (mapc symbols ->* symbol)
      (cycl-symbol-name symbol -> name)
      (mapc (cycl-symbol-genls-assertions symbol) ->* assertion)
      (funcall fun `(DECLARE-SUBSORT ',name ',(third (assertion-wff assertion)))))
    (prog->
      (mapc symbols ->* symbol)
      (cycl-symbol-name symbol -> name)
      (funcall fun `(DECLARE-CONSTANT ',name
                                             :sort ',(cycl-symbol-sort symbol)
                                             :documentation ',(cycl-symbol-documentation symbol))))
    (prog->
      (mapc symbols ->* symbol)
      (cycl-symbol-name symbol -> name)
      (cycl-symbol-arity symbol ->nonnil arity)
      (cond
       ((cycl-symbol-function-p symbol)
        (funcall fun `(DECLARE-FUNCTION ',name :any
                                        :input-function ',(require-n-arguments-function arity)
                                        :sort ',(cycl-symbol-function-sort symbol arity))))
       (t
        (funcall fun `(DECLARE-RELATION ',name :any
                                        :input-function ',(require-n-arguments-function arity)
                                        :sort ',(cycl-symbol-argument-sorts symbol arity))))))
    #+ignore
    (prog->
      (mapc symbols ->* symbol)
      (cycl-symbol-name symbol -> name)
      (when (cycl-symbol-sort-p symbol)
        (funcall fun `(DECLARE-RELATION ',name :any :input-function 'input-as-instance-of))))
    #+ignore
    (prog->
      (mapc symbols ->* symbol)
      (cycl-symbol-name symbol -> name)
      (when (cycl-symbol-sort-p symbol)
        (funcall fun `(ASSERT '(forall ((?x :sort ,name)) (instance-of ?x ,name)) :supported :uninherited))))
    (prog->
      (mapc (cycl-data-unclassified-assertions cycl-data) ->* assertion)
      (funcall fun assertion))
    nil))

(defun eval-cycl-data (cycl-data)
  (map-cycl-data 'eval cycl-data))

(defun print-cycl-data (cycl-data &key pretty package)
  (let* ((*print-pretty* pretty)
	 (*package* (if package (find-or-make-package package) *package*))
	 (*readtable* *hash-dollar-readtable*))
    (map-cycl-data (lambda (x) (print x) (terpri)) cycl-data)))

(defun cycl-symbol-isa (symbol x)
  (not (null (member x (cycl-symbol-isa-assertions symbol)
                     :key (lambda (x) (third (assertion-wff x)))))))

(defun cycl-symbol-documentation (symbol)
  ;; collect all the comment strings into a single string
  ;; use newline characters to separate the original comment strings
  (let ((strings nil))
    (dolist (assertion (cycl-symbol-comment-assertions symbol))
      (when strings
        (push (string #\Newline) strings))
      (push (third (assertion-wff assertion)) strings))
    (cond
     ((null strings)
      nil)
     ((null (rest strings))
      (first strings))
     (t
      (apply #'concatenate 'string strings)))))

(defun cycl-symbol-arity (symbol)
  (let (v)
    (cond
     ((and (setf v (cycl-symbol-arity-assertions symbol)) (null (rest v)))
      (third (assertion-wff (first v))))
     ((cycl-symbol-isa symbol '#$VariableArityRelation)
      :any)
     (t
      ;; some symbols don't have arity
      ;; function arity might not be declared
      #+ignore
      (error "Cannot determine arity of ~S." (cycl-symbol-name symbol))
      nil))))

(defun cycl-symbol-sort-p (symbol)
  (let ((v (cycl-symbol-cached-sort-p symbol)))
    (if (neq none v)
        v
        (setf (cycl-symbol-cached-sort-p symbol)
              (or (not (null (cycl-symbol-genls-assertions symbol)))
                  (eq '#$Thing (cycl-symbol-name symbol)))))))

(defun cycl-symbol-function-p (symbol)
  (let ((v (cycl-symbol-cached-function-p symbol)))
    (if (neq none v)
        v
        (setf (cycl-symbol-cached-function-p symbol)
              (or (cycl-symbol-isa symbol '#$NonPredicateFunction)
                  (not (null (cycl-symbol-result-isa-assertions symbol)))
                  (not (null (cycl-symbol-result-genl-assertions symbol))))))))

(defun cycl-symbol-arg-isa-sorts (symbol n)
  (mapcar #'cycl-assertion-sort
          (ecase n
            (1 (cycl-symbol-arg1-isa-assertions symbol))
            (2 (cycl-symbol-arg2-isa-assertions symbol))
            (3 (cycl-symbol-arg3-isa-assertions symbol))
            (4 (cycl-symbol-arg4-isa-assertions symbol))
            (5 (cycl-symbol-arg5-isa-assertions symbol))
            (6 (cycl-symbol-arg6-isa-assertions symbol))
            (7 (cycl-symbol-arg7-isa-assertions symbol))
            (8 (cycl-symbol-arg8-isa-assertions symbol))
            (9 (cycl-symbol-arg9-isa-assertions symbol)))))

(defun cycl-symbol-arg-genl-sorts (symbol n)
  (mapcar #'cycl-assertion-sort
          (ecase n
            (1 (cycl-symbol-arg1-genl-assertions symbol))
            (2 (cycl-symbol-arg2-genl-assertions symbol))
            (3 (cycl-symbol-arg3-genl-assertions symbol))
            (4 (cycl-symbol-arg4-genl-assertions symbol))
            (5 (cycl-symbol-arg5-genl-assertions symbol))
            (6 (cycl-symbol-arg6-genl-assertions symbol))
            (7 (cycl-symbol-arg7-genl-assertions symbol))
            (8 (cycl-symbol-arg8-genl-assertions symbol))
            (9 (cycl-symbol-arg9-genl-assertions symbol)))))

(defun cycl-symbol-args-isa-sorts (symbol)
  (mapcar #'cycl-assertion-sort (cycl-symbol-args-isa-assertions symbol)))

(defun cycl-symbol-args-genl-sorts (symbol)
  (mapcar #'cycl-assertion-sort (cycl-symbol-args-genl-assertions symbol)))

(defun cycl-symbol-result-isa-sorts (symbol)
  (mapcar #'cycl-assertion-sort (cycl-symbol-result-isa-assertions symbol)))

(defun cycl-symbol-result-genl-sorts (symbol)
  (mapcar #'cycl-assertion-sort (cycl-symbol-result-genl-assertions symbol)))

(defun cycl-assertion-sort (assertion)
  ;; extract the sort from arg#Isa and arg#Genl assertions
  (third (assertion-wff assertion)))

(defun cycl-sort-conjunction (isa-sorts genl-sorts)
  ;; only uses one arg#Isa assertion and no arg#Genl assertions
  (when genl-sorts
    (warn "Ignoring arg#Genl and resultGenl assertions."))
  (cond
   ((null isa-sorts)
    top-sort)
   ((null (rest isa-sorts))
    (first isa-sorts))
   (t
    (cons 'and isa-sorts))))

(defun cycl-symbol-sort (symbol)
  (let ((sorts (mapcar (lambda (assertion) (third (assertion-wff assertion)))
                       (cycl-symbol-isa-assertions symbol))))
    (cond
     ((null sorts)
      top-sort)
     ((null (rest sorts))
      (first sorts))
     (t
      (cons 'and sorts)))))

(defun cycl-symbol-argument-sorts (symbol arity)
  (let ((arg-sort-alist nil)
        (args-isa-sorts (cycl-symbol-args-isa-sorts symbol))
        (args-genl-sorts (cycl-symbol-args-genl-sorts symbol)))
    (let ((sort (cycl-sort-conjunction args-isa-sorts args-genl-sorts)))
      (unless (eq top-sort sort)
        (push (list t sort) arg-sort-alist)))
    (dotimes (n 9)
      (let ((n (- 9 n)))
        (when (or (eq :any arity) (<= n arity))
          (let ((isa-sorts (cycl-symbol-arg-isa-sorts symbol n))
                (genl-sorts (cycl-symbol-arg-genl-sorts symbol n)))
            (when (or isa-sorts genl-sorts)
              (let ((sort (cycl-sort-conjunction
                           (or isa-sorts args-isa-sorts)
                           (or genl-sorts args-genl-sorts))))
                (unless (eq top-sort sort)
                  (push (list n sort) arg-sort-alist))))))))
    arg-sort-alist))

(defun cycl-symbol-function-sort (symbol arity)
  (let ((result-sort (cycl-sort-conjunction
                      (cycl-symbol-result-isa-sorts symbol)
                      (cycl-symbol-result-genl-sorts symbol)))
        (arg-sort-alist (cycl-symbol-argument-sorts symbol arity)))
    (if (and (eq top-sort result-sort) (null arg-sort-alist))
        nil
        (cons result-sort arg-sort-alist))))

(defun cycl-file-test (&optional (case 0))
  (initialize)
  (use-cycl-symbols t)
  (let ((cycl-data (make-cycl-data)))
    (dolist (file
             (ecase case
               (0
                '("nori:research:snark:temp.cycl"))
               (1
                '(#+mcl "nori:research:snark:cycl-kernel.cycl"
                  #-mcl "cycl-kernel.cycl"))
               (2
                '(#+mcl "nori:research:snark:cyc-merged-ontology.cycl"
                  #-MCL "cyc-merged-ontology.cycl"))
               (3
                '(#+mcl "nori:research:snark:cycl-kernel.cycl"
                  #-mcl "cycl-kernel.cycl"
                  #+mcl "nori:research:snark:cyc-merged-ontology.cycl"
                  #-mcl "cyc-merged-ontology.cycl"))))
      (extract-cycl-data (read-cycl-assertion-file file) cycl-data))
    (setf it cycl-data)))

(defun cycl-test (&optional (case 1))
  (eval-cycl-data (cycl-file-test case)))

(eval-when (:compile-toplevel :load-toplevel)
  (setf *hash-dollar-package* nil))

;;; cycl.lisp EOF
