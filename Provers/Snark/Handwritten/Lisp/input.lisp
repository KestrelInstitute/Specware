;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: input.lisp
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

(defvar *skolem-function-alist* nil)
(defvar skfnnum 0)
(defvar *var-renaming-subst* nil)		;ttp
(defvar *input-wff* nil)
(defvar *input-wff-substitution*)		;alist of (variable-name . variable) or (variable-name . skolem-term) pairs
(defvar *input-wff-modal-prefix*)
(defvar *input-quote-term* nil)
(defvar *input-sort-wff* nil)
(defvar *input-proposition-variables* nil)	;for cnf and boolean ring rewrites

(defun keyword-argument-list-P (x)
  (or (null x)
      (and (consp x)
	   (keywordp (first x))
	   (consp (rest x))
	   (keyword-argument-list-p (rest (rest x))))))

(defun can-be-name1 (x &optional keyok nullok ?ok)
  (and (symbolp x)
       (if nullok t (not (null x)))
       (if keyok t (not (keywordp x)))
       (neq none x)
       (let ((s (symbol-name x)))
         (and (neql 0 (length s))
              (if ?ok t (neql #\? (char s 0)))))))

(defun wild-card-p (x)
  ;; like Prolog variable _, each occurrence of ? is a distinct variable
  (and (can-be-name1 x nil nil t)
       (let ((s (symbol-name x)))
         (and (eql 1 (length s))
              (eql #\? (char s 0))))))

(defun can-be-free-variable-name-p (x &optional action)
  ;; a free variable in an input formula is represented
  ;; by a symbol whose first but not only character is "?"
  (or (and (can-be-name1 x nil nil t)
           (let ((s (symbol-name x)))
             (and (neql 1 (length s))
                  (eql #\? (char s 0)))))
      (and action (funcall action "~S cannot be the name of a free variable." x))))

(defun can-be-variable-name-p (x &optional action)
  ;; a bound variable is represented like a free variable, or by an ordinary symbol
  (or (and (can-be-name1 x nil nil t)
           (let ((s (symbol-name x)))
             (or (neql 1 (length s))	;cannot be wild-card
                 (neql #\? (char s 0)))))
      (and action (funcall action "~S cannot be the name of a variable." x))))

(defun can-be-constant-name-p (x &optional action)
  (or (can-be-name1 x (allow-keyword-constant-symbols?) t *input-quote-term*)
      (numberp x)
      (characterp x)
      (stringp x)
      (and action (funcall action "~S cannot be the name of a constant." x))))

(defun can-be-proposition-name-p (x &optional action)
  (or (can-be-name1 x (allow-keyword-proposition-symbols?))
      (and action (funcall action "~S cannot be the name of a proposition." x))))
                    
(defun can-be-function-name-p (x &optional action)
  (or (can-be-name1 x (allow-keyword-function-symbols?))
      (and action (funcall action "~S cannot be the name of a function." x))))

(defun can-be-predicate-name-p (x &optional action)
  (or (can-be-name1 x (allow-keyword-relation-symbols?))
      (and action (funcall action "~S cannot be the name of a relation." x))))

(defun can-be-sort-name-p (x &optional action)
  ;; must be at least two characters long
  ;; disallow names with "&" or "%" to avoid confusion with SNARK created sorts and variables
  (or *can-be-sort-name*
      (let ((x (kif-fix-sort-spec x)))
        (and (can-be-name1 x (allow-keyword-sort-symbols?))
             (neq top-sort x)
             (neq bottom-sort x)
             (neq 'and x)
             (neq 'or x)
             (neq 'not x)
             (let ((s (symbol-name x)))
	       (and (neq 1 (length s))
	            (not (find #\% s))
	            (or (null (symbol-package x)) (not (find #\& s)))))))
      (and action (funcall action "~S cannot be the name of a sort." x))))

(defun can-be-sort-name-or-conjunction-p (x &optional action)
  ;; allows conjunction of sort names too
  (if (and (consp x) (eq 'and (first x)))
      (every (lambda (x) (can-be-sort-name-p x action)) (rest x))
      (can-be-sort-name-p x action)))

(defun assert-can-be-free-variable-name-p (x)
  (can-be-free-variable-name-p x 'error))

(defun assert-can-be-variable-name-p (x)
  (can-be-variable-name-p x 'error))

(defun assert-can-be-constant-name-p (x)
  (can-be-constant-name-p x 'error))

(defun assert-can-be-proposition-name-p (x)
  (can-be-proposition-name-p x 'error))

(defun assert-can-be-function-name-p (x)
  (can-be-function-name-p x 'error))

(defun assert-can-be-predicate-name-p (x)
  (can-be-predicate-name-p x 'error))

(defun assert-can-be-sort-name-p (x)
  (can-be-sort-name-p x 'error))

(defun assert-can-be-constant-or-function-name-p (x)
  (or (can-be-constant-name-p x)
      (can-be-function-name-p x)
      (error "~S cannot be the name of a constant or function." x)))

(defun check-usable-head1 (head)
  ;; some operations cannot deal with function/relation symbols
  ;; with special input handling
  (when (function-input-function head)
    (error "~S cannot be used as a ~A here."
           (function-name head)
           (function-kind-string head)))
  head)

(defun cerror1 (datum &rest args)
  (apply #'cerror
         "Input it anyway, but this may result in additional errors."
         datum
         args))

(defun cerror2 (datum &rest args)
  (apply #'cerror
         "Ignore this sort declaration, but this may result in additional errors."
         datum
         args))

;;; Convert LISP S-expression for formula into correct internal form for theorem prover
;;; Also eliminate quantifiers and modal operators

(defun input-wff (wff &key (polarity :pos) (clausify nil))
  (setq *var-renaming-subst* nil)	;ttp
  (let ((*input-wff* wff)
        (*input-wff-substitution* nil)
	(*input-wff-modal-prefix* nil))
    (let ((usr (use-sort-relativization?)))
      (when usr
	(let ((l nil))
	  (dolist (x (input-variables-in-form wff nil nil))
	    (let ((sort (variable-sort (cdr x))))
	      (when (neq top-sort sort)
		(push (if t
			  `(instance-of ,(car x) ,sort)
			  `(,sort ,(car x)))
		      l))))
	  (when l
	    (setq wff (list 'implies
			    (if (null (rest l))
				(first l)
				(cons 'and (nreverse l)))
			    wff))))))
    (let ((wff* (input-wff1 wff polarity)))
      (when clausify
        (setq wff* (clausify wff*)))
      (values wff* nil *input-wff*))))

(defun input-wff1 (wff polarity)
  (cond
   ((atom wff)
    (input-atom wff polarity))
   ((can-be-free-variable-name-p (first wff))
    (case (use-variable-heads?)
      ((nil)
       (cerror "Convert it to a LIST-TO-ATOM form."
               "Formula ~S has a variable head." wff))
      (warn
       (warn "Formula ~S has a variable head; converting it to a LIST-TO-ATOM form." wff)))
    ;; this will only work if use-code-for-lists option is true
    (input-atom `(list-to-atom (list ,@wff)) polarity))
   (t
    (let ((head (input-relation-symbol (first wff) (or (list-p (rest wff)) 1))))
      (if (function-logical-symbol-p head)
          (let ((algrthm (function-input-function head)))
            (if algrthm
                (funcall algrthm head (rest wff) polarity)
                (make-compound* head (input-wffs1 head (rest wff) polarity))))
          (input-atom wff polarity))))))

(defun input-wffs1 (head args polarity)
  (input-wffs2 args polarity (function-polarity-map head)))

(defun input-wffs2 (wffs polarity polarity-map)
  (lcons (input-wff1 (first wffs) (map-polarity (first polarity-map) polarity))
	 (input-wffs2 (rest wffs) polarity (rest polarity-map))
	 wffs))

(defun input-quotation (head args polarity)
  (assert-n-arguments-p head args 1)
  (let ((*input-quote-term* t))
    (input-term (first args) polarity)))

(defun input-equality (head args polarity)
  (require-2-arguments head args polarity))

(defun input-disequality (head args polarity)
  (declare (ignore head))
  (make-compound *not* (input-equality *=* args (opposite-polarity polarity))))

(defun input-negation (head args polarity)
  (if (and (test-option6?) (use-clausification?))
      (negate0 (input-wffs1 head args polarity))
      (negate* (input-wffs1 head args polarity))))

(defun input-conjunction (head args polarity)
  (conjoin* (input-wffs1 head args polarity)))

(defun input-disjunction (head args polarity)
  (disjoin* (input-wffs1 head args polarity)))

(defun input-implication (head args polarity)
  (if (eql 2 (length args))
      (make-implication* (input-wffs1 head args polarity))
      (input-kif-forward-implication head args polarity t)))

(defun input-reverse-implication (head args polarity)
  (if (eql 2 (length args))
      (make-reverse-implication* (input-wffs1 head args polarity))
      (input-kif-backward-implication head args polarity t)))

(defun input-kif-forward-implication (head args polarity &optional rep)
  (assert-n-or-more-arguments-p head args 1)
  (when rep
    (report-not-2-arguments-implication head args))
  (input-wff1
   (cond
    ((null (rest args))
     (first args))
    ((null (rest (rest args)))
     `(implies ,(first args) ,(second args)))
    (t
     `(implies (and ,@(butlast args)) ,(first (last args)))))
   polarity))

(defun input-kif-backward-implication (head args polarity &optional rep)
  (assert-n-or-more-arguments-p head args 1)
  (when rep
    (report-not-2-arguments-implication head args))
  (input-wff1
   (cond
    ((null (rest args))
     (first args))
    ((null (rest (rest args)))
     `(implied-by ,(first args) ,(second args)))
    (t
     `(implied-by ,(first args) (and ,@(rest args)))))
   polarity))

(defun input-nand (head args polarity)
  (declare (ignore head))
  (input-wff1 `(not (and ,@args)) polarity))

(defun input-nor (head args polarity)
  (declare (ignore head))
  (input-wff1 `(not (or ,@args)) polarity))

(defun input-listof (head args polarity)
  (declare (ignore head))
  (input-terms args polarity))

(defun input-listof* (head args polarity)
  (assert-n-or-more-arguments-p head args 1)
  (nconc (input-terms (butlast args) polarity) (input-term (first (last args)) polarity)))

(defun input-list*-args (head args polarity)
  (make-compound head (input-listof* head args polarity)))

(defun input-equivalence (head args polarity)
  (cond
    ((null args)
     true)
    ((null (rest args))
     (input-wff1 (first args) polarity))
    ((and (not (null (cddr args))) (eql 2 (function-arity head)))
     (input-equivalence head (list (first args) (cons (function-name head) (rest args))) polarity))
    ((eq :both polarity)
     (make-equivalence* (input-wffs1 head args polarity)))
    ((catch 'needs-strict-polarity
       (make-equivalence* (input-wffs1 head args polarity)))
     )
    (t
     (let ((x (first args))
	   (y (if (null (cddr args)) (second args) (cons (function-name head) (rest args)))))
       (input-wff1 (if (eq :neg polarity)
                       `(or (and ,x ,y) (and (not ,x) (not ,y)))
                       `(and (implies ,x ,y) (implied-by ,x ,y)))
                   polarity)))))

(defun input-exclusive-or (head args polarity)
  (cond
    ((null args)
     false)
    ((null (rest args))
     (input-wff1 (first args) polarity))
    ((and (not (null (cddr args))) (eql 2 (function-arity head)))
     (input-exclusive-or
       head (list (first args) (cons (function-name head) (rest args))) polarity))
    ((eq :both polarity)
     (make-exclusive-or* (input-wffs1 head args polarity)))
    ((catch 'needs-strict-polarity
       (make-exclusive-or* (input-wffs1 head args polarity)))
     )
    (t
     (let ((x (first args))
	   (y (if (null (cddr args)) (second args) (cons (function-name head) (rest args)))))
       (input-wff1 (if (eq :neg polarity)
                       `(or (and ,x (not ,y)) (and (not ,x) ,y))
                       `(and (or ,x ,y) (or (not ,x) (not ,y))))
                   polarity)))))

(defun input-conditional (head args polarity)
  (assert-n-arguments-p head args 3)
  (cond
    ((eq :both polarity)
     (make-conditional
      (input-wff1 (first args) :both)
      (input-wff1 (second args) polarity)
      (input-wff1 (third args) polarity)
      nil
      head))
    ((catch 'needs-strict-polarity
       (make-conditional
        (input-wff1 (first args) :both)
        (input-wff1 (second args) polarity)
        (input-wff1 (third args) polarity)
        nil
        head))
     )
    (t
     (input-wff1 (if (eq :neg polarity)
                     `(or (and ,(first args) ,(second args))
                          (and (not ,(first args)) ,(third args)))
                     `(and (implies ,(first args) ,(second args))
                           (implies (not ,(first args)) ,(third args))))
                 polarity))))

;;;: ttp: 6/19/93 21:33  added setting *var-renaming-subst* so variables can be deciphered
(defun input-quantification (head args polarity)
  (cond
   ((eq :both polarity)
    (throw 'needs-strict-polarity nil))
   (t
    (unless (eql 2 (length args))
      ;; (forall (vars) form . forms) means (forall (vars) (implies (and . forms) form))
      ;; (exists (vars) form . forms) means (exists (vars) (and form . forms))
      (assert-n-or-more-arguments-p head args 2)
      (report-not-2-arguments-quantification head args)
      (setq args
            (list (first args)
                  (cond
                   ((eq *forall* head)
                    `(=> ,@(rest args)))
                   ((eq *exists* head)
                    `(and ,@(rest args)))))))
    (let ((var-specs (input-quantifier-variables (first args)))
          (form (second args))
          (substitution *input-wff-substitution*)
          *input-wff-substitution*)
      (cond
       ((or (and (eq :pos polarity) (eq *forall* head))
            (and (eq :neg polarity) (eq *exists* head)))
        ;; add (variable-name . variable) pairs to substitution
        (dolist (var-spec var-specs)
          (let ((var (first var-spec)))
            (push (cons var (if (getf (rest var-spec) :global)
                                (declare-variable-symbol var)
                                (make-variable-from-var-spec var-spec)))
                  substitution)
            (push (car substitution) *var-renaming-subst*)))
        (setq *input-wff-substitution* substitution))
       ((or (and (eq :pos polarity) (eq *exists* head))
            (and (eq :neg polarity) (eq *forall* head)))
        (let ((free-vars-in-form (input-variables-in-form form (mapcar #'first var-specs) substitution)))
          ;; add (variable-name . skolem-term) pairs to substitution
          (dolist (var-spec var-specs)
            (let ((var (first var-spec)))
              (push (cons var (if (use-quantifier-preservation?)
                                  (make-variable-from-var-spec var-spec)
                                  (create-skolem-term var-spec form free-vars-in-form)))
                    substitution))))
        (setq *input-wff-substitution* substitution))
       (t
        (unimplemented)))
      (when (or (eq *forall* head)
                (eq *exists* head))
        (let ((usr (use-sort-relativization?))
              (l nil))
          (dolist (var-spec var-specs)
            (let ((sort (getf (rest var-spec) :sort)))
              (when (and (neq top-sort sort)
                         (or usr (getf (rest var-spec) :sort-unknown)))
                (push (if t
                          `(instance-of ,(first var-spec) ,sort)
                          `(,sort ,(first var-spec)))
                      l))))
          (when l
            (setq form (list (if (eq *forall* head) 'implies 'and)
                             (if (null (rest l)) (first l) (cons 'and (nreverse l)))
                             form)))))
      (cond
       ((use-quantifier-preservation?)
        (make-compound
         head
         (input-terms (mapcar #'first var-specs) polarity)
         (input-wff1 form polarity)))
       (t
        (input-wff1 form polarity)))))))

(defun input-quantifier-variable (var-spec)
  ;; var-spec should be of form
  ;;  variable-name
  ;; or
  ;;  (variable-name . keyword-argument-list)
  ;; such as
  ;;  (variable-name :sort sort-name)
  ;; or
  ;;  (variable-name restriction-name . keyword-argument-list)
  ;; such as
  ;;  (variable-name restriction-name) - KIF
  ;; interpeted as
  ;;  (variable-name :sort restriction-name . keyword-argument-list)
  ;;
  ;; output is always of form
  ;;  (variable-name . keyword-argument-list)
  (cond
   ((atom var-spec)
    (setq var-spec (list var-spec)))
   ((and (evenp (length var-spec)) (eq top-sort (second var-spec)))
    (setq var-spec (cons (first var-spec) (cddr var-spec))))
   ((evenp (length var-spec))
    ;; restriction-name is interpreted as sort (possibly unknown)
    (cl:assert (eq (second var-spec) (getf (cddr var-spec) :sort (second var-spec))) ()
               "In quantification, ~S has both a restriction and a sort." var-spec)
    (setq var-spec
          (cond
           ((sort-name-or-conjunction-p (second var-spec))
            (list* (first var-spec) :sort (second var-spec) (cddr var-spec)))
           (t
            (list* (first var-spec) :sort (second var-spec) :sort-unknown t (cddr var-spec)))))))
  (cl:assert (keyword-argument-list-p (rest var-spec)) ()
	     "In quantification, ~S is not a keyword argument list." (rest var-spec))
  (let ((var (first var-spec))
        (sort (getf (rest var-spec) :sort none))
        (sort-unknown (getf (rest var-spec) :sort-unknown))
        (global (getf (rest var-spec) :global)))
    (if global
        (cl:assert (can-be-free-variable-name-p var) ()
                   "In quantification, ~S is not a global variable name." var)
        (cl:assert (can-be-variable-name-p var) ()
	           "In quantification, ~S is not a variable name." var))
    (cond
     ((neq none sort)
      (cond
       (global
        (cond
         (sort-unknown
          ;; global variable must be unsorted if nonsort restriction is specified
          (declare-variable-symbol var :sort top-sort))
         (t
          ;; sort must agree with previous sort declaration for this variable
          (declare-variable-symbol var :sort sort))))
       (t
        (cond
         (sort-unknown
          (declare-variable-symbol var))
         (t
          ;; sort must have been declared
          (input-sort2 sort)
          (declare-variable-symbol var)))))
      (append var-spec
              '(:skolem-p t)))
     (t
      (append var-spec 
              `(:sort ,(sort-name (variable-sort (declare-variable-symbol var))))
              '(:skolem-p t))))))

(defun make-variable-from-var-spec (var-spec)
  (if (getf (rest var-spec) :sort-unknown)
      (make-variable)
      (make-variable (input-sort2 (getf (rest var-spec) :sort)))))

(defun input-quantifier-variables (var-specs)
  ;; CycL requires single variable-name,
  ;; KIF 3.0 allows it,
  ;; KIF proposed ANSI standard disallows it
  (unless (listp var-specs)
    (setq var-specs (list var-specs)))
  (cl:assert (and (listp var-specs) (not (keywordp (second var-specs)))) ()
             "Quantifier requires a list of bound variables.")
  (setq var-specs (mapcar #'input-quantifier-variable var-specs))
  (dotails (l var-specs)
    (let ((v (first (first l))))
      (when (member v (rest l) :key #'first)
	(error "In quantification, variable ~A is being rebound." v))
      (when (assoc v *input-wff-substitution*)
	(warn "In quantification, variable ~A is being rebound." v))))
  var-specs)

(defun input-variables-in-form (expr vars substitution &optional result)
  ;; excluding vars
  (cond
    ((atom expr)
     (let ((v nil))
       (cond
	 ((member expr vars)
	  (setq v nil))
	 ((wild-card-p expr)
	  (setq v nil))
	 ((setq v (assoc expr substitution))
	  (setq v (cdr v))
	  (unless (variable-p v)
	    (setq v nil)))
	 ((can-be-free-variable-name-p expr)
	  (setq v (declare-variable-symbol expr))))
       (if (and v (not (assoc expr result)))
	   (nconc result (list (cons expr v)))
	   result)))
    ((eq 'quote (first expr))
     result)
    ((member (first expr) '(forall exists all every some))
     (dolist (var-spec (input-quantifier-variables (second expr)))
       (pushnew (first var-spec) vars))
     (input-variables-in-form
      (third expr)
      vars
      substitution
      result))
    (t
     (dolist (arg (rest expr))
       (setq result (input-variables-in-form arg vars substitution result)))
     result)))

(defun create-skolem-term (var-spec form free-vars-in-form)
  (let ((sort (getf (rest var-spec) :sort))
        (sort-unknown (getf (rest var-spec) :sort-unknown))
	(newskfn (create-skolem-symbol var-spec form (mapcar #'car free-vars-in-form))))
    (setq var-spec (copy-list var-spec))
    (remf (rest var-spec) :sort)
    (remf (rest var-spec) :sort-unknown)
    (remf (rest var-spec) :conc-name)
    (remf (rest var-spec) :global)
    (cond
      ((null free-vars-in-form)
       (setq newskfn (apply #'declare-constant-symbol
			    newskfn
			    (rest var-spec)))
       (when (and (neq top-sort sort) (not sort-unknown))
	 (declare-constant-sort newskfn (input-sort2 sort)))
       newskfn)
      (t
       (setq newskfn (apply #'declare-function-symbol
			    newskfn
			    (length free-vars-in-form)
			    (rest var-spec)))
       (when (and (neq top-sort sort) (not sort-unknown))
	 (declare-function-sort newskfn (CONS SORT (CONSN TOP-SORT NIL (LENGTH FREE-VARS-IN-FORM)))))
       (make-compound* newskfn (mapcar #'cdr free-vars-in-form))))))

(defun create-skolem-symbol (var-spec form free-vars-in-form)
  ;; this code for generating skolem function names and world path function names
  ;; stores the generated name in an alist so that if the exact same wff is input
  ;; again, the same names will be generated
  ;; thus,
  ;; (assert '(all (x) (some (y) (p x y))))
  ;;  followed by
  ;; (assert '(all (x) (some (y) (p x y))))
  ;; will result in two occurrences of the same wff with the same skolem function
  ;;
  ;; this could be improved by checking for variants rather than equality so that
  ;; (assert '(all (u) (some (v) (p u v))))
  ;; would also produce the same wff with the same skolem function
  (let ((key (list var-spec form free-vars-in-form)))
    (or (cdr (assoc (list var-spec form free-vars-in-form) *skolem-function-alist* :test #'equal))
	(let* (conc-name
	       sort
	       (x (make-symbol			;don't intern skolem symbols
		   (cond
		     ((setq conc-name (getf (rest var-spec) :conc-name))
		      (format nil "~A~D" conc-name (incf skfnnum)))
                     ((getf (rest var-spec) :sort-unknown)
                      (format nil "SK~D" (incf skfnnum)))
		     ((neq top-sort (setq sort (getf (rest var-spec) :sort)))
		      (format nil "~A-SK~D" sort (incf skfnnum)))
		     (t
		      (format nil "SK~D" (incf skfnnum)))))))
	  (push (cons key x) *skolem-function-alist*)
	  x))))

(defun newcrfn ()
  (make-symbol (format nil "CR~D" (incf crfnnum))))

(defun input-form* (head terms polarity)
  (make-compound* head (input-terms terms polarity)))

(defun input-form (head terms polarity)
  (let ((algrthm (function-input-function head)))
    (if algrthm
        (funcall algrthm head terms polarity)
        (input-form* head terms polarity))))

(defun input-atom (atom polarity)
  (cond
    (*input-sort-wff*
     (declare-sort* atom)
     atom)
    ((can-be-proposition-name-p atom)
     (cond
       ((cdr (assoc atom *input-wff-substitution*))
	(unimplemented))			;proposition variables
       (t
        (let ((symbol (input-proposition-symbol atom)))
          (when (print-symbol-in-use-warnings?)
            (setf (constant-in-use symbol) t))
          symbol))))
    ((and (consp atom) (can-be-function-name-p (first atom)))
     (check-for-well-sorted-atom
      (let ((head (input-relation-symbol (first atom) (or (list-p (rest atom)) 1))))
	(when (print-symbol-in-use-warnings?)
	  (setf (function-in-use head) t))
        (input-form head (rest atom) polarity))))
    ((and *input-proposition-variables* (can-be-free-variable-name-p atom))
     (declare-variable-symbol atom))
    (t
     (error "Cannot understand ~S as an atomic formula." atom))))

(defun input-trm (term)
  (let ((*input-wff-substitution* nil)
	(*input-wff-modal-prefix* nil))
    (input-term term :pos)))

(defun input-term (term polarity)
  (cond
   ((if *input-quote-term* nil (cdr (assoc term *input-wff-substitution*)))
    )
   ((wild-card-p term)
    (if *input-quote-term* term (make-variable)))
   ((can-be-free-variable-name-p term)
    (if *input-quote-term* term (declare-variable-symbol term)))
   ((atom term)
    (let ((symbol (input-constant-symbol term)))
      (when (print-symbol-in-use-warnings?)
        (setf (constant-in-use symbol) t))
      symbol))
   (*input-quote-term*
    (input-terms term polarity))	;treat (f a b) as (list f a b)
   ((can-be-free-variable-name-p (first term))
    (case (use-variable-heads?)
      ((nil)
       (cerror "Convert it to a LIST-TO-TERM form."
               "Term ~S has a variable head." term))
      (warn
       (warn "Term ~S has a variable head; converting it to a LIST-TO-TERM form." term)))
    ;; this will only work if use-code-for-lists option is true
    (input-term `(list-to-term (list ,@term)) polarity))
   ((can-be-function-name-p (first term))
    (let ((head (input-function-symbol (first term) (or (list-p (rest term)) 1))))
      (when (print-symbol-in-use-warnings?)
	(setf (function-in-use head) t))
      (input-form head (rest term) polarity)))
   (t
    (error "Cannot understand ~S as a term." term))))

(defun input-terms (terms polarity)
  (lcons (input-term (first terms) polarity)
	 (input-terms (rest terms) polarity)
	 terms))

(defun map-polarity (fun polarity)
  (if fun (funcall fun polarity) polarity))

(defun opposite-polarity (polarity)
  (ecase polarity
    (:pos
      :neg)
    (:neg
      :pos)
    (:both
      :both)))

(defun clausify (wff &optional map-fun)
  ;; apply map-fun to each clause in the clause form of wff
  ;; if map-fun is NIL, return CNF of wff
  (let ((clauses nil) clauses-last)
    (labels
      ((clausify* (cc wff pos lits)
         (cond
          ((and pos (test-option6?) (clause-p wff t))
           (funcall cc (cons wff lits)))
          (t
	   (ecase (head-is-logical-symbol wff)
	     ((nil)
              (cond
               ((eq true wff)
                (unless pos
                  (funcall cc lits)))
               ((eq false wff)
                (when pos
                  (funcall cc lits)))
               (t
                (let ((-wff (make-compound *not* wff)))
                  (dolist (lit lits (funcall cc (cons (if pos wff -wff) lits)))
                    (cond
                     ((equal-p lit wff)
                      (when pos
                        (funcall cc lits))
                      (return))
                     ((equal-p lit -wff)
                      (unless pos
                        (funcall cc lits))
                      (return))))))))
	     (not
              (clausify* cc (first (args wff)) (not pos) lits))
	     (and
              (let ((args (args wff)))
	        (if pos
		    (if (and lits (some (lambda (arg) (member-p arg lits)) args))
		        (funcall cc lits)
		        (dolist (arg args)
		          (clausify* cc arg t lits)))
                    (let ((y (make-a1-compound* *and* true (rest args))))
		      (clausify* (lambda (l) (clausify* cc y nil l)) (first args) nil lits)))))
	     (or
              (let ((args (args wff)))
	        (if pos
                    (let ((y (make-a1-compound* *or* false (rest args))))
		      (clausify* (lambda (l) (clausify* cc y t l)) (first args) t lits))
		    (if (and lits (some (lambda (arg) (member-p (negate arg) lits)) args))
		        (funcall cc lits)
		        (dolist (arg args)
		          (clausify* cc arg nil lits))))))
	     (implies
              (let* ((args (args wff)) (x (first args)) (y (second args)))
	        (if pos
		    (clausify* (lambda (l) (clausify* cc y t l)) x nil lits)
		    (progn
		      (clausify* cc x t   lits)
		      (clausify* cc y nil lits)))))
	     (implied-by
              (let* ((args (args wff)) (x (first args)) (y (second args)))
	        (if pos
		    (clausify* (lambda (l) (clausify* cc y nil l)) x t lits)
		    (progn
		      (clausify* cc y t   lits)
		      (clausify* cc x nil lits)))))
	     (iff
              (let* ((args (args wff)) (x (first args)) (y (make-a1-compound* *iff* true (rest args))))
	        (if pos
		    (progn
		      (clausify* (lambda (l) (clausify* cc y t   l)) x nil lits)
		      (clausify* (lambda (l) (clausify* cc y nil l)) x t   lits))
		    (progn
		      (clausify* (lambda (l) (clausify* cc y nil l)) x nil lits)
		      (clausify* (lambda (l) (clausify* cc y t   l)) x t   lits)))))
	     (xor
              (let* ((args (args wff)) (x (first args)) (y (make-a1-compound* *xor* false (rest args))))
	        (if pos
		    (progn
		      (clausify* (lambda (l) (clausify* cc y nil l)) x nil lits)
		      (clausify* (lambda (l) (clausify* cc y t   l)) x t   lits))
		    (progn
		      (clausify* (lambda (l) (clausify* cc y t   l)) x nil lits)
		      (clausify* (lambda (l) (clausify* cc y nil l)) x t   lits)))))
             (if 
               (let* ((args (args wff)) (x (first args)) (y (second args)) (z (third args)))
                 (clausify* (lambda (l) (clausify* cc y pos l)) x nil lits)
                 (clausify* (lambda (l) (clausify* cc z pos l)) x t   lits))))))))
      (clausify* (lambda (lits)
                   (let ((clause (make-a1-compound* *or* false (reverse lits))))
                     (if map-fun (funcall map-fun clause) (collect clause clauses))))
                 wff t nil)
      (if map-fun nil (make-a1-compound* *and* true clauses)))))

(defun report-not-2-arguments-quantification (head args)
  (case (use-extended-quantifiers?)
    ((nil)
     (cerror "Convert it to a 2-ary quantification."
             "~S does not have exactly 2 arguments as ~A ~S wants."
             (cons (function-name head) args)
             (function-kind-string head)
             (function-name head)))
    (warn
     (warn "~S does not have exactly 2 arguments as ~A ~S wants.  It will be converted."
           (cons (function-name head) args)
           (function-kind-string head)
           (function-name head)))))

(defun report-not-2-arguments-implication (head args)
  (case (use-extended-implications?)
    ((nil)
     (cerror "Convert it to a 2-ary implication."
             "~S does not have exactly 2 arguments as ~A ~S wants."
             (cons (function-name head) args)
             (function-kind-string head)
             (function-name head)))
    (warn
     (warn "~S does not have exactly 2 arguments as ~A ~S wants.  It will be converted."
           (cons (function-name head) args)
           (function-kind-string head)
           (function-name head)))))

(defun assert-n-or-more-arguments-p (head args n)
  (unless (<= n (length args))
    (cerror1 "~S does not have at least ~D argument~:P as ~A ~S requires."
             (cons (function-name head) args)
             n
             (function-kind-string head)
             (function-name head))))

(defun assert-n-or-fewer-arguments-p (head args n)
  (unless (>= n (length args))
    (cerror1 "~S does not have at most ~D argument~:P as ~A ~S requires."
             (cons (function-name head) args)
             n
             (function-kind-string head)
             (function-name head))))

(defun assert-n-arguments-p (head args n)
  (unless (eql n (length args))
    (cerror1 "~S does not have exactly ~D argument~:P as ~A ~S requires."
             (cons (function-name head) args)
             n
             (function-kind-string head)
             (function-name head))))

(defun require-n-arguments (head args polarity n)
  (assert-n-arguments-p head args n)
  (input-form* head args polarity))

;;; the following functions can be used as in
;;; (declare-relation-symbol 'product :any :input-function 'require-3-arguments)
;;; so that that there is only one product relation symbol
;;; (not more than one of different arities as is usually allowed)
;;; and it always has three arguments
;;; (not arbitrarily many as is usual for :any arity relations)

(defun require-0-arguments (head args polarity)
  (require-n-arguments head args polarity 0))

(defun require-1-arguments (head args polarity)
  (require-n-arguments head args polarity 1))

(defun require-2-arguments (head args polarity)
  (require-n-arguments head args polarity 2))

(defun require-3-arguments (head args polarity)
  (require-n-arguments head args polarity 3))

(defun require-4-arguments (head args polarity)
  (require-n-arguments head args polarity 4))

(defun require-5-arguments (head args polarity)
  (require-n-arguments head args polarity 5))

(defun require-6-arguments (head args polarity)
  (require-n-arguments head args polarity 6))

(defun require-7-arguments (head args polarity)
  (require-n-arguments head args polarity 7))

(defun require-8-arguments (head args polarity)
  (require-n-arguments head args polarity 8))

(defun require-9-arguments (head args polarity)
  (require-n-arguments head args polarity 9))

(defun require-n-arguments-function (n)
  (cond
   ((eq :any n)
    nil)
   (t
    (cl:assert (naturalp n))
    (intern (format nil "REQUIRE-~D-ARGUMENTS" n) :snark))))

(defun input-as-instance-of (head args polarity)
  ;; converts (p x) to (instance-of x p)
  (assert-n-arguments-p head args 1)
  (input-atom (list 'instance-of (first args) (function-name head)) polarity))

;;; input.lisp EOF
