;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: functions.lisp
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

(declaim (special *subsuming*))

(defvar *name*)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter function-slots
    (append constant-and-function-slots
            '((name nil :read-only t)
              (arity nil :read-only t)
              (sort-declarations nil)
              (logical-symbol-p nil)
              (logical-symbol-dual nil)
              (polarity-map nil) 	;list of unary functions to compute polarity of arguments
              (ordering-status nil)	;:left-to-right, :right-to-left, or :multiset comparison of argument lists
              (make-compound-function nil)
              (make-compound*-function nil)
              (input-function nil)
              (to-lisp-code nil)
              (weight-code nil)
              (satisfy-code nil)	;LISP functions for making atoms headed by this relation true
              (falsify-code nil)	;LISP functions for making atoms headed by this relation false
              (paramodulate-code nil)	;LISP functions for paramodulating terms headed by this function
              (rewrite-code nil)	;LISP functions for rewriting terms headed by this function
              (equal-code nil)
              (variant-code nil)
              (unify-code nil)
              (associative nil)
              (commutative nil)
              ;;(idempotent nil)	;unifiable terms may have different functions
              ;;(inverse nil)		;unifiable terms may have different functions
              (identity none)		;unifiable terms may have different functions (none means no identity)
              (permutations nil)
              (permutations-min nil)
              (index-type nil)
              (rewritable-p nil) 	;if nil, no rewrite rule exists with this symbol as lhs head
              (rewrites nil)
              (code-name0 nil)
              (canonical-variants (make-sparse-vector))		;for instance-graphs
              (instance-graph						;for instance-graphs
               (make-instance-graph
                :name (concatenate 'string "for " (string *name*))))
              (term-memory-entries (make-sparse-vector))		;for instance-graphs
              ))))

(defstruct (function-symbol
	     (:constructor make-function-symbol0 (name arity))
	     (:copier nil)
	     (:print-function print-function-symbol)
	     (:conc-name :function-))
  . #.function-slots)

(defun make-function-symbol (name arity)
  (let* ((*name* name)
         (fn (make-function-symbol0 name arity)))
    fn))

(defun function-kind-string (function)
  (cond
   ((function-logical-symbol-p function)
    "logical symbol")
   ((function-boolean-valued-p function)
    "relation")
   (t
    "function")))

(defun function-alias-or-name (fn)
  (let ((aliases (function-aliases fn)))
    (if aliases (first aliases) (function-name fn))))

(defun function-aliases (fn)
  (getf (function-plist fn) :aliases))

(defun function-documentation (fn)
  (getf (function-plist fn) :documentation))

(defun function-author (fn)
  (getf (function-plist fn) :author))

(defun function-source (fn)
  (getf (function-plist fn) :source))

(defun (setf function-aliases) (value fn)
  (setf (getf (function-plist fn) :aliases) value))

(defun (setf function-documentation) (value fn)
  (setf (getf (function-plist fn) :documentation) value))

(defun (setf function-author) (value fn)
  (setf (getf (function-plist fn) :author) value))

(defun (setf function-source) (value fn)
  (setf (getf (function-plist fn) :source) value))

(defun function-sort-declaration (function)
  (let ((fsds (function-sort-declarations function)))
    (unless (null (rest fsds))
      (cerror "Use the first one."
              "~S has more than one sort declaration."
              (function-name function)))
    (first fsds)))

(defun function-identity2 (fn)
  (if *subsuming* none (function-identity fn)))

#+ignore
(defun right-identity-e-term-rewriter (term subst)
  ;; function-rewrite-code example
  ;; (fn x e) -> x
  (mvlet (((:list x y) (args term)))
    (if (equal-p y 'e subst) x none)))	;return value or none

#+ignore
(defun right-identity-e-term-paramodulater (cc term subst)
  ;; function-paramodulate-code example
  ;; (fn x y) -> x after unifying y with e
  (prog->
    (args term -> (:list x y))
    (unify y 'e subst ->* subst)
    (funcall cc x subst)))		;call cc with value and substitution

(defmacro set-function-slot (slot)
  (let ((slot-supplied (intern (concatenate 'string
                                            (symbol-name slot)
                                            "-SUPPLIED")
                               :snark))
        (function-slot (intern (concatenate 'string
                                            "FUNCTION-"
                                            (symbol-name slot))
                               :snark)))
    `(when ,slot-supplied
       (setf (,function-slot symbol) ,slot))))

(defmacro set-function-code (code)
  (let ((code-supplied (intern (concatenate 'string
                                            (symbol-name code)
                                            "-SUPPLIED")
                               :snark))
        (function-code (intern (concatenate 'string
                                            "FUNCTION-"
                                            (symbol-name code))
                               :snark)))
    `(when ,code-supplied
       (setf (,function-code symbol)
             (if (listp ,code)
                 (remove-duplicates ,code :from-end t)				;replace
                 (cons ,code (remove ,code (,function-code symbol))))))))	;add

(defun declare-function-symbol0 (symbol
                                 &key
                                 alias
                                 (sort nil)
                                 (documentation nil documentation-supplied)
                                 (author nil author-supplied)
                                 (source nil source-supplied)
                                 (weight nil weight-supplied)
                                 (allowed-in-answer nil allowed-in-answer-supplied)
                                 (ordering-status nil ordering-status-supplied)
                                 (to-lisp-code nil to-lisp-code-supplied)
                                 (weight-code nil weight-code-supplied)
                                 (rewrite-code nil rewrite-code-supplied)
                                 (paramodulate-code nil paramodulate-code-supplied)
                                 (equal-code nil equal-code-supplied)
                                 (variant-code nil variant-code-supplied)
                                 (unify-code nil unify-code-supplied)
                                 (associative nil associative-supplied)
                                 (commutative nil commutative-supplied)
                                 (constructor nil constructor-supplied)
                                 (skolem-p nil skolem-p-supplied)
                                 (created-p nil created-p-supplied)
                                 (kbo-weight nil kbo-weight-supplied)
                                 (polarity-map nil polarity-map-supplied)
                                 (input-function nil input-function-supplied)
                                 (make-compound-function nil make-compound-function-supplied)
                                 (make-compound*-function nil make-compound*-function-supplied)
                                 (identity nil identity-supplied)
                                 (permutations nil permutations-supplied)
                                 (constraint-theory nil constraint-theory-supplied)
                                 (index-type nil index-type-supplied)
                                 )
  ;; doesn't do anything if no keywords are supplied
  (when alias
    (create-aliases-for-symbol alias symbol))
  (when sort
    (declare-function-sort symbol sort))
  (set-function-slot documentation)
  (set-function-slot author)
  (set-function-slot source)
  (set-function-slot weight)
  (set-function-slot skolem-p)
  (set-function-slot created-p)
  (set-function-slot constructor)
  (set-function-slot allowed-in-answer)
  (set-function-slot kbo-weight)
  (set-function-slot constraint-theory)
  (set-function-slot polarity-map)
  (set-function-slot ordering-status)
  (set-function-slot make-compound-function)
  (set-function-slot make-compound*-function)
  (set-function-slot input-function)
  (set-function-code to-lisp-code)
  (set-function-code weight-code)
  (set-function-code rewrite-code)
  (set-function-code paramodulate-code)
  (set-function-code equal-code)
  (set-function-code variant-code)
  (set-function-code unify-code)
  (when associative-supplied
    (when associative				;can't undeclare it
      (declare-function-associative symbol)))
  (when commutative-supplied
    (when commutative				;can't undeclare it
      (declare-function-commutative symbol)))
  (set-function-slot identity)
  (when permutations-supplied
    (apply #'declare-function-permutative symbol permutations))
  (set-function-slot index-type)
  symbol)

(defun declare-relation-symbol0 (symbol
                                 &key
                                 alias
                                 documentation
                                 author
                                 source
                                 sort
                                 (weight nil weight-supplied)
                                 (allowed-in-answer nil allowed-in-answer-supplied)
                                 (ordering-status nil ordering-status-supplied)
                                 (to-lisp-code nil to-lisp-code-supplied)
                                 (weight-code nil weight-code-supplied)
                                 (rewrite-code nil rewrite-code-supplied)
                                 (satisfy-code nil satisfy-code-supplied)
                                 (falsify-code nil falsify-code-supplied)
                                 (equal-code nil equal-code-supplied)
                                 (variant-code nil variant-code-supplied)
                                 (unify-code nil unify-code-supplied)
                                 (associative nil associative-supplied)	;only for connectives
                                 (commutative nil commutative-supplied)
                                 
                                 (kbo-weight nil kbo-weight-supplied)
                                 (complement nil complement-supplied)
                                 (magic t magic-supplied)
                                 (polarity-map nil polarity-map-supplied)
                                 (input-function nil input-function-supplied)
                                 (make-compound-function nil make-compound-function-supplied)
                                 (make-compound*-function nil make-compound*-function-supplied)
                                 (permutations nil permutations-supplied)
                                 (constraint-theory nil constraint-theory-supplied)
                                 (index-type nil index-type-supplied)
                                 )
  ;; doesn't do anything if no keywords are supplied
  (when alias
    (create-aliases-for-symbol alias symbol))
  (when documentation
    (setf (function-documentation symbol) documentation))
  (when author
    (setf (function-author symbol) author))
  (when source
    (setf (function-source symbol) source))
  (when sort
    (declare-function-sort symbol sort))
  (set-function-slot weight)
  (set-function-slot allowed-in-answer)
  (set-function-slot kbo-weight)
  (set-function-slot constraint-theory)
  (set-function-slot complement)
  (set-function-slot magic)
  (set-function-slot polarity-map)
  (set-function-slot ordering-status)
  (set-function-slot make-compound-function)
  (set-function-slot make-compound*-function)
  (set-function-slot input-function)
  (set-function-code to-lisp-code)
  (set-function-code weight-code)
  (set-function-code rewrite-code)
  (set-function-code satisfy-code)
  (set-function-code falsify-code)
  (set-function-code equal-code)
  (set-function-code variant-code)
  (set-function-code unify-code)
  (when associative-supplied
    (when associative				;can't undeclare it
      (declare-function-associative symbol)))
  (when commutative-supplied
    (when commutative				;can't undeclare it
      (declare-function-commutative symbol)))
  (when permutations-supplied
    (apply #'declare-function-permutative symbol permutations))
  (set-function-slot index-type)
  symbol)

(defun declare-function-symbol1 (symbol keys-and-values)
  (cond
   ((null keys-and-values)
    symbol)
   ((function-boolean-valued-p symbol)
    (apply #'declare-relation-symbol0 symbol keys-and-values))
   (t
    (apply #'declare-function-symbol0 symbol keys-and-values))))

(defun declare-function-symbol2 (symbol keys-and-values)
  ;; for new function and relation symbols
  (case (function-arity symbol)
    (:plist
     (setf (function-input-function symbol) 'input-plist-args)	;input/output as plists
     (setf (function-equal-code symbol) '(equal-alist-args-p))	;but represented by alists
     (setf (function-variant-code symbol) '(variant-alist-args-p))
     (setf (function-unify-code symbol) '(unify-alist-args)))
    (:alist
     (setf (function-input-function symbol) 'input-alist-args)
     (setf (function-equal-code symbol) '(equal-alist-args-p))
     (setf (function-variant-code symbol) '(variant-alist-args-p))
     (setf (function-unify-code symbol) '(unify-alist-args)))
    (:list*
     (setf (function-input-function symbol) 'input-list*-args)))
  (declare-function-symbol1 symbol keys-and-values))

(defun declare-function-symbol* (symbol &rest keys-and-values)
  (declare (dynamic-extent keys-and-values))
  (cl:assert (and (function-symbol-p symbol)
                  (not (function-boolean-valued-p symbol))))
  (when keys-and-values
    (warn "Declaring function symbol ~S, which is already in use." (function-name symbol)))
  (declare-function-symbol1 symbol keys-and-values))

(defun declare-relation-symbol* (symbol &rest keys-and-values)
  (declare (dynamic-extent keys-and-values))
  (cl:assert (and (function-symbol-p symbol)
                  (function-boolean-valued-p symbol)
                  (not (function-logical-symbol-p symbol))))
  (when keys-and-values
    (warn "Declaring relation symbol ~S, which is already in use." (function-name symbol)))
  (declare-function-symbol1 symbol keys-and-values))

(defun allow-redeclaration-of-symbol-slots? ()
  '(alias documentation author source))

(defun print-symbol-in-use-warning? (symbol keys-and-values)
  (and (print-symbol-in-use-warnings?)
       (do ((l keys-and-values (cddr l)))
           ((null l)
            nil)
         (unless (member (first l) (allow-redeclaration-of-symbol-slots?))
           (return t)))
       (if (function-symbol-p symbol)
           (function-in-use symbol)
           (constant-in-use symbol))))

(defun remf2 (l property-name)
  (cond
   ((endp l)
    l)
   ((eql property-name (first l))
    (remf2 (rest (rest l)) property-name))
   (t
    (let* ((r (rest (rest l)))
           (r* (remf2 r property-name)))
      (if (eq r r*)
          l
          (list* (first l) (second l) r*))))))

(defun declare-function-symbol (&rest args)
  (declare (dynamic-extent args))
  (apply 'declare-function args))

(defun declare-function (name arity &rest keys-and-values)
  (declare (dynamic-extent keys-and-values))
  (mvlet (((:values symbol new) (input-function-symbol name arity)))
    (cond
     (new
      (declare-function-symbol2 symbol keys-and-values))
     (t
      (when (print-symbol-in-use-warning? symbol keys-and-values)
        (warn "Declaring function symbol ~S, which is already in use." name))
      (declare-function-symbol1 symbol keys-and-values)))))

(defun declare-predicate-symbol (&rest args)
  (declare (dynamic-extent args))
  (apply 'declare-relation args))

(defun declare-relation-symbol (&rest args)
  (declare (dynamic-extent args))
  (apply 'declare-relation args))

(defun declare-relation (name arity &rest keys-and-values)
  (declare (dynamic-extent keys-and-values))
  (mvlet (((:values symbol new) (input-relation-symbol name arity)))
    (cond
     (new
      (declare-function-symbol2 symbol keys-and-values))
     (t
      (cl:assert (not (function-logical-symbol-p symbol)))
      (when (print-symbol-in-use-warning? symbol keys-and-values)
        (warn "Declaring relation symbol ~S, which is already in use." name))
      (declare-function-symbol1 symbol keys-and-values)))))

(defun declare-logical-symbol (name &rest keys-and-values)
  (declare (dynamic-extent keys-and-values))
  (mvlet (((:values symbol new) (input-relation-symbol name :any)))
    (cond
     (new
      (setf (function-logical-symbol-p symbol) name)
      (declare-function-symbol1 symbol keys-and-values))
     (t
      (cl:assert (function-logical-symbol-p symbol))
      (when (print-symbol-in-use-warning? symbol keys-and-values)
        (warn "Declaring logical symbol ~S, which is already in use." name))
      (declare-function-symbol1 symbol keys-and-values)))))

(defun declare-function-associative (function &optional verbose)
  (when verbose
    (terpri-comment)
    (if (function-commutative function)
        (format t "Declaring ~A to be associative-commutative." (function-name function))
        (format t "Declaring ~A to be associative." (function-name function))))
  (setf (function-associative function) t)
  (setf (function-hash-code function) 0)
  (cond
    ((function-commutative function)
     (declare-function-symbol0
      function
      :ordering-status :ac
      :equal-code (cons 'equal-bag-p (remove 'equal-commute-p (function-equal-code function)))
      :variant-code (cons 'variant-bag (remove 'variant-commute (function-variant-code function)))
      :unify-code (cons 'unify-bag (remove 'unify-commute (function-unify-code function)))))
    (t
     (declare-function-symbol0
      function
      :ordering-status :ac
      :equal-code 'equal-vector-p
      :variant-code 'variant-vector
      :unify-code 'unify-vector)))
  (check-associative-function-sort function)
  nil)

(defun declare-function-commutative (function &optional verbose)
  (when verbose
    (terpri-comment)
    (if (function-associative function)
        (format t "Declaring ~A to be associative-commutative." (function-name function))
        (format t "Declaring ~A to be commutative." (function-name function))))
  (setf (function-commutative function) t)
  (cond
    ((function-associative function)
     (declare-function-symbol0
      function
      :ordering-status :ac
      :equal-code (cons 'equal-bag-p (remove 'equal-vector-p (function-equal-code function)))
      :variant-code (cons 'variant-bag (remove 'variant-vector (function-variant-code function)))
      :unify-code (cons 'unify-bag (remove 'unify-vector (function-unify-code function)))))
    (t
     (declare-function-symbol0
      function
      :ordering-status :multiset
      :equal-code 'equal-commute-p
      :variant-code 'variant-commute
      :unify-code 'unify-commute)))
  nil)

(defun declare-function-permutative (function permutation &rest more-permutations)
  (let ((arity (function-arity function)) (permutations (cons permutation more-permutations)))
    (common-lisp:assert (>= arity 2))
    (dolist (p permutations)
      (unless (permutation-p p arity)
	(error "~A is not a well formed permutation for arity ~D." p arity)))
    (cond
      ((= arity 2)
       (declare-function-commutative function))		
      (t
       (let ((permutations (permutations (integers-between 0 (1- arity)) permutations)))
	 (setf (function-permutations function) permutations)
	 (setf (function-permutations-min function) (permutations-min permutations))
	 (setf (function-ordering-status function) :multiset)
	 (setf (function-equal-code function) '(equal-permute-p))
	 (setf (function-variant-code function) '(variant-permute))
	 (setf (function-unify-code function) '(unify-permute)))))
    nil))

(defun permutations-min (permutations)
  (cons (reduce #'min permutations :key #'first)
	(if (null (rest (first permutations)))
	    nil
	    (permutations-min (mapcar #'rest permutations)))))

(defun function-code-name (symbol)
  (or (function-code-name0 symbol)
      (let ((fcn (intern (concatenate
		          'string
		          "CODE-FOR-"
		          (string (function-name symbol)))
		         :keyword)))
        (setf (function-code-name0 symbol) fcn))))

(defun function-resolve-code (fn v)
  (ecase v
    ((true :neg)
     (function-satisfy-code fn))
    ((false :pos)
     (function-falsify-code fn))))

(defun declare-function-rewrite-code (x)
  (mvlet (((:list* name arity rewrite-code more-options) x))
    (apply 'declare-function name arity
           :rewrite-code rewrite-code
           more-options)))

(defun declare-relation-rewrite-code (x)
  (mvlet (((:list* name arity rewrite-code more-options) x))
    (apply 'declare-relation name arity
           :rewrite-code rewrite-code
           :MAGIC NIL
           more-options)))

;;; functions.lisp EOF
