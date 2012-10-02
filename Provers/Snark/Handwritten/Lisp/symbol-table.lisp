;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: symbol-table.lisp
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

(defvar *symbol-table*)
(defvar *symbols-in-symbol-table* nil)		;just constants and functions

(declaim (special *input-wff* *using-sorts*))

;;; identical names in different packages yield different symbols
;;; logical symbols, equality relation, etc., are in SNARK package

;;; a symbol-table where
;;;  each row index is a name
;;;  each column index is a type (arity)
;;;  the value at row*column is the internal symbol

(defun make-symbol-table ()
  (setq *symbol-table* (make-sparse-matrix :rows t :default-value none))
  (setq *symbols-in-symbol-table* nil))

(defun create-symbol-table-entry (name arity-code symbol)
  (cl:assert (symbolp name))
  (cl:assert (arity-code-p arity-code))
  (let ((name# (funcall *standard-eql-numbering* :lookup name))
        (arity-code# (funcall *standard-eql-numbering* :lookup arity-code)))
    (setf (sparef *symbol-table* name# arity-code#) symbol))
  (unless (or (eq :variable arity-code) (eq :sort arity-code))
    (push symbol *symbols-in-symbol-table*)))

(defun find-symbol-table-entries (name)
  (let ((name# (funcall *standard-eql-numbering* :lookup name)))
    (sparse-matrix-row *symbol-table* name#)))

(defun find-symbol-table-entry (name arity-code)
  (prog->
    (find-symbol-table-entries name ->nonnil entries)
    (map-sparse-vector-with-indexes entries ->* symbol type#)
    (funcall *standard-eql-numbering* :inverse type# -> type)
    (when (arity-code-match arity-code type symbol)
      (return-from find-symbol-table-entry symbol)))
  none)

(defun find-or-create-symbol-table-entry (name arity-code &optional (sym none))
  (let ((symbol (find-symbol-table-entry name arity-code)))
    (cond
      ((neq none symbol)
       (when (neq none sym)
         (cl:assert (eql sym symbol)))
       symbol)
      (t
       (prog->
         (find-symbol-table-entries name ->nonnil entries)
         (map-sparse-vector-indexes-only entries ->* arity-code2#)
         (funcall *standard-eql-numbering* :inverse arity-code2# -> arity-code2)
         (cond
          ((and (integerp arity-code)
                (> 100 arity-code -100)
                (integerp arity-code2)
                (if (plusp arity-code) (plusp arity-code2) (minusp arity-code2)))
           (error "~S is being used as a ~A; it was already a ~A."
                  name (arity-print-name arity-code t) (arity-print-name arity-code2 t)))
          ((and (print-symbol-table-warnings?)
                (or (eq :all (print-symbol-table-warnings?))
                    (and (integerp arity-code) (integerp arity-code2))
                    (and (eq :constant arity-code) (eq :variable arity-code2))
                    (and (eq :variable arity-code) (eq :constant arity-code2))))
           (warn "~S is being used as a ~A~@[ in ~A~]; it is also a ~A."
                 name (arity-print-name arity-code t) *input-wff* (arity-print-name arity-code2 t)))))
       (cond
        ((neq none sym)
         (setq symbol sym))
        ((eq :variable arity-code)
         (setq symbol (make-variable none)))
        ((eq :sort arity-code)
         (setq symbol (intern-sort name)))
        ((eq :constant arity-code)
         (setq symbol name))
        ((eq :proposition arity-code)
         (cond
          ((or (eq true name) (eq false name))
           (setq symbol name))
          (t
           (setq symbol (make-symbol (symbol-name name)))))
         (setf (constant-boolean-valued-p symbol) name))
        (t
         (mvlet (((:values arity booleanp) (decode-arity arity-code)))
           (setq symbol (make-function-symbol name arity))
           (when booleanp
             (setf (function-boolean-valued-p symbol) t)))))
       (create-symbol-table-entry name arity-code symbol)
       (values symbol t)))))

(defun create-aliases-for-symbol (aliases symbol)
  (let* ((functionp (function-symbol-p symbol))
         (booleanp (if functionp
                       (function-boolean-valued-p symbol)
                       (constant-boolean-valued-p symbol)))
         (arity-code (cond
                      (functionp
                       (encode-arity (function-arity symbol) booleanp))
                      (booleanp
                       :proposition)
                      (t
                       :constant))))
    (dolist (alias (mklist aliases))
      (if functionp
          (if booleanp
              (assert-can-be-relation-name-p alias)
              (assert-can-be-function-name-p alias))
          (if booleanp
              (assert-can-be-proposition-name-p alias)
              (progn
                (assert-can-be-constant-name-p alias)
                (cl:assert (symbolp alias)))))
      (find-or-create-symbol-table-entry alias arity-code symbol)
      (if functionp
          (pushnew alias (function-aliases symbol))
          (pushnew alias (constant-aliases symbol))))))

(defun create-aliases-for-sort (aliases sort)
  (dolist (alias (mklist aliases))
    (assert-can-be-sort-name-p alias)
    (find-or-create-symbol-table-entry alias :sort sort)))

(defun input-symbol (name)
  ;; return SNARK symbol whose name is name
  ;; primary usage is for term ordering declarations
  (assert-can-be-constant-or-function-name-p name)
  (cond
   ((numberp name)
    (declare-number name))
   ((characterp name)
    (declare-character name))
   ((stringp name)
    (declare-string name))
   (t
    (let ((found nil))
      (prog->
        (find-symbol-table-entries name ->nonnil entries)
        (map-sparse-vector-with-indexes entries ->* symbol type#)
        (funcall *standard-eql-numbering* :inverse type# -> type)
        (cond
         ((or (eq :sort type) (eq :variable type))
          )
         (found
          (error "There is more than one entry for ~A in symbol table." name))
         (t
          (setq found (cons type symbol)))))
      (cond
       ((null found)
        (error "Couldn't find ~A in symbol table." name))
       (t
        (cdr found)))))))

(defun input-function (name &optional nargs)
  ;; finds function or relation symbol with specified name
  ;; and number of arguments
  (if nargs
      (let ((arity-code1 (encode-arity nargs nil))	;function
	    (arity-code2 (encode-arity nargs t)))	;relation
        (input-function0 name (lambda (type symbol)
                                (or (arity-code-match arity-code1 type symbol)
                                    (arity-code-match arity-code2 type symbol)))))
      (input-function0 name (lambda (type symbol)
                              (declare (ignore symbol))
                              (integerp type)))))

(defun input-function0 (name arity-test &optional (not-found-action 'error))
  (let ((found nil))
    (prog->
      (find-symbol-table-entries name ->nonnil entries)
      (map-sparse-vector-with-indexes entries ->* symbol type#)
      (funcall *standard-eql-numbering* :inverse type# -> type)
      (cond
       ((not (funcall arity-test type symbol))
        )
       ((not found)
        (setq found (cons type symbol)))
       (t
        (return-from input-function0
          (and not-found-action
               (funcall not-found-action "Couldn't find just one ~S in symbol table." name))))))
    (if found
        (cdr found)
        (and not-found-action
             (funcall not-found-action "Couldn't find ~S in symbol table." name)))))

(defun input-constant-symbol (name)
  (assert-can-be-constant-name-p name)
  (cond
   ((numberp name)
    (declare-number name))
   ((characterp name)
    (declare-character name))
   ((stringp name)
    (declare-string name))
   (t
    (find-or-create-symbol-table-entry name :constant))))

(defun input-proposition-symbol (name)
  (assert-can-be-proposition-name-p name)
  (find-or-create-symbol-table-entry name :proposition))

(defun input-function-symbol (name &optional arity)
  ;; find or create a function symbol with the right name and arity
  ;; if arity is not provided, try to find a function symbol with the right name
  ;; if there isn't exactly one symbol with the right name, return nil
  (assert-can-be-function-name-p name)
  (let ((arity-code (function-arity-p arity nil)))
    (if arity-code
        (find-or-create-symbol-table-entry name arity-code)
        (input-function0 name
                         (lambda (type symbol)
                           (declare (ignore symbol))
                           (positive-integer-p type))
                         nil))))

(defun input-predicate-symbol (name &optional arity no-logical-symbols)
  (input-relation-symbol name arity no-logical-symbols))

(defun input-relation-symbol (name &optional arity no-logical-symbols)
  ;; find or create a relation symbol with the right name and arity
  ;; if arity is not provided, try to find a relation symbol with the right name
  ;; if there isn't exactly one symbol with the right name, return nil
  (assert-can-be-relation-name-p name)
  (input-relation-symbol* name arity no-logical-symbols))

(defun input-relation-symbol* (name &optional arity no-logical-symbols)
  (mvlet (((:values symbol new)
           (let ((arity-code (function-arity-p arity t)))
             (if arity-code
                 (find-or-create-symbol-table-entry name arity-code)
                 (input-function0 name
                                  (lambda (type symbol)
                                    (declare (ignore symbol))
                                    (negative-integer-p type))
                                  nil)))))
    (when (and symbol no-logical-symbols (function-logical-symbol-p symbol))
      (error "~S cannot be the name of a relation." name))
    (if new (values symbol new) symbol)))

(defun input-variable (name)
  (assert-can-be-variable-name-p name)
  (find-or-create-symbol-table-entry name :variable))

(defun input-sort (name &optional (not-found-action 'error))
  (setq name (kif-fix-sort-spec name))
  (cond
    ((eq top-sort name)
     name)
    (t
     (mvlet (((:values sort new) (find-or-create-symbol-table-entry name :sort)))
       (and new
            not-found-action
            (funcall not-found-action "~S was not declared as a sort." name))
       sort))))

(defun input-sort2 (name-or-conjunction)
  (cond
    ((and (consp name-or-conjunction) (eq 'and (first name-or-conjunction)))
     (let ((sort top-sort))
       (dolist (name (rest name-or-conjunction))
         (when (eq bottom-sort (setf sort (sort-intersection sort (input-sort name))))
           (error "Sort ~S is empty." name-or-conjunction)))
       sort))
   (t
    (input-sort name-or-conjunction))))

(defun sort-name-or-conjunction-p (x)
  ;; allows conjunction of sort names too
  (if (and (consp x) (eq 'and (first x)))
      (every #'sort-name-p (rest x))
      (sort-name-p x)))

(defun sort-name-p (x)
  (or (eq top-sort x)
      (and *using-sorts* (neq none (find-symbol-table-entry (kif-fix-sort-spec x) :sort)))))

(defun assert-sort-name-p (x)
  (unless (sort-name-p x)
    (cerror "Declare ~S as a sort." "~S was not declared as a sort." x)
    (declare-sort* x)))

(defun function-arity-p (x boolean-valued-p)
  (let ((n (encode-arity x boolean-valued-p)))
    (and (integerp n) n)))

(defun encode-arity (arity boolean-valued-p)
  (cond
   ((numberp arity)
    (cl:assert (naturalp arity))
    (if boolean-valued-p (- -100 arity) (+ 100 arity)))
   (t
    (case arity
      (:any
       (if boolean-valued-p -99 99))
      (:alist
       (if boolean-valued-p -98 98))
      (:plist
       (if boolean-valued-p -97 97))
      (:list*
       (if boolean-valued-p -96 96))
      (otherwise
       arity)))))

(defun decode-arity (arity-code)
  (if (integerp arity-code)
      (let ((n (abs arity-code)))
        (values
         (case n
           (99 :any)
           (98 :alist)
           (97 :plist)
	   (96 :list*)
           (otherwise (- n 100)))
         (minusp arity-code)))
      arity-code))

(defun arity-code-p (x)
  (if (integerp x)
      (or (<= 96 x) (>= -96 x))
      (member x '(:constant :proposition :variable :sort))))

(defun arity-code-match (arity-code type symbol)
  (or (eql arity-code type)
      (and (integerp arity-code)
	   (integerp type)
	   (or (and (<= 100 arity-code)
		    (or (> 100 type 0)
			(and (eql 102 type) 	;binary associative function
			     (function-associative symbol))))
	       (and (>= -100 arity-code)
		    (or (< -100 type 0)
			(and (eql -102 type) 	;binary associative relation
			     (function-associative symbol))))))))

(defun arity-print-name (n &optional fun)
  (mvlet (((:values arity booleanp) (if (arity-code-p n) (decode-arity n) n)))
    (case arity
      (:constant
       "constant")
      (:proposition
       "proposition")
      (:variable
       "variable")
      (:sort
       "sort")
      (:alist
       (if fun (if booleanp "alist relation" "alist function") "alist"))
      (:plist
       (if fun (if booleanp "plist relation" "plist function") "plist"))
      (:list*
       (if fun (if booleanp "list* relation" "list* function") "list*"))
      (:any
       (if fun (if booleanp "any-ary relation or connective" "any-ary function") ""))
      (otherwise
       (cl:assert (integerp arity))
       (format
        nil
        (if fun (if booleanp "~D-ary relation or connective" "~D-ary function") "~D-ary")
        arity)))))

(defun constant-name-lessp (x y)
  (cond
    ((numberp x)
     (if (numberp y)
	 (< x y)
	 t))
    ((numberp y)
     nil)
    (t
     (string< x y))))

(defun function-name-lessp (x y)
  (string< (symbol-name x) (symbol-name y)))

(defun map-symbol-table (cc &key numbers characters strings)
  (prog->
    (map-sparse-vector-with-indexes (sparse-matrix-rows *symbol-table*) ->* row name#)
    (funcall *standard-eql-numbering* :inverse name# -> name)
    (map-sparse-vector-with-indexes row ->* symbol arity-code#)
    (funcall *standard-eql-numbering* :inverse arity-code# -> arity-code)
    (funcall cc name arity-code symbol))
  ;; numbers, characters, and strings aren't in *symbol-table*
  (when (or numbers characters strings)
    (prog->
      (map-constants ->* symbol)
      (when (cond
             ((numberp symbol)
              numbers)
             ((characterp symbol)
              characters)
             ((stringp symbol)
              strings)
             (t
              nil))
        (funcall cc symbol :constant symbol)))))

(defun print-symbol-table (&key (logical-symbols nil)
                                (variables nil)
                                (numbers nil)
                                (characters nil)
                                (strings nil))
  (let ((list-of-variables nil)
	(list-of-sorts nil)
	(list-of-constants nil)
	(list-of-propositions nil)
	(list-of-functions nil)
	(list-of-relations nil)
	(list-of-logical-symbols nil)
	(ambiguous nil))
    (prog->
      (identity none -> previous-name)
      (map-symbol-table :numbers numbers :characters characters :strings strings ->* name type symbol)
      (cond
       ((neql previous-name name)
        (setf previous-name name))
       ((or (null ambiguous) (neql name (first ambiguous)))
        (push name ambiguous)))
      (cond
       ((eq :variable type)
        (when variables
          (push name list-of-variables)))
       ((eq :sort type)
        (when (eq name (sort-name symbol))
          (push name list-of-sorts)))
       ((eq :constant type)
        (when (eql name symbol)
          (push name list-of-constants)))
       ((eq :proposition type)
        (unless (or (eq true symbol) (eq false symbol))
          (when (eq name (constant-boolean-valued-p symbol))
            (push name list-of-propositions))))
       ((function-logical-symbol-p symbol)
        (when logical-symbols
          (when (eq name (function-name symbol))
            (push symbol list-of-logical-symbols))))
       ((function-boolean-valued-p symbol)
        (when (eq name (function-name symbol))
          (push symbol list-of-relations)))
       (t
        (when (eq name (function-name symbol))
          (push symbol list-of-functions)))))
    (when logical-symbols
      (terpri-comment)
      (format t "   ~D logical symbol~:P" (length list-of-logical-symbols))
      (when list-of-logical-symbols
        (princ ":")
        (dolist (symbol (sort list-of-logical-symbols #'function-name-lessp :key #'function-name))
          (terpri-comment)
          (format t "      ")
          (prin1 symbol)
          (format t "   ~A" (arity-print-name (function-arity symbol))))))
    (when variables
      (terpri-comment)
      (format t "   ~D variable~:P" (length list-of-variables))
      (when list-of-variables
        (princ ":")
        (dolist (symbol (sort list-of-variables #'string<))
          (terpri-comment)
          (format t "      ")
          (prin1 symbol))))
    (terpri-comment)
    (format t "   ~D sort~:P" (length list-of-sorts))
    (when list-of-sorts
      (princ ":")
      (dolist (symbol (sort list-of-sorts #'string<))
        (terpri-comment)
        (format t "      ")
        (prin1 symbol)))
    (terpri-comment)
    (format t "   ~D proposition~:P" (length list-of-propositions))
    (when list-of-propositions
      (princ ":")
      (dolist (symbol (sort list-of-propositions #'constant-name-lessp))
        (terpri-comment)
        (format t "      ")
        (prin1 symbol)))
    (terpri-comment)
    (format t "   ~D constant~:P" (length list-of-constants))
    (when list-of-constants
      (princ ":")
      (dolist (symbol (sort list-of-constants #'constant-name-lessp))
        (terpri-comment)
        (format t "      ")
        (prin1 symbol)))
    (terpri-comment)
    (format t "   ~D function~:P" (length list-of-functions))
    (when list-of-functions
      (princ ":")
      (dolist (symbol (sort list-of-functions #'function-name-lessp :key #'function-name))
        (terpri-comment)
        (format t "      ")
        (prin1 symbol)
        (format t "   ~A" (arity-print-name (function-arity symbol)))
        (when (rest (function-sort-declarations symbol))
          (format t " with multiple sorts"))))
    (terpri-comment)
    (format t "   ~D relation~:P" (length list-of-relations))
    (when list-of-relations
      (princ ":")
      (dolist (symbol (sort list-of-relations #'function-name-lessp :key #'function-name))
        (terpri-comment)
        (format t "      ")
        (prin1 symbol)
        (format t "   ~A" (arity-print-name (function-arity symbol)))
        (when (rest (function-sort-declarations symbol))
          (format t " with multiple sorts"))))
    (when ambiguous
      (terpri-comment)
      (format t "   ~D symbol~:P with multiple meanings" (length ambiguous))
      (princ ":")
      (dolist (symbol (sort ambiguous #'string<))
        (terpri-comment)
        (format t "      ")
        (prin1 symbol))))
  nil)

(declaim (special *skolem-function-alist*))

(defvar *all-both-polarity*)

(eval-when (:load-toplevel :execute)
  (setq *all-both-polarity* (cons (constantly :both) nil))
  (rplacd *all-both-polarity* *all-both-polarity*)
  nil)

(defun initialize-symbol-table ()
  (let-options ((allow-keyword-constant-symbols t)
		(allow-keyword-function-symbols t)
		(allow-keyword-proposition-symbols t)
		(allow-keyword-relation-symbols t))
    (setq *skolem-function-alist* nil)
    (make-symbol-table)
    (declare-proposition false)
    (declare-proposition true)
    (declare-constant nil :constructor t)
    (setq *cons* (declare-function 'cons 2 :constructor t))
    (declare-function 'list :any :input-function #'input-listof)
    (declare-function 'list* :any :input-function #'input-listof*)
    (declare-function 'alist :alist)
    (declare-function 'plist :plist)
    (declare-function 'quote :any :input-function #'input-quotation)
    (declare-function 'term-to-list 1 :rewrite-code 'term-to-list-rewriter :unify-code 'dont-unify)
    (declare-function 'list-to-term 1 :rewrite-code 'list-to-term-rewriter :unify-code 'dont-unify)
    (declare-relation 'list-to-atom 1 :rewrite-code 'list-to-atom-rewriter :unify-code 'dont-unify)
    (setq *not*
	  (declare-logical-symbol
	   'not
           :make-compound-function  #'negate
           :make-compound*-function #'negate*
	   :input-function #'input-negation
	   :polarity-map (list #'opposite-polarity)))
    (setq *and*
	  (declare-logical-symbol
	   'and
           :make-compound-function  #'conjoin
           :make-compound*-function #'conjoin*
	   :input-function #'input-conjunction
	   :associative (use-ac-connectives?)
	   :commutative (use-ac-connectives?)
	   :rewrite-code (if (use-ac-connectives?) '(and-wff-rewriter) nil)))
    (setq *or*
	  (declare-logical-symbol
	   'or
           :make-compound-function  #'disjoin
           :make-compound*-function #'disjoin*
	   :input-function #'input-disjunction
	   :associative (use-ac-connectives?)
	   :commutative (use-ac-connectives?)
	   :rewrite-code (if (use-ac-connectives?) '(or-wff-rewriter) nil)))
    (setq *implies*
	  (declare-logical-symbol
	   'implies
           :make-compound-function  #'make-implication
           :make-compound*-function #'make-implication*
	   :input-function #'input-implication
	   :polarity-map (list #'opposite-polarity)
	   :rewrite-code '(implies-wff-rewriter)))
    (setq *implied-by*
	  (declare-logical-symbol
	   'implied-by
           :make-compound-function  #'make-reverse-implication
           :make-compound*-function #'make-reverse-implication*
	   :input-function #'input-reverse-implication
	   :polarity-map (list #'identity #'opposite-polarity)
	   :rewrite-code '(implied-by-wff-rewriter)))
    (setq *iff*
	  (declare-logical-symbol
	   'iff
           :make-compound-function  #'make-equivalence
           :make-compound*-function #'make-equivalence*
	   :input-function #'input-equivalence
	   :polarity-map *all-both-polarity*
	   :associative (use-ac-connectives?)
	   :commutative (use-ac-connectives?)
           :alias '<=>))
    (setq *xor*
	  (declare-logical-symbol
	   'xor
           :make-compound-function  #'make-exclusive-or
           :make-compound*-function #'make-exclusive-or*
	   :input-function #'input-exclusive-or
	   :polarity-map *all-both-polarity*
	   :associative (use-ac-connectives?)
	   :commutative (use-ac-connectives?)))
    (setq *if*
	  (declare-logical-symbol
	   'if
           :make-compound-function  #'make-conditional
           :make-compound*-function #'make-conditional*
	   :input-function #'input-conditional
	   :polarity-map (list (constantly :both))))
    (setq *answer-if*
	  (declare-logical-symbol
	   'answer-if
	   :input-function #'input-conditional
	   :polarity-map (list (constantly :both))))
    (setq *forall* (declare-logical-symbol 'forall :input-function #'input-quantification))
    (setq *exists* (declare-logical-symbol 'exists :input-function #'input-quantification))
    (setq *=*
	  (declare-relation
	   '= :any
           :input-function #'input-equality
	   :rewrite-code (if (use-code-for-equality?) '(equality-rewriter) nil)
	   :satisfy-code (if (use-code-for-equality?) '(equality-satisfier) nil)
	   :commutative (if (test-option22?) nil t)
           :MAGIC NIL
           :alias '(equal |equal|)))
    #+ignore
    (declare-relation
     'nonvariable 1
     :rewrite-code 'nonvariable-rewriter
     :satisfy-code 'nonvariable-satisfier
     :unify-code 'dont-unify)
    #+ignore
    (declare-function 'the 2 :rewrite-code 'the-term-rewriter)
    (declare-logical-symbol '=>        :input-function #'input-kif-forward-implication)
    (declare-logical-symbol '<=        :input-function #'input-kif-backward-implication)
    (declare-logical-symbol 'nand      :input-function #'input-nand)
    (declare-logical-symbol 'nor       :input-function #'input-nor)
    (declare-relation '/= :any :input-function #'input-disequality)
    (setf (function-boolean-valued-p *=*) '=)
    (setf (function-logical-symbol-dual *and*) *or*)
    (setf (function-logical-symbol-dual *or*) *and*)
    (setf (function-logical-symbol-dual *forall*) *exists*)
    (setf (function-logical-symbol-dual *exists*) *forall*)
    nil))

(defun symbol-alias-or-name (symbol)
  (if (function-symbol-p symbol)
      (function-alias-or-name symbol)
      (constant-alias-or-name symbol)))

(defun symbol-boolean-valued-p (x)
  (and (if (function-symbol-p x)
           (function-boolean-valued-p x)
           (constant-boolean-valued-p x))
       t))

(defmethod use-lisp-types-as-sorts :before (&optional (value t))
  (cond
   (value
    (declare-disjoint-sorts 'character 'string 'list 'number)
    (declare-disjoint-subsorts 'list 'cons 'null)
    (declare-disjoint-subsorts 'number 'real 'complex)
    (declare-disjoint-subsorts 'real 'negative 'nonnegative)
    (declare-disjoint-subsorts 'nonnegative 'zero 'positive)
    (declare-disjoint-subsorts 'real 'rational 'float)
    (declare-disjoint-subsorts 'rational 'integer 'ratio)
    (declare-disjoint-subsorts 'integer 'even 'odd)
    (declare-sort-intersection 'positive-integer    'positive    'integer)
    (declare-sort-intersection 'negative-integer    'negative    'integer)
    (declare-sort-intersection 'nonnegative-integer 'nonnegative 'integer)
    (declare-sort              'nonnegative-integer :alias 'natural)
    (declare-function 'the-nonnegative-integer 1 :alias 'the-natural)
    (declare-constant-sort nil 'null)
    (declare-function-sort *cons* 'cons)
    )))

(defun declare-character (x)
  (when (and (eq top-sort (constant-sort x)) (sort-name-p 'character))
    (declare-constant-sort x (input-sort 'character)))
  x)

(defun declare-string (x)
  (let ((x* (let ((numbering *standard-equal-numbering*))
              (funcall numbering :inverse (funcall numbering :lookup x)))))
    (when (sort-name-p 'string)
      (declare-constant-sort x* (input-sort 'string)))
    x*))

(defun declare-number (x)
  (when (and (eq top-sort (constant-sort x)) *using-sorts*)
    (let ((integer nil) (ratio nil) (rational nil) (float nil) (real nil) (complex nil))
      (cond
       ((integerp x)
        (setq integer t rational t real t))
       ((rationalp x)
        (setq ratio t rational t real t))
       ((floatp x)
        (setq float t real t))
       (t
        (cl:assert (complexp x))
        (setq complex t)))
      (when real
        (cond
         ((minusp x)
          (when (sort-name-p 'negative)
            (declare-constant-sort x (input-sort 'negative))))
         ((plusp x)
          (when (sort-name-p 'nonnegative)
            (declare-constant-sort x (input-sort 'nonnegative)))
          (when (sort-name-p 'positive)
            (declare-constant-sort x (input-sort 'positive))))
         (t
          (when (sort-name-p 'nonnegative)
            (declare-constant-sort x (input-sort 'nonnegative)))
          (when (sort-name-p 'zero)
            (declare-constant-sort x (input-sort 'zero))))))
      (when integer
        (if (evenp x)
            (when (sort-name-p 'even)
              (declare-constant-sort x (input-sort 'even)))
            (when (sort-name-p 'odd)
              (declare-constant-sort x (input-sort 'odd))))
        (when (sort-name-p 'integer)
          (declare-constant-sort x (input-sort 'integer)))
        (when (and (<= 0 x) (sort-name-p 'natural))
          (declare-constant-sort x (input-sort 'natural))))
      (when (and ratio (sort-name-p 'ratio))
        (declare-constant-sort x (input-sort 'ratio)))
      (when (and rational (sort-name-p 'rational))
        (declare-constant-sort x (input-sort 'rational)))
      (when (and float (sort-name-p 'float))
        (declare-constant-sort x (input-sort 'float)))
      (when (and real (sort-name-p 'real))
        (declare-constant-sort x (input-sort 'real)))
      (when (and complex (sort-name-p 'complex))
        (declare-constant-sort x (input-sort 'complex)))
      (when (sort-name-p 'number)
        (declare-constant-sort x (input-sort 'number)))))
  x)

(defun symbol-number (x)
  (cond
   ((function-symbol-p x)
    (function-number x))
   (t
    (constant-number x))))

(defun symbol-numbering (action object)
  (ecase action
    ((:lookup :lookup?)
     (symbol-number object))))

(defun constant-numbered (n)
  ;; returns the constant such that (eql n (constant-number constant)) if there is one,
  ;; returns none otherwise
  ;; slow linear search
  (prog->
    (map-constants ->* const)
    (when (eql n (constant-number const))
      (return-from constant-numbered const)))
  none)

(defun function-numbered (n)
  ;; returns the function such that (eql n (function-number function)) if there is one,
  ;; returns none otherwise
  ;; slow linear search
  (prog->
    (map-sparse-vector (sparse-matrix-rows *symbol-table*) ->* row)
    (map-sparse-vector row ->* symbol)
    (when (and (function-symbol-p symbol) (eql n (function-number symbol)))
      (return-from function-numbered symbol)))
  none)

(defun symbol-numbered (n)
  (let (v)
    (cond
     ((neq none (setf v (function-numbered n)))
      v)
     ((neq none (setf v (constant-numbered n)))
      v)
     (t
      none))))

;;; symbol-table.lisp EOF
