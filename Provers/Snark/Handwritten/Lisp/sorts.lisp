;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: sorts.lisp
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

(eval-when (:compile-toplevel :load-toplevel)
  (defparameter sort-slots
    '((documentation nil)
      (source nil)		;for KIF
      (author nil)		;for KIF
      )))

(defstruct sort-info
  . #.sort-slots)

(progn
  . #.(mapcan
       (lambda (x)
         (let* ((slot-name (if (consp x) (first x) x))
                (sort-slot (intern (format nil "SORT-~A" slot-name) :snark))
                (set-sort-slot (list 'setf sort-slot))
                (sort-info-slot (intern (format nil "SORT-INFO-~A" slot-name) :snark)))
           (list
            `(defun ,SORT-SLOT (sort)
               (,sort-info-slot (get-sort-info sort)))
            `(defun ,SET-SORT-SLOT (value sort)
               (setf (,sort-info-slot (get-sort-info sort)) value)))))
	sort-slots))

(defvar *sort-info-table*)

(defun get-sort-info (sort)
  (gethash sort *sort-info-table*))

(defvar *using-sorts*)				;t if sorts are in use
(defvar *sort-theory*)
(defvar *subsort-cache*)
(defvar *sort-intersection-cache*)
(defvar *check-sorts-nontrivial* nil)

(declaim
 (special
  *dp-sort-intersections*))

(defmethod use-sort-implementation :before (&optional (value t))
  (initialize-sort-theory value))

(defun initialize-sort-theory (&optional (type (use-sort-implementation?)))
  (cl:assert (not *using-sorts*))
  (ecase type
    (:dp
     (setq *sort-theory* (make-sort-theory-dp-clause-set))
     (setq *dp-sort-intersections* (make-hash-table :test #'equal)))
    (:km
     (initialize-km-sorts))
    (:bdd
     (setq *sort-theory* (make-sort-theory-bdd))))
  (clear-sort-caches)
  (setq *sort-info-table* (make-hash-table))
  (setq *using-sorts* nil))

(defun clear-sort-caches ()
  (setq *subsort-cache* (make-assoc-cache 7))
  (setq *sort-intersection-cache* (make-assoc-cache 7))
  nil)

(defun intern-sort (sort-name)
  (assert-can-be-sort-name-p sort-name)
  (setq *using-sorts* t)
  (ecase (use-sort-implementation?)
    (:dp
     sort-name)
    (:km
     (km-intern-sort sort-name))
    (:bdd
     (bdd-intern-sort sort-name))))

(defun sort-name (sort)
  (ecase (use-sort-implementation?)
    ((:dp :km)
     sort)
    (:bdd
     (bdd-sort-name sort))))

(defun declare-the-sort-function-symbol (name sort)
  (unless (null (symbol-package name))
    (declare-function
     (intern (concatenate 'string (symbol-name 'the-) (symbol-name name)) :snark-user) 1
     :sort name
     :rewrite-code (lambda (term subst)
                     (let ((x (arg1 term)))
                       (if (subsort-p (term-sort term subst) sort) x none))))))

(defun declare-sort* (name)
  (setf name (kif-fix-sort-spec name))
  (let ((sort (input-sort name nil)))
    (unless (get-sort-info sort)
      (let ((info (make-sort-info)))
        (setf (gethash sort *sort-info-table*) info)
        ;; attach sort-info to sort-name as well as sort
        (unless (eq sort name)
          (setf (gethash name *sort-info-table*) info)))
      (declare-the-sort-function-symbol name sort))
    sort))

(defun declare-subsort* (subsort sort)
  (cond
   ((eq subsort sort)
    )
   (t
    (clear-sort-caches)
    (cond
     ((and (eq (time-point-sort-name?) (sort-name subsort))
           (eq (time-interval-sort-name?) (sort-name sort)))
      (warn "Not declaring ~A to be subsort of ~A." (sort-name subsort) (sort-name sort))
      (return-from declare-subsort*))
     ((and (eq (time-interval-sort-name?) (sort-name subsort))
           (not (subsort-p (declare-sort* (time-point-sort-name?)) sort)))
      (warn "Declaring ~A to be subsort of ~A." (time-point-sort-name?) (sort-name sort))
      (declare-subsort* (declare-sort* (time-point-sort-name?)) sort)))
    (ecase (use-sort-implementation?)
      (:dp
       (dp-assert-subsort subsort sort))
      (:km
       (km-assert-subsort subsort sort))
      (:bdd
       (bdd-assert-subsort subsort sort))))))

(defun declare-sort-disjoint* (sorts)
  (cond
   ((null (rest sorts))
    )
   (t
    (clear-sort-caches)
    (ecase (use-sort-implementation?)
      (:dp
       (dp-assert-sort-disjoint sorts))
      (:km
       (km-assert-sort-disjoint sorts))
      (:bdd
       (bdd-assert-sort-disjoint sorts))))))

;;; user operations for defining a sort theory:
;;;  declare-sort
;;;  declare-subsort
;;;  declare-disjoint-sorts
;;;  declare-subsorts
;;;  declare-disjoint-subsorts
;;;  declare-sort-intersection
;;;  declare-sort-partition

(defun declare-sort (sort-name &key
                               alias documentation author source
                               ((:iff definition) nil definition-supplied))
  (with-clock-on sortal-reasoning
    (let ((sort (declare-sort* sort-name)))
      (when alias
        (create-aliases-for-sort alias sort))
      (when documentation
        (setf (sort-documentation sort) documentation))
      (when author
        (setf (sort-author sort) author))
      (when source
        (setf (sort-source sort) source))
      (when definition-supplied
        (assert-sort-definition `(iff ,sort-name ,definition)))
      sort)))

(defun declare-subsort (subsort-name sort-name)
  (with-clock-on sortal-reasoning
    (declare-subsort* (declare-sort* subsort-name) (declare-sort* sort-name)))
  nil)

(defun declare-disjoint-sorts (&rest sort-names)
  (with-clock-on sortal-reasoning
    (declare-sort-disjoint* (mapcar #'declare-sort* sort-names)))
  nil)

(defun declare-subsorts (sort-name &rest subsort-names)
  (with-clock-on sortal-reasoning
    (let ((sort (declare-sort* sort-name)))
      (dolist (subsort-name subsort-names)
        (declare-subsort* (declare-sort* subsort-name) sort))))
  nil)

(defun declare-disjoint-subsorts (sort-name &rest subsort-names)
  (with-clock-on sortal-reasoning
    (let ((sort (declare-sort* sort-name)) (subsorts nil))
      (dolist (subsort-name subsort-names)
        (let ((subsort (declare-sort* subsort-name)))
          (declare-subsort* subsort sort)
          (push subsort subsorts)))
      (declare-sort-disjoint* subsorts)))
  nil)

(defun declare-sort-intersection (sort-name supersort-name1 supersort-name2 &rest more-supersort-names)
  (assert-can-be-sort-name-p sort-name)
  (let ((s (sort-intersection (declare-sort* supersort-name1) (declare-sort* supersort-name2))))
    (dolist (supersort-name more-supersort-names)
      (setq s (sort-intersection s (declare-sort* supersort-name))))
    (cl:assert (neq bottom-sort s) ()
               "Cannot declare sort ~A to be intersection of ~A and ~A~{ and ~A~}, which is empty."
               sort-name supersort-name1 supersort-name2 more-supersort-names)
    (create-aliases-for-sort sort-name s)
    (declare-the-sort-function-symbol sort-name s)
    s))

(defun declare-sort-partition (sort-name subsort-name1 subsort-name2 &rest more-subsort-names)
  (apply #'declare-disjoint-sorts subsort-name1 subsort-name2 more-subsort-names)
  (declare-sort sort-name :iff `(or ,subsort-name1 ,subsort-name2 ,@more-subsort-names)))

(defun assert-sort-definition (wff)
  (with-clock-on sortal-reasoning
    (clear-sort-caches)
    (ecase (use-sort-implementation?)
      (:dp
       (dp-assert-sort-definition wff))
      (:km
       (km-assert-sort-definition wff))
      (:bdd
       (bdd-assert-sort-definition wff)))))

(defun same-sort-p (x y)
  (ecase (use-sort-implementation?)
   (:dp
    (or (eq x y) (and (equal x 'number) (eq y (dp-sort-intersection 'nonnegative 'integer t)))
	(and (equal x 'number) (eq y 'integer))))
   (:km
    (km-same-sort-p x y))
   (:bdd
    (bdd-same-sort-p x y))))

(defun subsort-p (x y)
  ;; returns true for both identical sorts and strict subsorts
  (cond
    ((eq top-sort y)
     t)
    ((eq top-sort x)
     nil)
    ((same-sort-p x y)
     t)
    (t
     (or (cdr (assoc-if (lambda (k)
                          (and (same-sort-p x (car k))
                               (same-sort-p y (cdr k))))
			*subsort-cache*))
	 (with-clock-on sortal-reasoning
	   (assoc-cache-push
	    (cons x y)
	    (funcall (ecase (use-sort-implementation?)
		       (:dp
			'dp-subsort-p)
		       (:km
                        'km-subsort-p)
                       (:bdd
			'bdd-subsort-p))
		     x y)
	    *subsort-cache*))))))

(defun supersort-p (x y)
  (subsort-p y x))

(defun sort-equivalent-p (x y)
  (and (subsort-p x y)
       (subsort-p y x)))

(defun sort-intersection (x y &optional (naming t))
  (cond
    ((subsort-p x y)
     x)
    ((subsort-p y x)
     y)
    (t
     (or (cdr (assoc-if (lambda (k)
                          (and (same-sort-p x (car k))
                               (same-sort-p y (cdr k))))
			*sort-intersection-cache*))
	 (with-clock-on sortal-reasoning
	   (assoc-cache-push
	    (cons x y)
	    (funcall (ecase (use-sort-implementation?)
		       (:dp
			'dp-sort-intersection)
		       (:km
                        'km-sort-intersection)
                       (:bdd
			'bdd-sort-intersection))
		     x y naming)
	    *sort-intersection-cache*))))))

(defun sort-disjoint-p (x y)
  (ecase (use-sort-implementation?)
    (:dp
     (cond
       ((or (eq top-sort x) (eq top-sort y) (eq x y))
	nil)
       (t
	(with-clock-on sortal-reasoning
	  (dp-sort-disjoint-p x y)))))
    ((:km :bdd)
     (eq bottom-sort (sort-intersection x y nil)))))

(defun check-sorts-nontrivial ()
  (with-clock-on sortal-reasoning
    (ecase (use-sort-implementation?)
     (:dp
      (dp-check-sorts-nontrivial))
     (:km
      (km-check-sorts-nontrivial))
     (:bdd
      (bdd-check-sorts-nontrivial)))))

(defvar *can-be-sort-name* nil)		;ad hoc way to suppress name test for new internal sort

(defun declare-constant-sort (constant sort)
  "assigns a sort to a constant"
  (let* ((old-sort (constant-sort constant))
         (new-sort (cond
                    ((subsort-p sort old-sort)
                     sort)
                    ((subsort-p old-sort sort)
                     old-sort)
		    (t
		     (ecase (use-sort-implementation?)
		       (:dp
			(dp-sort-intersection old-sort sort t))
		       (:km
                        (km-sort-intersection old-sort sort t))
                       (:bdd
			(let ((n1 (sort-name old-sort))
			      (n2 (sort-name sort))
                              (*can-be-sort-name* t))
			  (declare-sort (intern (format nil "~A&~A" n1 n2) :snark-user)
					:iff `(and ,n1 ,n2)))))))))
    (cond
     ((eq new-sort old-sort)
      nil)
     ((eq new-sort bottom-sort)
      (error "Cannot declare ~A as constant of sort ~A; ~A is of incompatible sort ~A."
	     constant sort constant old-sort))
     (t
      (setf (constant-sort constant) new-sort)
      t))))

(defun declare-function-sort (function sort-spec)
  (let ((fsd
         (cond
          ((function-boolean-valued-p function)
           (cl:assert (consp sort-spec))
           ;; relation argument sorts can be preceded by boolean result-sort
           ;; (this is stylistically undesirable and just for backward compatibility)
           (when (eq 'boolean (car sort-spec))
             (setf sort-spec (rest sort-spec)))
           (make-function-sort-declaration
            :argument-sort-alist (input-argument-sort-alist function sort-spec)))
          ((or (atom sort-spec) (eq 'and (first sort-spec)))
           (make-function-sort-declaration
            :result-sort (input-sort sort-spec)))
          (t
           (make-function-sort-declaration
            :result-sort (input-sort2 (car sort-spec))
            :argument-sort-alist (input-argument-sort-alist function (cdr sort-spec)))))))
    (case (function-arity function)
      ((:alist :plist)
       (declare-alist-function-sort function fsd))
      (:list*
       (declare-list*-function-sort function fsd))
      (otherwise
       (declare-ordinary-function-sort function fsd)))))

(defun declare-ordinary-function-sort (function fsd)
  "assigns result and argument sorts to a function"
;; (unless argument-sorts
;;   (error "No argument sorts provided.~%Can't declare sorts for 0-ary function; use a constant instead."))
  (let ((fsds (function-sort-declarations function)))
    (cond
     ((null fsds)
      (setf (function-sort-declarations function) (list fsd)))
     ((function-boolean-valued-p function)
      ;; keep all sort-declarations that are not instances of another
      (unless (member fsd fsds :test #'sub-fsd-p)
        (setf (function-sort-declarations function) (cons fsd (remove fsd fsds :test #'super-fsd-p)))))
     (t
      (unless (member fsd fsds :test #'same-fsd-p)
        (cerror2 "Multiple sort declaration for function ~S is unimplemented."
                 (function-name function))
;;      (setf (function-sort-declarations function) (process-function-sorts (cons fsd fsds)))
        )))))

;;; multiple sort declarations are not allowed for
;;; :alist, :plist, and :list* relations and functions
;;;
;;; consider the sort declarations
;;; (declare-relation 'p :alist :sort '(true (:a dog) (:b dog)))
;;; (declare-relation 'p :alist :sort '(true (:a cat) (:b cat)))
;;; 
;;; ((:a . fido) . ?) and ((:b . felix) . ?) are well sorted
;;; but their unifier ((:a . fido) (:b . felix) . ?) is not
;;;
;;; we cannot use multiple sort declarations if we assume
;;; that well-sortedness is inherited by instances but not all
;;; arguments are present when well-sortedness is checked initially
;;;
;;; the situation is even worse for :list* relations and functions
;;; because their argument lists can end in variables other than ?
;;; even single sort declarations may be violated when these
;;; tail variables are instantiated

(defun declare-alist-function-sort (function fsd)
  (let ((fsds (function-sort-declarations function)))
    (cond
     ((null fsds)
      (setf (function-sort-declarations function) (list fsd)))
     (t
      (unless (member fsd fsds :test #'same-fsd-p)
        (cerror2 "Multiple sort declaration for ~(~A~) ~As like ~S is not allowed."
                 (function-arity function)
                 (function-kind-string function)
                 (function-name function)))))))

(defun declare-list*-function-sort (function fsd)
  ;; do the declaration anyway, and note the fact that
  ;; instantiation of the tail variable may yield a non-well-sorted term or atom?
  (declare (ignore fsd))
  (cerror2 "Sort declaration for ~(~A~) ~As like ~S is not allowed."
           (function-arity function)
           (function-kind-string function)
           (function-name function)))

;;; ASSUME THAT SORT COERCION IS UNITARY
;;; not for functions with special unification algorithms

(defun coerce-list (l subst fsd)
  (do ((l l (rest l))
       (i 1 (1+ i)))
      ((null l)
       subst)
    (when (eq none (setq subst (coerce-term (first l) subst (fsd-arg-sort fsd i))))
      (return none))))

(defun coerce-compound (x subst new-sort)
  ;; the current sort scheme ensures that only the first sort declaration
  ;; whose result sort is a subsort of new-sort must be tried
  (cl:assert (and new-sort (neq top-sort new-sort)))
  (let* ((head (head x))
         (fsds (function-sort-declarations head)))
    (cond
     ((null fsds)
      none)
     ((null (rest fsds))
      (if (fsd-subsort-p (first fsds) new-sort) subst none))
     (t
      (let ((args (args x)))
        (case (function-arity head)
          ((:alist :plist :list*)
           ;; these don't have multiple sort declarations
           (unimplemented))
          (otherwise
           (dolist (fsd fsds)
             (when (fsd-subsort-p fsd new-sort)
               (return (coerce-list args subst fsd)))))))))))

(defun coerce-term (x subst new-sort)
  (cl:assert (and new-sort (neq top-sort new-sort)))
  (dereference
   x subst
   :if-variable (let ((s (variable-sort x)))
                  (cond
                   ((subsort-p s new-sort)
                    subst)
                   ((variable-frozen-p x)
                    none)
                   ((subsort-p new-sort s)
                    (bind-variable-to-term x (make-variable new-sort) subst))
                   (t
                    (let ((s* (sort-intersection s new-sort)))
                      (if (neq bottom-sort s*)
                          (bind-variable-to-term x (make-variable s*) subst)
                          none)))))
   :if-compound (coerce-compound x subst new-sort)
   :if-constant (if (subsort-p (constant-sort x) new-sort) subst none)))

(defvar *%check-for-well-sorted-atom%* t)

(defun check-for-well-sorted-atom (atom &optional subst)
  (when *%check-for-well-sorted-atom%*
    (assert-atom-is-well-sorted atom subst))
  atom)

(defun assert-atom-is-well-sorted (atom &optional subst)
  (or (well-sorted-p atom subst)
      (error "Atomic formula ~A is not well sorted." (term-to-lisp atom subst))))

(defun check-well-sorted (x &optional subst)
  (unless (well-sorted-p x subst)
    (error "~A is not well sorted." (term-to-lisp x subst)))
  x)

(defvar *%checking-well-sorted-p%* nil)

(defun well-sorted-p (x &optional subst (sort top-sort))
  ;; determines if expression is well sorted
  ;; it does this by doing well-sorting on the expression
  ;; with the restriction that no instantiation be done
  (prog->
    (quote t -> *%checking-well-sorted-p%*)
    (well-sort x subst sort ->* subst)
    (declare (ignore subst))
    (return-from prog-> t)))

(defun well-sorted-args-p (args subst fsd &optional (argcount 0))
  (prog->
    (quote t -> *%checking-well-sorted-p%*)
    (well-sort-args args subst fsd argcount ->* subst)
    (declare (ignore subst))
    (return-from prog-> t)))    

(defun term-sort (term &optional subst)
  ;; return sort of well-sorted term
  (dereference
   term subst
   :if-variable (variable-sort term)
   :if-constant (progn
                  (cl:assert (not (constant-boolean-valued-p term)))
                  (constant-sort term))
   :if-compound (let* ((head (head term))
		       (fsds (function-sort-declarations head)))
                  (cl:assert (not (function-boolean-valued-p head)))
		  (cond
                   ((null fsds)
                    top-sort)
                   ((null (rest fsds))
                    (fsd-result-sort (first fsds)))
                   (t
                    (case (function-arity head)
                      ((:alist :plist :list*)
                       ;; these don't have multiple sort-declarations
                       (unimplemented))
                      (otherwise
                       (let ((args (args term))
                             (sort top-sort))
                         (when (and (function-associative head) (cddr args))
                           (setq args (list (first args) (make-compound* head (rest args)))))
                         (dolist (fsd fsds)
                           (let ((fsd-sort (fsd-result-sort fsd)))
                             (when (and (not (subsort-p sort fsd-sort))
                                        (not (sort-disjoint-p sort fsd-sort))
                                        (well-sorted-args-p args subst fsd))
                               (setq sort (sort-intersection sort fsd-sort)))))
                         sort))))))))

(defun well-sort (cc x &optional subst (sort top-sort))
  (dereference
   x subst
   :if-variable (cond
                 ((or (eq top-sort sort) (subsort-p (variable-sort x) sort))
                  (funcall cc subst))
                 (*%checking-well-sorted-p%*
                  )
                 ((subsort-p sort (variable-sort x))
                  (funcall cc (bind-variable-to-term x (make-variable sort) subst)))
                 (t
                  (let ((sort (sort-intersection sort (variable-sort x))))
                    (unless (eq bottom-sort sort)
                      (funcall cc (bind-variable-to-term x (make-variable sort) subst))))))
   :if-constant (when (or (eq top-sort sort) (subsort-p (constant-sort x) sort))
                  (funcall cc subst))
   :if-compound (let* ((head (head x))
                       (args (args x))
                       (fsds (function-sort-declarations head)))
                  (cond
                   ((null fsds)
                    (well-sort-args cc args subst nil))
                   (t
                    (case (function-arity head)
                      ((:alist :plist)
                       (dolist (fsd fsds)
                         (when (fsd-subsort-p fsd sort)
                           (well-sort-alist cc (first args) subst fsd))))
                      (:list*
                       (dolist (fsd fsds)
                         (when (fsd-subsort-p fsd sort)
                           (well-sort-args cc (first args) subst fsd))))
                      (otherwise
                       (when (and (function-associative head) (cddr args))
                         (setq args (list (first args) (make-compound* head (rest args)))))
                       (dolist (fsd fsds)
                         (when (fsd-subsort-p fsd sort)
                           (well-sort-args cc args subst fsd)))))))))
  nil)

(defun well-sort-args (cc args subst fsd &optional (argcount 0))
  (dereference
   args subst
   :if-constant (funcall cc subst)
   :if-variable (funcall cc subst)
   :if-compound-appl (funcall cc subst)
   :if-compound-cons (prog->
                       (well-sort (carc args) subst (fsd-arg-sort fsd (incf argcount)) ->* subst)
                       (well-sort-args (cdrc args) subst fsd argcount ->* subst)
                       (funcall cc subst)))
  nil)

(defun well-sort-alist (cc alist subst fsd)
  (dereference
   alist subst
   :if-constant (funcall cc subst)	;nil at the end of the alist
   :if-variable (funcall cc subst)	;well-sorted except for future binding of this variable
   :if-compound-cons (prog->
                       (carc alist -> p)
                       (well-sort (cdr p) subst (fsd-arg-sort fsd (car p)) ->* subst)
                       (well-sort-alist (cdrc alist) subst fsd ->* subst)
                       (funcall cc subst)))
  nil)

(defun well-sort-atoms (cc atoms subst)
  (cond
   ((null atoms)
    (funcall cc subst))
   (t
    (prog->
      (well-sort (first atoms) subst ->* subst)
      (well-sort-atoms (rest atoms) subst ->* subst)
      (funcall cc subst)))))

(defun well-sort-atoms1 (cc atoms subst)
  (prog->
    (quote t -> first)
    (well-sort-which-atoms atoms subst -> atoms)
    (replace-skolem-terms-by-variables-in-atoms atoms subst -> atoms2 sksubst)
    (well-sort-atoms atoms2 subst ->* subst)
    (unless (fix-skolem-term-sorts sksubst first subst)
      (cerror "Use only first instance."
              "Input wff has more than well-sorted instance of existentially quantifed variable.")
      (return-from prog->))
    (setq first nil)
    (funcall cc subst)))

(defun well-sort-which-atoms (atoms &optional subst)
  (prog->
    (delete-if atoms ->* atom)
    (cond
     ((well-sorted-p atom subst)
      t)
     ((eq :terms (use-well-sorting?))
      (cond
       ((well-sorted-p (args atom) subst)
        (warn "Atomic formula ~A is not well sorted.~%Its arguments are well sorted, so will continue."
              (term-to-lisp atom subst))
        t)
       (t
        (warn "Atomic formula ~A is not well sorted.~%Will try to make its arguments well sorted and continue."
              (term-to-lisp atom subst))
        nil)))
     (t
      (warn "Atomic formula ~A is not well sorted." (term-to-lisp atom subst))
      nil))))

(defun well-sort-wff (cc wff &optional subst)
  (cond
   ((and *using-sorts* (use-well-sorting?))
    (well-sort-atoms1 cc (atoms-in-wff wff subst) subst))
   (t
    (funcall cc subst))))

(defun well-sort-wffs (cc wffs &optional subst)
  (cond
   ((and *using-sorts* (use-well-sorting?))
    (well-sort-atoms1 cc (atoms-in-wffs wffs subst) subst))
   (t
    (funcall cc subst))))

(defun replace-skolem-terms-by-variables-in-atoms (atoms &optional subst)
  ;; this garbage is for HPKB and is needed for
  ;; automatic well-sorting of unsorted wffs with existential quantifiers,
  ;; which shouldn't even be allowed
  ;; intended for freshly skolemized formulas; no skolem terms embedded in skolem terms
  (let ((sksubst nil))
    (values
     (prog->
       (mapcar atoms ->* atom)
       (map-terms-in-atom-and-compose-result atom subst ->* term polarity)
       (declare (ignore polarity))
       (dereference
        term subst
        :if-variable term
        :if-constant (if (constant-skolem-p term)
                         (let ((v (lookup-value-in-substitution term sksubst)))
                           (when (eq none v)
                             (setq v (make-variable (constant-sort term)))
                             (setq sksubst (bind-variable-to-term v term sksubst)))
                           v)
                         term)
        :if-compound (let ((fn (head term)))
                       (if (function-skolem-p fn)
                           (let ((v (lookup-value-in-substitution2 term sksubst subst)))
                             (when (eq none v)
                               (setq v (make-variable (caar (function-sort-declarations fn))))
                               (setq sksubst (bind-variable-to-term v term sksubst)))
                             v)
                           term))))
     sksubst)))

(defun fix-skolem-term-sorts (sksubst first subst)
  (do ((l sksubst (cddr l)))
      ((null l)
       t)
    (let ((sort (let ((var (first l)))
                  (dereference var subst)
                  (variable-sort var)))
          (val (second l)))
      (dereference
       val nil
       :if-constant (unless (same-sort-p sort (constant-sort val))
                      (if first
                          (setf (constant-sort val) sort)
                          (return nil)))
       :if-compound (let* ((head (head val))
                           (fsd (first (function-sort-declarations head))))
                      (unless (same-sort-p sort (fsd-result-sort fsd))
                        (if first
                            (setf (function-sort-declarations head)
                                  (list (make-function-sort-declaration
                                         :result-sort sort
                                         :argument-sort-alist (fsd-argument-sort-alist fsd))))
                            (return nil))))))))

(defun term-subsort-p (term1 term2 &optional subst)
  (OR (DEREFERENCE					;allows wffs for rewriting
       TERM2 SUBST
       :IF-CONSTANT (CONSTANT-BOOLEAN-VALUED-P TERM2)
       :IF-COMPOUND-APPL (FUNCTION-BOOLEAN-VALUED-P (HEADA TERM2))
       :IF-VARIABLE (DEREFERENCE
		     TERM1 SUBST
		     :IF-CONSTANT (CONSTANT-BOOLEAN-VALUED-P TERM1)
		     :IF-COMPOUND-APPL (FUNCTION-BOOLEAN-VALUED-P (HEAD TERM1))))
      (let ((sort2 (term-sort term2 subst)))
        (or (eq top-sort sort2)
            (subsort-p (term-sort term1 subst) sort2)))))

(defun sort-compatible-p (term1 term2 &optional subst)
  (let ((sort2 (term-sort term2 subst)))
    (or (eq top-sort sort2)
	(not (sort-disjoint-p (term-sort term1 subst) sort2)))))

(defun process-function-sorts (fsds)
  (declare (ignorable fsds))
  (unimplemented)
  #||
  (setq fsds (delete-duplicates (copy-list fsds)
                                :test (lambda (fsd1 fsd2)
                                        (every #'sort-equivalent-p fsd1 fsd2))))
  (dotails (l fsds)
    (let ((fsd1 (first fsds)))
      (dolist (fsd2 (rest fsds))
        (cond
         ((sort-disjoint-p (first fsd1) (first fsd2))
          (unless (some #'sort-disjoint-p (rest fsd1) (rest fsd2))
            (error "Result sort is disjoint but argument sort is not:~{~%~A~}."
                   (list (fsd-name fsd1)
                         (fsd-name fsd2)))))
         ((sort-equivalent-p (first fsd1) (first fsd2))
          (dolist (fsd3 fsds)
            (when (and (neq fsd1 fsd3)
                       (neq fsd2 fsd3)
                       (supersort-p (first fsd3) (first fsd1))
                       (not (subsort-p (first fsd3) (first fsd1))))
              (error "Illegal combination of sort declarations:~{~%~A~}."
                     (list (fsd-name fsd3)
                           (fsd-name fsd1)
                           (fsd-name fsd2))))))
         ((if (subsort-p (first fsd2) (first fsd1))
              (progn (psetq fsd1 fsd2 fsd2 fsd1) t)
              (subsort-p (first fsd1) (first fsd2)))
          (unless (and (every #'subsort-p (rest fsd1) (rest fsd2))
                       (notevery #'supersort-p (rest fsd1) (rest fsd2)))
            (error "Result sort is subsort but argument sort is not:~{~%~A~}."
                   (list (fsd-name fsd1)
                         (fsd-name fsd2)))))
         (t
          (error "Result sort is not subsort or disjoint:~{~%~A~}."
                 (list (fsd-name fsd1)
                       (fsd-name fsd2))))))))
  (sort fsds #'supersort-p :key #'first)
  ||#
  )

(defun associative-function-sort (fn)
  (let ((fsds (function-sort-declarations fn)))
    (cond
     ((null fsds)
      top-sort)
     ((rest fsds)
      (error "The associative function ~A can have only one sort declaration." fn))
     (t
      (let ((sort (fsd-result-sort (first fsds))))
        (cond
         ((and (same-sort-p sort (fsd-arg-sort (first fsds) 1))
               (same-sort-p sort (fsd-arg-sort (first fsds) 2))
               (every (lambda (p) (same-sort-p sort (cdr p)))
                      (fsd-argument-sort-alist (first fsds))))
          sort)
         (t
          (error "The sort of associative function ~S must be of form (S (1 S) (2 S))." fn))))))))

(defun print-sort-theory ()
  (ecase (use-sort-implementation?)
    (:dp
     (dp-print-sort-theory))
    ((:km :bdd)
     (unimplemented))))

(defun declare-sorts (declarations)
  ;; declare sorts in depth-first order
  (let ((todo nil) (done nil) sort)
    (dolist (decl declarations)
      (when (eq 'declare-subsort (first decl))
	(setq sort (first (last decl)))
	(when (and (not (member sort todo))
		   (dolist (decl declarations t)
		     (when (and (eq 'declare-subsort (first decl))
				(rest (member sort (rest decl))))
		       (return nil))))
	  (push sort todo))))
    (loop
      (when (null todo)
	(return))
      (setq sort (pop todo))
      (unless (member sort done)
	(declare-sort sort)
	(dolist (decl declarations)
	  (when (and (eq 'declare-subsort (first decl))
		     (member sort (rest (rest decl))))
	    (push (second (member sort (reverse (rest decl)))) todo)))
	(push sort done)))
    (declare-sorts2 declarations)))

(defun declare-sorts2 (declarations)
  (let ((*bdd* *sort-theory*))
    (declare (special *bdd*))
    (setq declarations (mapcar (lambda (decl)
                                 (mvlet (((:values max-sort min-sort)
                                          (max-and-min-sorts (rest decl))))
                                   (list* (- max-sort min-sort) min-sort decl)))
			       declarations))
    (setq declarations (sort declarations (lambda (x y)
                                            (or (< (first x) (first y))
                                                (and (= (first x) (first y))
                                                     (> (second x) (second y)))))))
    (setq declarations (mapcar #'cddr declarations))
    (dolist (decl declarations)
      (apply (first decl) (rest decl)))))

(defun max-and-min-sorts (sorts)
  (let* ((max-sort (bdd-node-if (declare-sort (first sorts))))
	 (min-sort max-sort))
    (dolist (sort (rest sorts))
      (let ((n (bdd-node-if (declare-sort sort))))
	(cond
	  ((> n max-sort)
	   (setq max-sort n))
	  ((< n min-sort)
	   (setq min-sort n)))))
    (values max-sort min-sort)))

(defmethod checkpoint-theory ((theory (eql 'sortal)))
  (ecase (use-sort-implementation?)
    (:dp
     (checkpoint-dp-sort-theory *sort-theory*))
    ((:km :bdd)
     (unimplemented))))

(defmethod restore-theory ((theory (eql 'sortal)))
  (clear-sort-caches)
  (ecase (use-sort-implementation?)
    (:dp
     (restore-dp-sort-theory *sort-theory*))
    ((:km :bdd)
     (unimplemented))))

(defmethod uncheckpoint-theory ((theory (eql 'sortal)))
  (ecase (use-sort-implementation?)
    (:dp
     (uncheckpoint-dp-sort-theory *sort-theory*))
    ((:km :bdd)
     (unimplemented))))

;;; sorts.lisp EOF
