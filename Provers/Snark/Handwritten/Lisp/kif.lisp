;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: kif.lisp
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

(declare-snark-option kif-nonasserted-relations-without-warning
                      '(nth-domain domain range domains
                        nth-domain-subclass-of domain-subclass-of
                        range-subclass-of slot-value-type
                        nth-argument-name domain-name range-name
                        arity function-arity relation-arity
                        documentation author source
                        binary-relation)
                      :never-print)
(declare-snark-option kif-nonasserted-relations-with-warning
                      '(relation function individual slot undefined my-source)
                      :never-print)
(declare-snark-option kif-nondenied-relations-without-warning
                      '()
                      :never-print)
(declare-snark-option kif-nondenied-relations-with-warning
                      '()
                      :never-print)

(declaim (special *processing-row*))

(defvar *form-author* nil)
(defvar *form-documentation* nil)
(defvar *form-name* nil)
(defvar *form-source* nil)

(defvar *kif-assertion-options* nil)
(defvar *kif-form* nil)
(defvar *kif-def-kind* nil)
(defvar *load-kif-file-phase* nil)	;:sorts, :symbols, :wffs

(defvar *kif-assertable-constant-slots*
  (set-difference
   (list* 'alias 'documentation 'author 'source (mapcar #'first constant-slots))
   '(sort number hash-code boolean-valued-p skolem-p created-p in-use plist)))

(defvar *kif-assertable-function-slots*
  (set-difference
   (list* 'alias 'documentation 'author 'source (mapcar #'first function-slots))
   '(name arity sort-declarations boolean-valued-p skolem-p created-p
     rewritable-p hash-code logical-symbol-p logical-symbol-dual polarity-map
     equal-code variant-code unify-code
     permutations permutations-min rewrites make-compound-function make-compound*-function
     code-name0 complement number plist)))

(defun initialize-kif ()
  (when (use-kif-rewrites?)
    (declare-relation 'instance-of 2 :rewrite-code 'instance-of-rewriter
;;                              :satisfy-code 'instance-of-satisfier
                              )
    (declare-relation 'subclass-of 2 :rewrite-code 'subclass-of-rewriter)))

(defun kif-variable-list-p (x)
  (and (listp x)
       (dotails (l x t)
         (unless (and (can-be-free-variable-name-p (first l))
                      (not (member (first l) (rest l))))
           (return nil)))))

(defun kif-assertion-sent-name (x)
  (case (head-is-logical-symbol x)
    ((nil)
     (dereference
      x nil
      :if-constant x
      :if-compound (cond
		     ((equality-p x)
		      (or (kif-assertion-sent-name (arg1 x))
			  (kif-assertion-sent-name (arg2 x))))
		     (t
		      (function-name (head x))))))
    (not
     (kif-assertion-sent-name (arg1 x)))
    (implies
     (kif-assertion-sent-name (arg2 x)))
    (implied-by
     (kif-assertion-sent-name (arg1 x)))
    (iff
     (kif-assertion-sent-name (arg1 x)))))

(defun kif-assertion-conc-name (form wff)
  (let ((sym (kif-assertion-sent-name wff)))
    (cond
      ((and form sym)
       (format nil "~A-~A-~A-" (first form) (second form) sym))
      (form
       (format nil "~A-~A-" (first form) (second form)))
      (sym
       (format nil "~A-" sym))
      (t
       nil))))

(defun subclass-of-sort-name-p (sort-name)
  (let* ((str (symbol-name sort-name))
         (len (length str)))
    (and (<= 14 len) (equal "SUBCLASS-OF-" (subseq str 0 12)))))

(defun subclass-of-sort-name (sort-name)
  (assert-can-be-sort-name-p sort-name)
  (cl:assert (not (subclass-of-sort-name-p sort-name)))
  (let ((str (symbol-name sort-name)))
    (intern (concatenate 'string "SUBCLASS-OF-" str) :snark)))

(defun kif-fix-sort-spec (x)
  (cond
   ((atom x)
    x)
   ((and (eq 'subclass-of (first x)) (eql 2 (length x)) (can-be-sort-name-p (second x)))
    (subclass-of-sort-name (second x)))
   (t
    (lcons (kif-fix-sort-spec (car x))
           (kif-fix-sort-spec (cdr x))
           x))))

(defun kif-declare-constant-symbol (name &rest declare-constant-symbol-options)
  (apply 'declare-constant
         name
         (append declare-constant-symbol-options
                 (list :documentation *form-documentation*
                       :author *form-author*
                       :source *form-source*))))

(defun kif-declare-function-symbol (name arity &rest declare-function-symbol-options)
  (let ((fn (apply 'declare-function
                   name
                   arity
                   (append declare-function-symbol-options
                           (list :documentation *form-documentation*
                                 :author *form-author*
                                 :source *form-source*)))))
    ;; create rewrite for (f a b c) -> (= (f a b) c)
    (cond
     ((numberp arity)
      (let* ((fsd (function-sort-declaration fn))		;assume single sort declaration
             (result-sort (fsd-result-sort fsd))
	     (sort-alist (fsd-argument-sort-alist fsd))
             (value (make-variable result-sort))
             (args nil))
        (dotimes (i arity)
          (declare (ignorable i))
          (push (make-variable (if fsd (fsd-arg-sort fsd (1+ i)) top-sort)) args))
        (setq args (renumber (cons value (nreverse args))))
        (setq value (pop args))
        (assert-rewrite
         (make-compound *iff*
                        (make-compound*
                         (let ((*%print-symbol-table-warnings%* nil))
                           (if fsd
                               (declare-relation
                                name (1+ arity)
                                :sort (mapcar (lambda (x) (list (car x) (cdr x)))
                                              (ACONS (1+ ARITY) RESULT-SORT SORT-ALIST)))
                               (declare-relation
                                name (1+ arity))))
                         (append args (list value)))
                        (make-compound
                         *=*
                         (make-compound* fn args)
                         value))
         :input nil))))
    fn))

(defun kif-declare-predicate-symbol (name arity &rest declare-predicate-symbol-options)
  (apply 'declare-relation
         name arity
         (append declare-predicate-symbol-options
                 (list :documentation *form-documentation*
                       :author *form-author*
                       :source *form-source*))))

(defun kif-declare-sort (s)
  (let ((ss (subclass-of-sort-name s)))
    (prog1
      (declare-sort s
                    :documentation *form-documentation*
                    :author *form-author*
                    :source *form-source*)
      (declare-sort ss
                    :documentation (concatenate
                                    'string
                                    "A class whose instances are subclasses of "
                                    (symbol-name s))
                    :author *form-author*
                    :source *form-source*)
      (when (test-option1?)
	(declare-disjoint-sorts s ss))
      (declare-subsort ss 'class)	;do we really want this?
      (kif-declare-sort2 s)
      )))

(defun kif-declare-sort2 (s)
  (let ((ss (subclass-of-sort-name s)))
    (kif-declare-constant-symbol s :sort ss)
    (declare-constant-sort s (declare-sort* 'predicate))
    (kif-assert `(forall ((v ,s)) (instance-of v ,s))
                :supported (or (assert-supported?) :uninherited))
    (kif-declare-predicate-symbol s 1)
    (assert-rewrite `(iff (,s ?x) (instance-of ?x ,s)))
    (kif-assert `(forall ((v ,ss)) (subclass-of v ,s))
                :supported (or (assert-supported?) :uninherited))
;;  (kif-declare-predicate-symbol ss 1)
;;  (assert-rewrite `(iff (,ss ?x) (subclass-of ?x ,s)))
    ))

(defun kif-sort-sentence (wff)
  (assert-sort-definition
   (term-to-lisp
    (prog->
      (quote nil -> var)
      (map-atoms-in-wff-and-compose-result (input-wff wff) ->* atom polarity)
      (declare (ignore polarity))
      (cond
       ((and (consp atom)
             (sort-name-p (function-name (head atom)))
             (let ((args (args atom)))
               (and (eql 1 (length args))
                    (if var
                        (eq var (first args))
                        (and (variable-p (setq var (first args)))
                             (eq top-sort (variable-sort var)))))))
        (function-name (head atom)))
       ((and (consp atom)
             (eq 'instance-of (function-name (head atom)))
             (let ((args (args atom)))
               (and (eql 2 (length args))
                    (sort-name-p (second args))
                    (if var
                        (eq var (first args))
                        (and (variable-p (setq var (first args)))
                             (eq top-sort (variable-sort var)))))))
        (arg2 atom))
       (t
        (return-from kif-sort-sentence
          nil))))))
  t)

(defun kif-nonasserted-relation-without-warning? (name)
  (or (member name (kif-nonasserted-relations-without-warning?))
      (case *kif-def-kind*
        (:object
         (member name *kif-assertable-constant-slots*))
        ((:function :relation)
         (member name *kif-assertable-function-slots*)))))

(defun kif-nonasserted-relation-with-warning? (name)
  (member name (kif-nonasserted-relations-with-warning?)))

(defun kif-nondenied-relation-without-warning? (name)
  (member name (kif-nondenied-relations-without-warning?)))

(defun kif-nondenied-relation-with-warning? (name)
  (member name (kif-nondenied-relations-with-warning?)))

(defun kif-assert (wff &rest assert-options)
  (apply 'assert
         wff
         (append *kif-assertion-options*
                 assert-options
                 (list :documentation *form-documentation*
                       :author *form-author*
                       :source *form-source*
                       :name *form-name*
                       :conc-name (let ((form *kif-form*))
                                    (lambda (wff) (kif-assertion-conc-name form wff)))))))

(defun kif-deny (wff &rest kif-assert-options)
  (apply 'kif-assert `(not ,wff) kif-assert-options))

(defun kif-assert-sentence (sentence)
  (cond
   ((not (consp sentence))
    (warn "Ignoring ~A." sentence))
   (t
    (kif-assert-sentence* (first sentence) sentence))))

(defun kif-deny-sentence (sentence)
  (cond
   ((not (consp sentence))
    (warn "Ignoring ~A." `(not ,sentence)))
   (t
    (kif-deny-sentence* (first sentence) sentence))))

(defmethod kif-assert-sentence* (head sentence)
  (when (implies *load-kif-file-phase* (eq :wffs *load-kif-file-phase*))
    (cond
     ((kif-nonasserted-relation-without-warning? head)
      )
     ((kif-nonasserted-relation-with-warning? head)
      (warn "Ignoring ~A." sentence))
     (t
      (kif-assert sentence)))))

(defmethod kif-deny-sentence* (head sentence)
  (when (implies *load-kif-file-phase* (eq :wffs *load-kif-file-phase*))
    (cond
     ((kif-nondenied-relation-without-warning? head)
      )
     ((kif-nondenied-relation-with-warning? head)
      (warn "Ignoring ~A." `(not ,sentence)))
     (t
      (kif-deny sentence)))))

(defmethod kif-assert-sentence* :around ((head (eql 'not)) sentence)
  (kif-deny-sentence (second sentence)))

(defmethod kif-deny-sentence* :around ((head (eql 'not)) sentence)
  (kif-assert-sentence (second sentence)))

(defmethod kif-assert-sentence* :around ((head (eql 'and)) sentence)
  (mapc #'kif-assert-sentence (rest sentence)))

(defmethod kif-deny-sentence* :around ((head (eql 'or)) sentence)
  (mapc #'kif-deny-sentence (rest sentence)))

(defmethod kif-assert-sentence* :around ((head (eql 'class)) sentence)
  (let ((s (second sentence)))
    (cond
     ((can-be-sort-name-p s 'warn)
      (when (implies *load-kif-file-phase* (eq :sorts *load-kif-file-phase*))
        (kif-declare-sort s)))
     (t
      (call-next-method)))))

(defmethod kif-assert-sentence* :around ((head (eql 'subclass-of)) sentence)
  (let ((s1 (second sentence))
        (s2 (third sentence)))
    (cond
     ((let ((v1 (can-be-sort-name-p s1 'warn))
            (v2 (can-be-sort-name-p s2 'warn)))
        (and v1 v2))
      (when (implies *load-kif-file-phase* (eq :sorts *load-kif-file-phase*))
        (declare-subsort s1 s2)
        (declare-subsort (subclass-of-sort-name s1) (subclass-of-sort-name s2))))
     (t
      (call-next-method)))))

(defmethod kif-assert-sentence* :around ((head (eql 'disjoint-with)) sentence)
  (let ((s1 (second sentence))
        (s2 (third sentence)))
    (cond
     ((let ((v1 (can-be-sort-name-p s1 'warn))
            (v2 (can-be-sort-name-p s2 'warn)))
        (and v1 v2))
      (when (implies *load-kif-file-phase* (eq :sorts *load-kif-file-phase*))
        (declare-disjoint-sorts s1 s2)
        (declare-disjoint-sorts (subclass-of-sort-name s1) (subclass-of-sort-name s2))))
     (t
      (call-next-method)))))

(defmethod kif-assert-sentence* :around ((head (eql 'instance-of)) sentence)
  (let ((c (second sentence))
        (s (third sentence)))
    (cond
     ((can-be-relation-name-p c)
      (when (implies *load-kif-file-phase* (eq :wffs *load-kif-file-phase*))
        (case s
          (anti-symmetric-binary-predicate
           (kif-assert (anti-symmetric-binary-predicate-wff c)))
          (anti-transitive-binary-predicate
           (kif-assert (anti-transitive-binary-predicate-wff c)))
          (asymmetric-binary-predicate
           (kif-assert (asymmetric-binary-predicate-wff c)))
          (irreflexive-binary-predicate
           (kif-assert (irreflexive-binary-predicate-wff c)))
          (reflexive-binary-predicate
           (kif-assert (reflexive-binary-predicate-wff c)))
          (symmetric-binary-predicate
           (kif-assert (symmetric-binary-predicate-wff c)))
          (transitive-binary-predicate
           (kif-assert (transitive-binary-predicate-wff c)))))))
    (cond
     ((and (can-be-free-variable-name-p c) (can-be-sort-name-p s 'warn))
      (when (implies *load-kif-file-phase* (eq :symbols *load-kif-file-phase*))
        (declare-variable c :sort s)))
     ((and (can-be-constant-name-p c) (can-be-sort-name-p s 'warn))
      (when (implies *load-kif-file-phase* (eq :symbols *load-kif-file-phase*))
        (declare-constant c :sort s)))
     (t
      (call-next-method)))))

(defmethod kif-deny-sentence* :around ((head (eql 'instance-of)) sentence)
  (let ((c (second sentence))
        (s (third sentence)))
    (cond
     ((can-be-relation-name-p c)
      (when (implies *load-kif-file-phase* (eq :wffs *load-kif-file-phase*))
        (case s
          (anti-symmetric-binary-predicate
           (kif-deny (anti-symmetric-binary-predicate-wff c)))
          (anti-transitive-binary-predicate
           (kif-deny (anti-transitive-binary-predicate-wff c)))
          (asymmetric-binary-predicate
           (kif-deny (asymmetric-binary-predicate-wff c)))
          (irreflexive-binary-predicate
           (kif-deny (irreflexive-binary-predicate-wff c)))
          (reflexive-binary-predicate
           (kif-deny (reflexive-binary-predicate-wff c)))
          (symmetric-binary-predicate
           (kif-deny (symmetric-binary-predicate-wff c)))
          (transitive-binary-predicate
           (kif-deny (transitive-binary-predicate-wff c)))))))
    (call-next-method)))

(defmethod kif-assert-sentence* :around ((head (eql 'the-partition)) sentence)
  (let ((s (rest sentence)))
    (cond
     #+ignore
     ((every (lambda (x) (can-be-sort-name-p x 'warn)) s)
      ;; interprets (THE-PARTITION A B C) as meaning C is the disjoint union of A and B,
      ;; not that C is an object of type partition
      (when (implies *load-kif-file-phase* (eq :sorts *load-kif-file-phase*))
        (apply 'declare-sort-partition (first (last s)) (butlast s))))
     ((every (lambda (x) (can-be-sort-name-p x 'warn)) s)
      (when (implies *load-kif-file-phase* (eq :sorts *load-kif-file-phase*))
        (apply #'declare-disjoint-sorts (butlast s)))
      (call-next-method))	;only disjointness information has been extracted
     (t
      (call-next-method)))))

(defmethod kif-assert-sentence* :around ((head (eql 'template-slot-value)) sentence)
  (let ((slot (second sentence))
        (class (third sentence))
        (value (fourth sentence)))
    (cond
     ((and (can-be-sort-name-p class 'warn) (can-be-function-name-p slot))
      (when (implies *load-kif-file-phase* (eq :symbols *load-kif-file-phase*))
        (declare-relation slot 2)
        (declare-sort class)
        (let ((v (intern (concatenate 'string "?" (symbol-name class)) :snark)))
          (declare-variable v :sort class)
          (kif-assert `(,slot ,v ,value)))
        (let* ((ss (subclass-of-sort-name class))
               (v (intern (concatenate 'string "?" (symbol-name ss)) :snark)))
          (declare-sort ss)
          (declare-variable v :sort ss)
          (kif-assert `(template-slot-value ,slot ,v ,value)))))
     (t
      (call-next-method)))))

(defmethod kif-assert-sentence* :around ((head (eql 'subrelation-of)) sentence)
  ;; 2000-02-09
  (call-next-method)
  (when (implies *load-kif-file-phase* (eq :wffs *load-kif-file-phase*))
    (let* ((r1 (second sentence))
           (r2 (third sentence))
           (v1 (can-be-relation-name-p r1 'warn))
           (v2 (can-be-relation-name-p r2 'warn)))
      (when (and v1 v2)
        (kif-assert `(implies (,r1 ?x ?y) (,r2 ?x ?y)))))))	;only for binary predicates

(defmethod kif-assert-sentence* :around ((head (eql 'subinverse-of)) sentence)
  ;; 2000-03-08
  (call-next-method)
  (when (implies *load-kif-file-phase* (eq :wffs *load-kif-file-phase*))
    (let* ((r1 (second sentence))
           (r2 (third sentence))
           (v1 (can-be-relation-name-p r1 'warn))
           (v2 (can-be-relation-name-p r2 'warn)))
      (when (and v1 v2)
        (kif-assert `(implies (,r1 ?x ?y) (,r2 ?y ?x)))))))	;only for binary predicates

(defmethod kif-assert-sentence* :around ((head (eql 'inverse)) sentence)
  ;; 2000-02-09
  (call-next-method)
  (when (implies *load-kif-file-phase* (eq :wffs *load-kif-file-phase*))
    (let* ((r1 (second sentence))
           (r2 (third sentence))
           (v1 (can-be-relation-name-p r1 'warn))
           (v2 (can-be-relation-name-p r2 'warn)))
      (when (and v1 v2)
        (kif-assert `(iff (,r1 ?x ?y) (,r2 ?y ?x)))))))		;use assert-rewrite instead?

(defun get-kif-info (name sentences result)
  (let ((type *kif-def-kind*) (props nil) (new-sentences nil) (sorted nil))
  (labels
    ((get-kif-info* (sentence)
         (let ((head (and (consp sentence) (first sentence))))
           (cond
            ((eq 'and head)
             (mapc #'get-kif-info* (rest sentence)))
            ((member head '(arity function-arity relation-arity))
             (arity-info sentence))
            ((member head '(class))
             (cl:assert (eq :relation type))
             (cl:assert (eql 2 (length sentence)))
             (arity-info `(relation-arity ,(second sentence) 1)))
            ((member head '(binary-relation
                            anti-symmetric-binary-relation
                            anti-transitive-binary-relation
                            asymmetric-binary-relation
                            irreflexive-binary-relation
                            reflexive-binary-relation
                            symmetric-binary-relation
                            transitive-binary-relation))
             (cl:assert (eql 2 (length sentence)))
             (ecase type
               (:relation
                (arity-info `(relation-arity ,(second sentence) 2)))
               (:function
                (arity-info `(function-arity ,(second sentence) 1)))))
            ((member head '(range range-subclass-of slot-value-type))
             (cl:assert (eql 3 (length sentence)))
             (cond
              ((eq 'slot-value-type head)
               (setq sentence `(range ,(second sentence) ,(third sentence))))
              ((eq 'range-subclass-of head)
               (setq sentence `(range ,(second sentence) ,(subclass-of-sort-name (third sentence))))))
             (get-name (second sentence))
             (get-sort (third sentence))
             (let ((v (assoc head result)))
               (cond
                ((null v)
                 (push (list (first sentence) (second sentence) (third sentence)) result))
                ((nequal sentence v)
                 (let ((s (sort-intersection (third v) (third sentence))))
                   (cl:assert (neq bottom-sort s))
                   (setf (third v) s))))))
            ((member head '(domain domain-subclass-of nth-domain nth-domain-subclass-of nth-argument-name))
             (cond
              ((eq 'domain head)
               (cl:assert (eql 3 (length sentence)))
               (setq sentence `(nth-domain ,(second sentence) 1 ,(third sentence))))
              ((eq 'domain-subclass-of head)
               (cl:assert (eql 3 (length sentence)))
               (setq sentence `(nth-domain ,(second sentence) 1 ,(subclass-of-sort-name (third sentence)))))
              ((eq 'nth-domain-subclass-of head)
               (cl:assert (eql 4 (length sentence)))
               (setq sentence `(nth-domain ,(second sentence) ,(third sentence) ,(subclass-of-sort-name (fourth sentence))))))
             (nth-arg-info sentence))
            ((eq 'domains head)
             ;; translate (domains name dom1 ... domn) to
             ;; (nth-domain name 1 dom1)
             ;;   :
             ;; (nth-domain name n domn)
             (cl:assert (<= 3 (length sentence)))
             (arity-info `(,(ecase type (:relation 'relation-arity) (:function 'function-arity))
                           ,(second sentence)
                           ,(length (cddr sentence))))
             (let ((i 0))
               (dolist (s (cddr sentence))
                 (nth-arg-info `(nth-domain ,(second sentence) ,(incf i) ,s)))))
	    #+ignore
            ((eq 'instance-of head)
             (cl:assert (eql 3 (length sentence)))
             (when (and (eq :object type)
                        (eql name (second sentence))
               (let* ((head (first sentence))
                      (v (assoc head result)))
                 (cond
                  (v
                   (cl:assert (equal v sentence) () "~A and ~A conflict." v sentence))
                  (t
                   (get-sort (third sentence))
                   (push sentence result)))))))
            ((member head (if (eq :object type)
                              *kif-assertable-constant-slots*
                              *kif-assertable-function-slots*))
             (cl:assert (eql 3 (length sentence)))
             (get-name (second sentence))
             (setq props (list* (intern (symbol-name head) :keyword) (third sentence) props)))
            (t
             (push sentence new-sentences))
            )))
     (get-name (nm)
       (cond
        ((eq none name)
         (if (eq :object type)
             (cl:assert (can-be-constant-name-p nm))
             (cl:assert (can-be-function-name-p nm)))
         (setq name nm))
        (t
         (cl:assert (eql name nm)))))
     (get-sort (nm)
       (assert-sort-name-p nm)
       (setq sorted t)
;;     (input-sort nm 'warn)
       )
     (arity-info (sentence)
       (let* ((head (first sentence))
              (v (assoc head result)))
         (cond
          (v
           (cl:assert (equal v sentence) () "~A and ~A conflict." v sentence))
          (t
           (cl:assert (eql 3 (length sentence)))
           (get-name (second sentence))
           (cl:assert (or (positive-integer-p (third sentence))
                          (eq :any (third sentence))))
           (push sentence result)))))
     (nth-arg-info (sentence)
       (cl:assert (eql 4 (length sentence)))
       (let* ((head (first sentence))
              (v (first (member-if (lambda (x)
                                     (and (eq head (first x))
                                          (eql (third sentence) (third x))))
                                   result))))
         (cond
          ((null v)
           (unless (eq 'nth-argument-name head)
             (get-sort (fourth sentence)))
           (push (list (first sentence) (second sentence) (third sentence) (fourth sentence)) result))
          ((eq 'nth-argument-name head)
           (cl:assert (equal v sentence) () "~A and ~A conflict." v sentence))
          ((nequal sentence v)
           (get-sort (fourth sentence))
           (let ((s (sort-intersection (fourth v) (fourth sentence))))
             (cl:assert (neq bottom-sort s))
             (setf (fourth v) s))))))
     (arity-from-domain-declarations (result)
       ;; return maximum domain number or nil if no domains are specified
       (let ((n 0))
         (dolist (x result)
           (when (and (eq 'nth-domain (first x)) (< n (third x)))
             (setq n (third x))))
         (cond
          ((eql 0 n)
           nil)
          ((and (eq :relation type) (assoc 'range result))
           (1+ n))
          (t
           n))))
     (arity-from-argument-name-declarations (result)
       (let ((N 0))
         (dolist (x result)
           (when (and (eq 'nth-argument-name (first x)) (< n (third x)))
             (setq n (third x))))
         (cond
          ((eql 0 n)
           nil)
          (t
           n))))
     (sort-list (arity range-sort)
       (let ((l (and range-sort (list range-sort))))
         (dotimes (i arity)
           (push (or (fourth (first (member-if (lambda (x)
                                                 (and (eq 'nth-domain (first x))
                                                      (eql (1+ i) (third x))))
                                               result)))
                     (and (eq :relation type) (third (assoc 'range result)))
                     true)
                 l))
         (nreverse l))))
    (mapc #'get-kif-info* sentences)
    ;; return list of name, arity, sort
    (values
    (ecase type
      (:object
       (list* name
              (let ((sort (third (assoc 'instance-of result))))
                (if sort
                    (list* :sort sort props)
                    props))))
      (:relation
       (let ((arity (or (third (assoc 'relation-arity result))
                        (third (assoc 'arity result))
                        (arity-from-domain-declarations result)
                        (arity-from-argument-name-declarations result))))
         (unless arity
           (error "Could not determine arity of ~A ~A." type name))
         (list* name
                (or arity :any)
                (if (and sorted arity)
                    (list* :sort
                           (sort-list arity nil)
                           props)
                    props))))
      (:function
       (let ((arity (or (third (assoc 'function-arity result))
                        (let ((n (third (assoc 'arity result))))
                          (when n
                            (warn "Interpreting ~A as ~A."
                                  `(arity ,name ,n)
                                  `(function-arity ,name ,(1- n)))
                            (1- n)))
                        (third (assoc 'arity result))
                        (arity-from-domain-declarations result)
                        (arity-from-argument-name-declarations result))))
         (unless arity
           (error "Could not determine arity of ~A ~A." type name))
         (list* name
                (or arity :any)
                (if (and sorted arity)
                    (list* :sort (sort-list arity (or (third (assoc 'range result)) true)) props)
                    props)))))
    (nreverse new-sentences)))))

(defun get-kif-doc (name sentences)
  (labels
    ((get-kif-doc* (sentence)
       (case (and (consp sentence) (first sentence))
         (and
          (mapc #'get-kif-doc* (rest sentence)))
         ((documentation author source)
          (cl:assert (eql 3 (length sentence)))
          (cond
           ((neql name (second sentence))
            (warn "Ignoring ~A." sentence))
           (t
            (ecase (first sentence)
              (documentation (setq *form-documentation* (third sentence)))
              (author        (setq *form-author*        (third sentence)))
              (source        (setq *form-source*        (third sentence))))))))))
    (mapc #'get-kif-doc* sentences))
  nil)

(defun kif-def1 (name sentences &optional assertions kif-info)
  (get-kif-doc name sentences)
  (when (implies *load-kif-file-phase* (eq :symbols *load-kif-file-phase*))
    (apply (ecase *kif-def-kind*
             (:object   #'kif-declare-constant-symbol)
             (:function #'kif-declare-function-symbol)
             (:relation #'kif-declare-predicate-symbol))
           (get-kif-info name sentences kif-info)))
  (mapc #'kif-assert-sentence (or assertions sentences))
  nil)

;;; kif-defobject, kif-deffunction, and kif-defrelation
;;; accept a superset of KIF 3.0 and ANSI KIF
;;; :axiom and :conservative-axiom were used only in KIF 3.0
;;; optional documentation strings were used only in ANSI KIF
;;;
;;; (defobject name [string] := term)
;;; (defobject name [string] :conservative-axiom sentence)
;;; (defobject name [string] :-> variable :=> sentence)
;;; (defobject name [string] :-> variable :<= sentence)
;;; (defobject name [string] . sentences)
;;;
;;; (deffunction name (variables) [string] := term)
;;; (deffunction name (variables) [string] :-> variable :=> sentence)
;;; (deffunction name (variables) [string] :-> variable :<= sentence)
;;; (deffunction name [string] :conservative-axiom sentence)
;;; (deffunction name [string] . sentences)
;;;
;;; (defrelation name (variables) [string] := sentence)
;;; (defrelation name (variables) [string] :<= sentence)
;;; (defrelation name (variables) [string] :=> sentence)
;;; (defrelation name (variables) [string] :=> sentence :axiom sentence)
;;; (defrelation name (variables) [string] :=> sentence :conservative-axiom sentence)
;;; (defrelation name [string] :conservative-axiom sentence)
;;; (defrelation name [string] . sentences)

(defun kif-defobject (form)
  (with-clock-on kif-input
    (cl:assert (<= 2 (length form)))
    (let ((name (second form))
          (args (rest (rest form)))
          (*kif-def-kind* :object)
          (*kif-form* form)
          (*form-documentation* *form-documentation*)
          (*form-author* *form-author*)
          (*form-source* *form-source*))
      (let ((v (first args)))
        (when (stringp v)
          (setq *form-documentation* v args (rest args))))
      (cond
       ((member := args)
        ;; (defobject name [string] := term)
        (cl:assert (and (eql 2 (length args))
                        (eq := (first args))))
        (kif-def1 name nil (list `(= ,name ,(second args)))))
       ((member :conservative-axiom args)
        ;; (defobject name [string] :conservative-axiom sentence)
        (cl:assert (and (eql 2 (length args))
                        (eq :conservative-axiom (first args))))
        (kif-def1 name (list (second args))))
       ((or (member :-> args) (member :=> args) (member :<= args))
        ;; (defobject name [string] :-> variable :=> sentence)
        ;; (defobject name [string] :-> variable :<= sentence)
        (cl:assert (and (eql 4 (length args))
                        (eq :-> (first args))
                        (can-be-free-variable-name-p (second args))
                        (member (third args) '(:=> :<=))))
        (kif-def1  name
                  (list (fourth args))
                  (list `(,(ecase (third args) (:=> '=>) (:<= '<=))
                          (= ,name ,(second args))
                          ,(fourth args)))))
       (t
        ;; (defobject name [string] . sentences)
        (kif-def1 name args)))
      name)))

(defun kif-deffunction (form)
  (with-clock-on kif-input
    (cl:assert (<= 2 (length form)))
    (let ((name (second form))
          (args (rest (rest form)))
          (*kif-def-kind* :function)
          (*kif-form* form)
          (*form-documentation* *form-documentation*)
          (*form-author* *form-author*)
          (*form-source* *form-source*))
      (assert-can-be-function-name-p name)
      (cond
       ((member := args)
        ;; (deffunction name (variables) [string] := term)
        (let ((v (second args)))
          (when (stringp v)
            (setq *form-documentation* v args (cons (first args) (rest (rest args))))))
        (cl:assert (and (eql 3 (length args))
                        (kif-variable-list-p (first args))
                        (eq := (second args))))
        (kif-def1 name
                  nil
                  (list `(= (,name ,@(first args)) ,(third args)))
                  (list `(function-arity ,name ,(length (first args))))))
       ((or (member :=> args) (member :<= args))
        ;; (deffunction name (variables) [string] :-> variable :=> sentence)
        ;; (deffunction name (variables) [string] :-> variable :<= sentence)
        (let ((v (second args)))
          (when (stringp v)
            (setq *form-documentation* v args (cons (first args) (rest (rest args))))))
        (cl:assert (and (eql 5 (length args))
                        (kif-variable-list-p (first args))
                        (eq :-> (second args))
                        (can-be-free-variable-name-p (third args))
                        (member (fourth args) '(:=> :<=))))
        (kif-def1 name
                  (list (fifth args))
                  (list `(,(ecase (fourth args) (:=> '=>) (:<= '<=))
                          (= (,name ,@(first args)) ,(third args))
                          ,(fifth args)))
                  (list `(function-arity ,name ,(length (first args))))))
       (t
        (let ((v (first args)))
          (when (stringp v)
            (setq *form-documentation* v args (rest args))))
        (cond
         ((member :conservative-axiom args)
          ;; (deffunction name [string] :conservative-axiom sentence)
          (cl:assert (and (eql 2 (length args))
                          (eq :conservative-axiom (first args))))
          (kif-def1 name (list (second args))))
         (t
          ;; (deffunction name [string] . sentences)
          (kif-def1 name args)))))
      name)))

(defun kif-defrelation (form)
  (with-clock-on kif-input
    (cl:assert (<= 2 (length form)))
    (let ((name (second form))
          (args (rest (rest form)))
          (*kif-def-kind* :relation)
          (*kif-form* form)
          (*form-documentation* *form-documentation*)
          (*form-author* *form-author*)
          (*form-source* *form-source*))
      (assert-can-be-function-name-p name)
      (cond
       ((member := args)
        ;; (defrelation name (variables) [string] := sentence)
        (let ((v (second args)))
          (when (stringp v)
            (setq *form-documentation* v args (cons (first args) (rest (rest args))))))
        (cl:assert (and (eql 3 (length args))
                        (kif-variable-list-p (first args))
                        (eq := (second args))))
        (kif-def1 name
                  (list (third args))
                  (list `(<=> (,name ,@(first args)) ,(third args)))
                  (list `(relation-arity ,name ,(length (first args))))))
       ((member :<= args)
        ;; (defrelation name (variables) [string] :<= sentence)
        (let ((v (second args)))
          (when (stringp v)
            (setq *form-documentation* v args (cons (first args) (rest (rest args))))))
        (cl:assert (and (eql 3 (length args))
                        (kif-variable-list-p (first args))
                        (eq :<= (second args))))
        (kif-def1 name
                  (list (third args))
                  (list `(<= (,name ,@(first args)) ,(third args)))
                  (list `(relation-arity ,name ,(length (first args))))))
       ((member :=> args)
        ;; (defrelation name (variables) [string] :=> sentence)
        ;; (defrelation name (variables) [string] :=> sentence :axiom sentence)
        ;; (defrelation name (variables) [string] :=> sentence :conservative-axiom sentence)
        (let ((v (second args)))
          (when (stringp v)
            (setq *form-documentation* v args (cons (first args) (rest (rest args))))))
        (cl:assert (and (member (length args) '(3 5))
                        (kif-variable-list-p (first args))
                        (eq ':=> (second args))))
        (kif-def1 name
                  (cons (third args)
                        (when (eql 5 (length args))
                          (cl:assert (member (fourth args) '(:axiom :conservative-axiom)))
                          (list (fifth args))))
                  (cons `(=> (,name ,@(first args)) ,(third args))
                        (when (eql 5 (length args))
                          (list (fifth args))))
                  (list `(relation-arity ,name ,(length (first args))))))
       (t
        (let ((v (first args)))
          (when (stringp v)
            (setq *form-documentation* v args (rest args))))
        (cond
         ((member :conservative-axiom args)
          ;; (defrelation name [string] :conservative-axiom sentence)
          (cl:assert (and (eql 2 (length args))
                          (eq :conservative-axiom (first args))))
          (kif-def1 name (list (second args))))
         (t
          ;; (defrelation name [string] . sentences)
          (kif-def1 name args)))))
      name)))

(defmacro defobject (&whole form name &rest args)
  (declare (ignore name args))
  `(kif-defobject ',form))

(defmacro deffunction (&whole form name &rest args)
  (declare (ignore name args))
  `(kif-deffunction ',form))

(defmacro defrelation (&whole form name &rest args)
  (declare (ignore name args))
  `(kif-defrelation ',form))

(defun instance-of-satisfier (cc atom subst)
  (mvlet (((:list x class) (args atom)))
    (dereference
     class subst
     :if-constant (let ((sort2 (find-symbol-table-entry class :sort)))
                    (when (neq none sort2)
                      (unify cc (make-variable sort2) x))))))

(defun instance-of-rewriter (atom subst)
  (mvlet (((:list x class) (args atom)))
    (cond
     ((and (null subst)
           *processing-row*
           (eq 'assertion (row-reason *processing-row*))
           (redex-at-top?))
      none)
     (t
      (dereference
       class subst
       :if-variable none
       :if-constant (let ((sort2 (find-symbol-table-entry class :sort)))
                      (cond
                       ((neq none sort2)
                        (let ((sort1 (term-sort x subst)))
                          (cond
                           ((subsort-p sort1 sort2)
                            true)
                           ((sort-disjoint-p sort1 sort2)
                            false)
                           (t
                            none))))
                       (t
                        none)))
       :if-compound none)))))

(defun subclass-of-rewriter (atom subst)
  (cond
   ((and (null subst)
         *processing-row*
         (eq 'assertion (row-reason *processing-row*))
         (redex-at-top?))
    none)
   (t
    (mvlet (((:list class1 class2) (args atom)))
      (let ((sort1 (dereference
                    class1 subst
                    :if-variable none
                    :if-constant (find-symbol-table-entry class1 :sort)
                    :if-compound none)))
        (cond
         ((neq none sort1)
          (let ((sort2 (dereference
                        class2 subst
                        :if-variable none
                        :if-constant (find-symbol-table-entry class2 :sort)
                        :if-compound none)))
            (cond
             ((neq none sort2)
              (cond
               ((subsort-p sort1 sort2)
                true)
               ((sort-disjoint-p sort1 sort2)
                false)
	       (t
	        none)))
             (t
              none))))
         (t
          none)))))))

(defun sort-relativization (wff)
  ;; e.g.,
  ;;  (print-term
  ;;   (sort-relativization
  ;;    (input-wff '(all ((b1 :sort bird) (f1 :sort fox))
  ;;                 (m b1 f1)))))
  ;;
  ;; only variable sorts are examined,
  ;; i.e., not skolem function/constant sorts
  ;;
  ;; assume sort-name is a sort symbol
  ;;
  (let ((vars (variables wff)))
    (cond
     ((null vars)
      wff)
     (nil
      (make-implication
       (conjoin*
        (let ((instance-of (input-function 'instance-of 2)))
          (mapcan (lambda (var)
                    (let ((sort (variable-sort var)))
                      (cond
                       ((eq top-sort sort)
                        nil)
                       (t
                        (list (make-compound instance-of var (sort-name sort)))))))
	          vars)))
       wff))
     (t
      (let ((var-specs (mapcan (lambda (var)
                                 (let ((sort (variable-sort var)))
                                   (when (neq top-sort sort)
                                     (list (list var (sort-name sort))))))
                               vars)))
        (cond
         ((null var-specs)
          wff)
         (t
          (make-compound *forall*
                         var-specs
                         wff))))))))

(defmacro define-kb (name inclusion-list &rest args)
  (declare (ignore name inclusion-list args))
  `(warn "Ignoring DEFINE-KB form."))

(defmacro define-okbc-frame (&rest args)
  (declare (ignore args))
  `(warn "Ignoring DEFINE-OKBC-FRAME form."))

(defun snark-specified-p (system-spec)
  (if (consp system-spec)
      (ecase (first system-spec)
	(or
	 (some #'snark-specified-p (rest system-spec)))
	(and
	 (every #'snark-specified-p (rest system-spec)))
	(not
	 (not (snark-specified-p (second system-spec)))))
      (eq :snark system-spec)))

(defmacro when-system (system-spec &body forms)
  (when (snark-specified-p system-spec)
    (cons 'progn forms)))

(defvar *load-kif-forms-to-eval*
  '(in-package in-language in-kb 
    has-author has-documentation has-name has-source
    in-author in-documentation in-name in-source	;obsolete names
    defobject deffunction defrelation
    define-kb define-okbc-frame
    assertion when-system
    ))

(defvar *load-kif-forms-to-assert*
  '(forall exists and or not implies iff =
    all some
    => <= <=> /=
    ))

(defun load-kif-eval (form)
  ;; what load-kif does to each top-level form
  (let ((name (and (consp form) (first form))))
    (cond
     ((member name *load-kif-forms-to-eval*)
      (eval form))
     (t
      (when (implies *load-kif-file-phase* (neq :symbols *load-kif-file-phase*))
        (unless (member name *load-kif-forms-to-assert*)
          (warn "Asserting ~S." form))
        (kif-assert-sentence form))))))

(defvar *load-kif-file-verbose* t)
(defvar *load-kif-file-print* t)

(defun kif-definition-p (x)
  (and (consp x) (member (first x) '(defrelation deffunction defobject))))

(defun load-kif-file (filespec
                      &key
                      (if-does-not-exist :error)
                      (verbose *load-kif-file-verbose*)
                      (print *load-kif-file-print*)
                      (phases t))
  (when verbose
    (format t "~%;Loading ~A..." filespec))
  (load-kif-forms (read-kif-file filespec :if-does-not-exist if-does-not-exist)
                  :verbose verbose
                  :print print
                  :phases phases)
  t)

(defun read-kif-file (filespec &key (if-does-not-exist :error))
  (let ((*readtable* (copy-readtable nil))
	(*package* (find-package :snark))
	(*%use-kif-version%* *%use-kif-version%*))
    (values (prog->
	     (mapnconc-file-forms filespec :if-does-not-exist if-does-not-exist ->* form)
	     (when (and (consp form) (member (first form) '(in-package in-language)))
	       (eval form))
	     (list form))
            *package*			;last one used by in-package
	    *%use-kif-version%*		;last one used by in-language
            )))

(defun load-kif-forms (forms &key verbose print phases)
  (labels
    ((load-kif-forms0 ()
       (let ((*package* (find-package :snark))
             (*%use-kif-version%* *%use-kif-version%*)
	     (*form-author* nil)
	     (*form-documentation* nil)
	     (*form-name* nil)
	     (*form-source* nil))
         (dolist (form forms)
           (let ((defn (kif-definition-p form)))
             (when (and print defn)
               (format t "~%;Evaluating ~A ~S~@[ ~A~]..."
                       (first form) (second form) *load-kif-file-phase*))
             (let ((value (load-kif-eval form)))
               (when (and print (not defn))
                 (fresh-line)
                 (prin1 value)))))))
     (load-kif-forms1 (phase string)
       (when verbose
         (format t string))
       (let ((*load-kif-file-phase* phase))
         (load-kif-forms0))))
    (cond
     (phases
      (load-kif-forms1 :sorts   "~2%;Extracting sort information...")
      (load-kif-forms1 :symbols "~2%;Extracting symbol information...")
      (load-kif-forms1 :wffs    "~2%;Extracting assertions..."))
     (t
      (load-kif-forms0)))))

(defun write-kif-file (filespec forms *package* language)
  (let ((*print-pretty* t))
    (with-open-file (stream filespec
			    :direction :output)
      (print `(in-package ,(package-name *package*)) stream)
      (terpri stream)
      (print `(in-language ,language) stream)
      (terpri stream)
      (dolist (form forms)
	(when (and (consp form) (eq 'in-package (first form)))
	  (eval form))
	(print form stream)
	(terpri stream)))))

(defun kif-def-contains-def (x y)
  (and (eq (first x) (first y))
       (eql (second x) (second y))
       (subsetp (cddr y) (cddr x) :test #'equal)
       (not (subsetp (cddr x) (cddr y) :test #'equal))))

(defun kif-def-must-precede-def (x y)
  (and (kif-definition-p x)
       (constant-occurs-p (second x) y nil)))

(defun reorder-kif-forms (forms)
  (setq forms (delete-duplicates forms :test #'equal))
  (setq forms (remove-if (lambda (y)
                           (some (lambda (x) (kif-def-contains-def x y)) forms))
			 forms))
  (setq forms (reverse forms))	;preserves order better
  (setq forms (topological-sort forms #'kif-def-must-precede-def)))

(defun reorder-kif-file (filespec)
  (mvlet (((:values forms package language) (read-kif-file filespec)))
    (setq forms (reorder-kif-forms forms))
    (write-kif-file (concatenate 'string filespec ".new") forms package language)))

(defun anti-symmetric-binary-predicate-wff (p)
  `(forall (?x ?y) (implies (and (,p ?x ?y) (,p ?y ?x)) (= ?x ?y))))

(defun anti-transitive-binary-predicate-wff (p)
  `(forall (?x ?y ?z) (not (and (,p ?x ?y) (,p ?y ?z) (,p ?x ?z)))))

(defun asymmetric-binary-predicate-wff (p)
  `(forall (?x ?y) (implies (,p ?x ?y) (not (,p ?y ?x)))))

(defun irreflexive-binary-predicate-wff (p)
  `(forall (?x) (not (,p ?x ?x))))

(defun reflexive-binary-predicate-wff (p)
  `(forall (?x) (,p ?x ?x)))

(defun symmetric-binary-predicate-wff (p)
  `(forall (?x ?y) (implies (,p ?x ?y) (,p ?y ?x))))

(defun transitive-binary-predicate-wff (p)
  `(forall (?x ?y ?z) (implies (and (,p ?x ?y) (,p ?y ?z)) (,p ?x ?z))))

(defun kif-test1 ()
  (initialize)
;;(trace kif-defobject declare-constant assert)
  (defobject c1 "c1" := c)
  (defobject c1      := c)
  (defobject c2 "c2" :conservative-axiom (= c2 c))
  (defobject c2      :conservative-axiom (= c2 c))
  (defobject c3 "c3" :-> ?x :=> (evenp ?x))
  (defobject c3      :-> ?x :=> (evenp ?x))
  (defobject c4 "c4" :-> ?x :<= (evenp ?x))
  (defobject c4      :-> ?x :<= (evenp ?x))
  (defobject c5 "c5" (evenp c5) (plusp c5))
  (defobject c5      (evenp c5) (plusp c5))
  nil)

(defun kif-test2 ()
  (initialize)
;;(trace kif-deffunction declare-function assert)
  (deffunction f1 (?x) "f1" := (g ?x))
  (deffunction f1 (?x)      := (g ?x))
  (deffunction f2 (?x) "f2" :-> ?y :=> (p ?x ?y))
  (deffunction f2 (?x)      :-> ?y :=> (p ?x ?y))
  (deffunction f3 (?x) "f3" :-> ?y :<= (p ?x ?y))
  (deffunction f3 (?x)      :-> ?y :<= (p ?x ?y))
  (deffunction f4 "f4" :conservative-axiom (q (f4 ?x ?x)))
  (deffunction f4      :conservative-axiom (q (f4 ?x ?x)))
  (deffunction f5 "f5" (evenp (f5 ?x)) (plusp (f5 ?x)))
  (deffunction f5      (evenp (f5 ?x)) (plusp (f5 ?x)))
  )

(defun kif-test3 ()
  (initialize)
;;(trace kif-defrelation declare-relation assert)
  (defrelation r1 (?x) "r1" := (s ?x))
  (defrelation r1 (?x)      := (s ?x))
  (defrelation r2 (?x) "r2" :<= (s ?x))
  (defrelation r2 (?x)      :<= (s ?x))
  (defrelation r3 (?x) "r3" :=> (s ?x))
  (defrelation r3 (?x)      :=> (s ?x))
  (defrelation r4 (?x) "r4" :=> (s ?x) :axiom (r4 a))
  (defrelation r4 (?x)      :=> (s ?x) :axiom (r4 a))
  (defrelation r5 (?x) "r5" :=> (s ?x) :conservative-axiom (r5 a))
  (defrelation r5 (?x)      :=> (s ?x) :conservative-axiom (r5 a))
  (defrelation r6 "r6" :conservative-axiom (r6 a))
  (defrelation r6      :conservative-axiom (r6 a))
  (defrelation r7 "r7" (r7 a) (r7 b))
  (defrelation r7      (r7 a) (r7 b)))

;;; kif.lisp EOF
