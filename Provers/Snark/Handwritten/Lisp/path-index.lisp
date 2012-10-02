;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: path-index.lisp
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

(declaim (special *terpri-indent*))

(defvar *path-index*)
(defvar *default-path-index-delete-empty-nodes* t)
(defvar *default-path-index-size* 50000)
(defvar *default-path-index-alist-length-limit* 50)
(declaim (type integer *default-path-index-size*)
         (type fixnum *default-path-index-alist-length-limit*))

(defstruct (path-index
	     (:constructor make-path-index0
                           (entry-constructor delete-empty-nodes alist-length-limit entries))
	     (:copier nil))
  (top-node (make-path-index-internal-node1 :mark nil) :read-only t)
  (entries nil :read-only t)			;term->entry hash-table for entry lookup
  (entry-constructor nil :read-only t)		;term->entry function for new entry insertion
  (delete-empty-nodes nil :read-only t)
  (alist-length-limit nil :read-only t)
  (node-counter (make-counter 1))
  (entry-counter (make-counter)))

(defstruct (path-index-node
	     (:copier nil))
  (parent-node nil :read-only t)
  (mark (increment-counter (path-index-node-counter *path-index*))))

(defstruct (path-index-internal-node1
            (:include path-index-node)
            (:copier nil))
  (variable-child-node nil)			;nil or internal-node
  (constant-indexed-child-nodes (make-sparse-vector))	;alist of (constant . leaf-node) pairs
  (function-indexed-child-nodes (make-sparse-vector)))	;alist of (function . internal-node) pairs

(defstruct (path-index-internal-node2
	     (:include path-index-node)
	     (:copier nil))
  (integer-indexed-child-nodes nil :read-only t)	;vector of internal-nodes (or nil) indexed by argument position
  query)					;node in integer-indexed-child-nodes to use to generate all instances

(defstruct (path-index-leaf-node
	     (:include path-index-node)
	     (:copier nil))
  (entries (make-sparse-vector) :read-only t))

(defstruct (path-index-entry
	     (:constructor make-path-index-entry (term))
	     (:copier nil))
  (term nil :read-only t)
  in-nodes					;vector of (possible query) nodes that contain entry
  in-nodes-last					;last index into in-nodes
  (mark nil))

(defun make-path-index (&key
			(entry-constructor #'make-path-index-entry)
			(delete-empty-nodes *default-path-index-delete-empty-nodes*)
                        (alist-length-limit *default-path-index-alist-length-limit*)
			(size *default-path-index-size*))
  (declare (ignorable size))
  (setq *path-index* (make-path-index0
                      entry-constructor
                      delete-empty-nodes
                      alist-length-limit
                      (make-sparse-vector))))

(defmacro path-index-internal-node1-function-indexed-child-node (head node1)
  `(sparef (path-index-internal-node1-function-indexed-child-nodes ,node1) (function-number ,head)))

(defmacro path-index-internal-node1-constant-indexed-child-node (const node1)
  `(sparef (path-index-internal-node1-constant-indexed-child-nodes ,node1) (constant-number ,const)))

(defmacro add-path-index-internal-node1-function-indexed-child-node (head node1 node)
  `(setf (path-index-internal-node1-function-indexed-child-node ,head ,node1) ,node))

(defmacro add-path-index-internal-node1-constant-indexed-child-node (const node1 node)
  `(setf (path-index-internal-node1-constant-indexed-child-node ,const ,node1) ,node))

(defun path-index-entry (term)
  ;; return path-index-entry for term
  ;; create one if there isn't one
  (let ((term# (funcall *standard-eql-numbering* :lookup term)))
    (or (sparef (path-index-entries *path-index*) term#)
        (path-index-insert term))))

(defun the-path-index-entry (term)
  ;; return path-index-entry for term
  ;; error if there isn't one
  (let ((term# (funcall *standard-eql-numbering* :lookup term)))
    (or (sparef (path-index-entries *path-index*) term#)
        (progn
	  (cl:assert (eql term (hash-term term)))
	  (error "No path-index-entry for term.")))))

(defun some-path-index-entry (term)
  ;; return path-index-entry for term
  ;; return nil if there isn't one
  (let ((term# (funcall *standard-eql-numbering* :lookup term)))
    (or (sparef (path-index-entries *path-index*) term#)
        (progn
	  #+ignore (cl:assert (eql term (hash-term term)))
	  nil))))

(defun path-index-delete (term)
  (let* ((path-index *path-index*)
         (term# (funcall *standard-eql-numbering* :lookup term))
	 (entry (or (sparef (path-index-entries path-index) term#)
		    (progn
		      #+ignore (cl:assert (eql term (hash-term term)))
		      nil))))
    (when entry
      (every (if (not (path-index-delete-empty-nodes path-index))
	         (lambda (node)
                   (when (path-index-leaf-node-p node)
                     (setf (sparef (path-index-leaf-node-entries node) (tme-number entry)) nil))
                   t)
	         (lambda (node)
                   (when (path-index-leaf-node-p node)
                     (let ((entries (path-index-leaf-node-entries node)))
                       (setf (sparef entries (tme-number entry)) nil)
                       (when (eql 0 (sparse-vector-count entries))
                         (path-index-delete-leaf-node node))))
                   t))
             (path-index-entry-in-nodes entry))
      (setf (sparef (path-index-entries path-index) term#) nil)
      (decrement-counter (path-index-entry-counter path-index)))
    entry))

(defun path-index-delete-leaf-node (node)
  (let ((path-index *path-index*)
	(parent (path-index-node-parent-node node)))
    (cond
      ((eq node (path-index-internal-node1-variable-child-node parent))
       (setf (path-index-internal-node1-variable-child-node parent) nil))
      (t
       (let ((table (path-index-internal-node1-constant-indexed-child-nodes parent)))
         (map-sparse-vector-with-indexes
          (lambda (value key)
            (when (eq node value)
              (setf (sparef table key) nil)))
          table))))
    (decrement-counter (path-index-node-counter path-index))))

(defvar *path-index-insert-entry*)
(defvar *path-index-insert-entry-leaf-nodes*)
(defvar *path-index-insert-entry-internal-nodes*)

(defun path-index-insert (term)
  #+ignore (cl:assert (eql term (hash-term term)))
  (let* ((path-index *path-index*)
	 (entry (funcall (path-index-entry-constructor path-index) term)))
    (increment-counter (path-index-entry-counter path-index))
    (let ((term# (funcall *standard-eql-numbering* :lookup term)))
      (setf (sparef (path-index-entries path-index) term#) entry))
    (let ((*path-index-insert-entry* entry)
	  (*path-index-insert-entry-leaf-nodes* nil)
	  (*path-index-insert-entry-internal-nodes* nil))
      ;; FOR EMBEDDINGS
      (WHEN (COMPOUND-P TERM)
	(LET ((HEAD (HEAD TERM)))
	  (WHEN (FUNCTION-ASSOCIATIVE HEAD)
	    (SETQ TERM (MAKE-COMPOUND* HEAD (MAKE-VARIABLE) (ARGS TERM))))))
      (path-index-insert* term (path-index-top-node path-index))
      (let* ((l (nconc *path-index-insert-entry-internal-nodes* *path-index-insert-entry-leaf-nodes*))
             (n (length l)))
        (setf (path-index-entry-in-nodes entry) (make-array n :initial-contents l))
        (setf (path-index-entry-in-nodes-last entry) (1- n))))
    entry))

(defun path-index-insert* (term node1 &optional head-if-associative)
  ;; find or create paths for term so that term can be inserted in path-index
  (dereference
    term nil
    :if-variable (let ((leaf (path-index-internal-node1-variable-child-node node1)))
		   (unless leaf
		     (setq leaf (make-path-index-leaf-node :parent-node node1))
		     (setf (path-index-internal-node1-variable-child-node node1) leaf))
		   (path-index-insert-at-leaf leaf))
    :if-constant (let ((leaf (path-index-internal-node1-constant-indexed-child-node term node1)))
		   (unless leaf
		     (setq leaf (make-path-index-leaf-node :parent-node node1))
		     (add-path-index-internal-node1-constant-indexed-child-node term node1 leaf))
		   (path-index-insert-at-leaf leaf))
    :if-compound (let ((args (args term)))
		   (if args
		       (path-index-insert-appl (head term) args node1 head-if-associative)
		       (PATH-INDEX-INSERT* (FUNCTION-NAME (HEAD TERM)) NODE1 HEAD-IF-ASSOCIATIVE)))))	;handle 0-ary as constant

(defun path-index-insert-appl (head args node1 head-if-associative)
  (cond
    ((eq head-if-associative head)
     (dolist (arg args)
       (path-index-insert* arg node1 head-if-associative)))
    ((no-integer-indexed-child-nodes-p head)
     (let ((node1a (path-index-internal-node1-function-indexed-child-node head node1)))
       (unless node1a
	 (setq node1a (make-path-index-internal-node1 :parent-node node1))
	 (add-path-index-internal-node1-function-indexed-child-node head node1 node1a))
       (let ((l *path-index-insert-entry-internal-nodes*))
	 (unless (member node1a l)
	   (setq *path-index-insert-entry-internal-nodes* (cons node1a l))))
       (ecase (function-index-type head)
         (:jepd
          (path-index-insert* (first args) node1a)
          (path-index-insert* (second args) node1a))
         ((nil)
          (case (function-arity head)
            ((:alist :plist)
             (dolist (arg (path-index-alist-args (first args) nil))
               (path-index-insert* arg node1a)))
            (otherwise
             (let ((head-if-associative (and (function-associative head) head)))
               (dolist (arg args)
                 (path-index-insert* arg node1a head-if-associative)))))))))
    ((function-commutative head)
     (path-index-insert-list head args node1 #'c-index))
    ((function-permutations head)
     (path-index-insert-list head args node1 #'p-index))
    (t
     (path-index-insert-list head args node1))))

(defun path-index-insert-list (head args node1 &optional indexfun)
  (loop with node2 = (path-index-insert-list1 head (length args) node1 indexfun)
	with iinodes = (path-index-internal-node2-integer-indexed-child-nodes node2)
        for arg in args
        as i from 0
        do (path-index-insert* arg (svref iinodes (if indexfun (funcall indexfun head i) i)))))

(defun path-index-insert-list1 (head arity node1 indexfun)
  (let ((node2 (path-index-internal-node1-function-indexed-child-node head node1)))
    (unless node2
      (let ((iinodes (make-array arity :initial-element nil)))
	(setq node2 (make-path-index-internal-node2 :parent-node node1 :integer-indexed-child-nodes iinodes))
	(dotimes (i arity)
	  (let ((i* (if indexfun (funcall indexfun head i) i)))
	    (unless (svref iinodes i*)
	      (setf (svref iinodes i*) (make-path-index-internal-node1 :parent-node node2)))))
	(loop for i downfrom (1- arity)
	      as v = (svref iinodes i)
	      do (when v
		   (setf (path-index-internal-node2-query node2) v)
		   (return))))
      (add-path-index-internal-node1-function-indexed-child-node head node1 node2))
    (let ((l *path-index-insert-entry-internal-nodes*)
	  (n (path-index-internal-node2-query node2)))
      (unless (member n l)
	(setq *path-index-insert-entry-internal-nodes* (cons n l))))
    node2))

(defun path-index-insert-at-leaf (leaf)
  (let ((entry *path-index-insert-entry*)
	(entries (path-index-leaf-node-entries leaf)))
    (let ((num (tme-number entry)))
      (unless (sparef entries num)
        (push leaf *path-index-insert-entry-leaf-nodes*)
        (setf (sparef entries num) entry)))))

(defun no-integer-indexed-child-nodes-p (head)
  (ecase (function-index-type head)
    (:jepd
     t)
    ((nil)
     (let ((arity (function-arity head)))
       (or (eql 1 arity)
           (and (eql 2 arity)
                (function-commutative head))
           (function-associative head)
           (eq :any arity)
           (eq :alist arity)
           (eq :plist arity)
           (and (function-permutations head)
                (every #'zerop (function-permutations-min head))))))))

(defun c-index (head i)
  (declare (ignore head))
  (if (= 1 i) 0 i))

(defun p-index (head i)
  (nth i (function-permutations-min head)))

(defun path-index-alist-args (alist subst)
  (dereference
   alist subst
   :if-variable (list alist)
   :if-constant nil
   :if-compound (lcons (first alist)
                       (path-index-alist-args (rest alist) subst)
                       alist)))

(defmacro path-index-variable-leaf (node1)
  `(let ((v (path-index-internal-node1-variable-child-node ,node1)))
     (and v
	  (neql 0 (sparse-vector-count (path-index-leaf-node-entries v)))
	  v)))

(defmacro path-index-constant-leaf (node1 const)
  `(let ((v (path-index-internal-node1-constant-indexed-child-node ,const ,node1)))
     (and v
	  (neql 0 (sparse-vector-count (path-index-leaf-node-entries v)))
	  v)))

(defun make-path-index-query (type term &optional subst)
  (let ((query
	  (ecase type
	    (:generalization
	      (make-path-index-query-g term subst (path-index-top-node *path-index*)))
	    (:instance
	      (make-path-index-query-i term subst (path-index-top-node *path-index*)))
	    (:unifiable
	      (make-path-index-query-u term subst (path-index-top-node *path-index*)))
	    (:variant
	      (make-path-index-query-v term subst (path-index-top-node *path-index*))))))
    #+ignore
    (progn
      (terpri-comment-indent)
      (print-term term subst)
      (format t " ~(~A~) query:" type)
      (print-path-index-query query)
      (terpri))
    query))

(defun make-path-index-query-v (term subst node1 &optional head-if-associative)
  (dereference
    term subst
    :if-variable (path-index-variable-leaf node1)
    :if-constant (path-index-constant-leaf node1 term)
    :if-compound (let ((args (args term)))
		   (if args
		       (make-path-index-query-appl #'make-path-index-query-v (head term) args subst node1 head-if-associative)
		       (MAKE-PATH-INDEX-QUERY-V (FUNCTION-NAME (HEAD TERM)) SUBST NODE1 HEAD-IF-ASSOCIATIVE)))))	;handle 0-ary as constant

(defun make-path-index-query-i (term subst node1 &optional head-if-associative)
  (dereference
    term subst
    :if-variable t
    :if-constant (path-index-constant-leaf node1 term)
    :if-compound (let ((args (args term)))
		   (if args
		       (make-path-index-query-appl #'make-path-index-query-i (head term) args subst node1 head-if-associative)
		       (MAKE-PATH-INDEX-QUERY-I (FUNCTION-NAME (HEAD TERM)) SUBST NODE1 HEAD-IF-ASSOCIATIVE)))))	;handle 0-ary as constant

(defun make-path-index-query-g (term subst node1 &optional head-if-associative)
  (dereference
    term subst
    :if-variable (path-index-variable-leaf node1)
    :if-constant (make-uniond-query2
		   (path-index-constant-leaf node1 term)
		   (path-index-variable-leaf node1))
    :if-compound (let ((args (args term)))
		   (if args
		       (make-uniond-query2
			 (make-path-index-query-appl #'make-path-index-query-g (head term) args subst node1 head-if-associative)
			 (path-index-variable-leaf node1))
		       (MAKE-PATH-INDEX-QUERY-G (FUNCTION-NAME (HEAD TERM)) SUBST NODE1 HEAD-IF-ASSOCIATIVE)))))	;handle 0-ary as constant

(defun make-path-index-query-u (term subst node1 &optional head-if-associative)
  (dereference
    term subst
    :if-variable t
    :if-constant (make-uniond-query2
		   (path-index-constant-leaf node1 term)
		   (path-index-variable-leaf node1))
    :if-compound (let ((args (args term)))
		   (if args
		       (make-uniond-query2
			 (make-path-index-query-appl #'make-path-index-query-u (head term) args subst node1 head-if-associative)
			 (path-index-variable-leaf node1))
		       (MAKE-PATH-INDEX-QUERY-U (FUNCTION-NAME (HEAD TERM)) SUBST NODE1 HEAD-IF-ASSOCIATIVE)))))	;handle 0-ary as constant

(defun make-path-index-query-appl (make-query head args subst node1 head-if-associative)
  (cond
    ((eq head-if-associative head)
     (let ((v (let ((qq nil) qq-last)
		(dolist (arg args)
		  (let ((q (funcall make-query arg subst node1 head-if-associative)))
		    (cond
		      ((null q)
		       (return-from make-path-index-query-appl nil))
		      ((neq t q)
		       (collect q qq)))))
		(make-boolean-query 'intersection qq))))
       (if (eq t v) node1 v)))
    ((no-integer-indexed-child-nodes-p head)
     (let ((node1a (path-index-internal-node1-function-indexed-child-node head node1)))
       (and node1a
	    (let ((v (let ((qq nil) qq-last)
                       (ecase (function-index-type head)
                         (:jepd
                          (dolist (arg (firstn args 2))
                            (let ((q (funcall make-query arg subst node1a)))
                              (cond
                               ((null q)
                                (return-from make-path-index-query-appl nil))
                               ((neq t q)
                                (collect q qq))))))
                         ((nil)
		          (case (function-arity head)
                            ((:alist :plist)
			     (dolist (arg (path-index-alist-args (first args) subst))
			       (let ((q (funcall make-query arg subst node1a)))
			         (cond
				  ((null q)
				   (return-from make-path-index-query-appl nil))
				  ((neq t q)
				   (collect q qq))))))
			    (otherwise
			     (let ((head-if-associative (and (function-associative head) head)))
			       (dolist (arg args)
			         (let ((q (funcall make-query arg subst node1a head-if-associative)))
				   (cond
				    ((null q)
				     (return-from make-path-index-query-appl nil))
				    ((neq t q)
				     (collect q qq))))))))))
		       (make-boolean-query 'intersection qq))))
	      (if (eq t v) node1a v)))))
    ((function-commutative head)
     (make-path-index-query-list make-query head args subst node1 #'c-index))
    ((function-permutations head)
     (make-path-index-query-list make-query head args subst node1 #'p-index))
    (t
     (make-path-index-query-list make-query head args subst node1))))

(defun make-path-index-query-list (make-query head args subst node1 &optional indexfun)
  (let ((node2 (path-index-internal-node1-function-indexed-child-node head node1)))
    (and node2
	 (let ((v (make-boolean-query
                   'intersection
		    (loop with iinodes = (path-index-internal-node2-integer-indexed-child-nodes node2)
			  for arg in args
			  as i from 0
			  as q = (funcall make-query arg subst (svref iinodes (if indexfun (funcall indexfun head i) i)))
			  when (null q)
			    do (return-from make-path-index-query-list nil)
                          unless (eq t q)
			    collect q))))
	   (if (eq t v) (path-index-internal-node2-query node2) v)))))

(defmacro map-leaf0 (leaf x &optional y)
  `(prog->
     (map-sparse-vector (path-index-leaf-node-entries ,leaf) ->* entry)
     (cond
      ((eq query-id (path-index-entry-mark entry))
       )
      ,@(when y (list y))
      ((or (null queries) (path-index-entry-satisfies-query-p entry (first queries) (rest queries)))
       ,x
       (setf (path-index-entry-mark entry) query-id)))))

(defmacro map-leaf (leaf)
  `(if retrieve-entries
       (if (null test)
	   (map-leaf0 ,leaf (funcall cc entry))
	   (map-leaf0 ,leaf (funcall cc entry test-value)
		      ((null (setq test-value (funcall test entry)))
		       (setf (path-index-entry-mark entry) query-id))))
       (if (null test)
	   (map-leaf0 ,leaf (funcall cc (path-index-entry-term entry)))
	   (map-leaf0 ,leaf (funcall cc (path-index-entry-term entry) test-value)
		      ((null (setq test-value (funcall test entry)))
		       (setf (path-index-entry-mark entry) query-id))))))

;;; test is a predicate applied to a path-index-entry before path-index
;;; query evaluation is complete to quickly determine whether the
;;; path-index-entry should be retrieved if it satisfies the query
;;; the result of test is also passed as second argument to cc

(defun map-path-index-entries (cc type term &optional subst test query-id)
  (let ((query (make-path-index-query type term subst)))
    (when query
      (map-path-index-by-query cc query test t query-id))))

(defun map-path-index (cc type term &optional subst test retrieve-entries query-id)
  (let ((query (make-path-index-query type term subst)))
    (when query
      (map-path-index-by-query cc query test retrieve-entries query-id))))

(defun map-path-index-entries-by-query (cc query &optional test query-id)
  (map-path-index-by-query cc query test t query-id))

(defun map-path-index-by-query (cc query &optional test retrieve-entries query-id)
  (let ((optimized nil))
    (cond
     ((test-option14?)
      (when (sparse-vector-expression-p query)
        (setf query (if (trace-optimize-sparse-vector-expression?)
                        (mes::traced-optimize-sparse-vector-expression query)
                        (optimize-sparse-vector-expression query)))
        (if test
            (let (test-value)
              (flet ((filter (entry) (setf test-value (funcall test entry))))
                (declare (dynamic-extent #'filter))
                (if retrieve-entries
                    (prog->
                      (map-sparse-vector-expression query :reverse t :filter #'filter ->* entry)
                      (funcall cc entry test-value))
                    (prog->
                      (map-sparse-vector-expression query :reverse t :filter #'filter ->* entry)
                      (funcall cc (path-index-entry-term entry) test-value)))))
            (if retrieve-entries
                (prog->
                  (map-sparse-vector-expression query :reverse t ->* entry)
                  (funcall cc entry))
                (prog->
                  (map-sparse-vector-expression query :reverse t ->* entry)
                  (funcall cc (path-index-entry-term entry)))))
        (return-from map-path-index-by-query))))
    (unless query-id
      (setq query-id (cons 'query-id nil)))	;query-id unique, eq testable
    (let (test-value)
      (labels
        ((map-path-index-by-query* (query queries)
	   (loop
	     (cond
              ((not (consp query))
               (cond
                ((path-index-leaf-node-p query)
                 (map-leaf query)
                 (return))
                (t
                 (when (path-index-internal-node2-p query)
                   (setq query (path-index-internal-node2-query query)))
                 (map-sparse-vector
                  (lambda (v) (map-leaf v))
                  (path-index-internal-node1-constant-indexed-child-nodes query)
                  :reverse t)
                 (let ((var-leaf (path-index-internal-node1-variable-child-node query)))
                   (when var-leaf
                     (map-leaf var-leaf)))
                 (let ((q nil))
                   (map-sparse-vector
                    (lambda (v)
                      (when q
                        (map-path-index-by-query* q queries))
                      (setq q v))
                    (path-index-internal-node1-function-indexed-child-nodes query)
                    :reverse t)
                   (if q
                       (setq query q)
                       (return))))))
              ((eq 'intersection (first query))
               (dolist (q (prog1 (setq query (rest query))
                            (setq query (if optimized (first query) (select-query query)))))
                 (unless (eq q query)
                   (push q queries))))
              (t
;;             (cl:assert (member (first query) '(union uniond)))
               (do* ((l (rest query) l1)
                     (l1 (rest l) (rest l1)))
                    ((null l1)
                     (setq query (first l)))
                 (map-path-index-by-query* (first l) queries)))))))
        #+ignore (cl:assert query)
        (when (eq t query)
	  (setq query (path-index-top-node *path-index*)))
        (map-path-index-by-query* query nil)))))

(defmacro mark-path-index-entry-in-nodes (entry)
  (cl:assert (symbolp entry))
  (let ((v (gensym)) (i (gensym)))
    `(let ((,v (path-index-entry-in-nodes ,entry))
           (,i (path-index-entry-in-nodes-last ,entry)))
       (declare (type vector ,v) (type fixnum ,i))
       (loop
         (setf (path-index-node-mark (svref ,v ,i)) ,entry)
         (if (eql 0 ,i)
             (return)
             (decf ,i))))))

(defmacro member-path-index-entry-in-nodes (query entry)
  (cl:assert (symbolp query))
  (cl:assert (symbolp entry))
  (let ((v (gensym)) (i (gensym)))
    `(let ((,v (path-index-entry-in-nodes ,entry))
           (,i (path-index-entry-in-nodes-last ,entry)))
       (declare (type vector ,v) (type fixnum ,i))
       (loop
         (when (eq (svref ,v ,i) ,query)
           (return t))
         (if (eql 0 ,i)
             (return nil)
             (decf ,i))))))

(defun path-index-entry-satisfies-query-p (entry query &optional more-queries)
  (cond
    (more-queries
     (mark-path-index-entry-in-nodes entry)
     (and (path-index-entry-satisfies-query-p* entry query)
	  (path-index-entry-satisfies-query-p* entry (first more-queries))
	  (dolist (query (rest more-queries) t)
	    (unless (path-index-entry-satisfies-query-p* entry query)
	      (return nil)))))
    ((consp query)
     (mark-path-index-entry-in-nodes entry)
     (path-index-entry-satisfies-query-p* entry query))
    (t
     (member-path-index-entry-in-nodes query entry))))

(defun path-index-entry-satisfies-query-p* (entry query)
  (loop
    (cond
      ((not (consp query))			;query is a node
       (return-from path-index-entry-satisfies-query-p*
	 (eq (path-index-node-mark query) entry)))
      ((eq 'intersection (first query))		;intersection
       (do* ((l (rest query) l1)
	     (l1 (rest l) (rest l1)))
	    ((null l1)
	     (setq query (first l)))
	 (unless (path-index-entry-satisfies-query-p* entry (first l))
	   (return-from path-index-entry-satisfies-query-p*
	     nil))))
      (t
;;     (cl:assert (member (first query) '(union uniond)))
       (do* ((l (rest query) l1)
	     (l1 (rest l) (rest l1)))
	    ((null l1)
	     (setq query (first l)))
	 (when (path-index-entry-satisfies-query-p* entry (first l))
	   (return-from path-index-entry-satisfies-query-p*
	     t)))))))

(defun retrieval-size (query bound)
  (cond
    ((not (consp query))
     (cond
       ((path-index-leaf-node-p query)
	(sparse-vector-count (path-index-leaf-node-entries query)))
       (t
	(when (path-index-internal-node2-p query)
	  (setq query (path-index-internal-node2-query query)))
	(let ((total-size 0))
	  (let ((var-leaf (path-index-internal-node1-variable-child-node query)))
	    (when var-leaf
	      (incf total-size (sparse-vector-count (path-index-leaf-node-entries var-leaf)))
	      (when (>= total-size bound)
		(return-from retrieval-size bound))))
          (map-sparse-vector
           (lambda (v)
             (incf total-size (sparse-vector-count (path-index-leaf-node-entries v)))
             (when (>= total-size bound)
               (return-from retrieval-size bound)))
           (path-index-internal-node1-constant-indexed-child-nodes query))
          (map-sparse-vector
           (lambda (v)
             (incf total-size (retrieval-size v (- bound total-size)))
             (when (>= total-size bound)
               (return-from retrieval-size bound)))
           (path-index-internal-node1-function-indexed-child-nodes query))
	  total-size))))
    ((eq 'intersection (first query))
     (let* ((args (rest query))
	    (min-size (retrieval-size (first args) bound)))
       (dolist (arg (rest args))
	 (let ((n (retrieval-size arg min-size)))
	   (when (< n min-size)
	     (when (<= (setq min-size n) 1)
	       (return)))))
       min-size))
    (t
;;   (cl:assert (member (first query) '(union uniond)))
     (let ((total-size 0))
       (dolist (arg (rest query))
	 (incf total-size (retrieval-size arg (- bound total-size)))
	 (when (>= total-size bound)
	   (return-from retrieval-size bound)))
       total-size))))

(defun select-query (args)
  (let* ((best (first args))
	 (min-size (retrieval-size best 1000000)))
    (dolist (arg (rest args))
      (let ((n (retrieval-size arg min-size)))
	(when (< n min-size)
	  (setq best arg)
	  (when (<= (setq min-size n) 1)
	    (return)))))
    best))

(defun make-boolean-query* (fn l)
  (let ((a (first l)) 
	(d (rest l)))
    (if (null d)
	(if (and (consp a) (eq fn (first a)))
	    (rest a)
	    l)
	(let ((d* (make-boolean-query* fn d)))
	  (cond
	    ((and (consp a) (eq fn (first a)))
	     (nodup-append (rest a) d*))
	    ((equal a (first d*))
	     d*)
	    ((member a (rest d*) :test #'equal)
	     (cons a (cons (first d*) (remove a (rest d*) :test #'equal))))
	    ((eq d d*)
	     l)
	    (t
	     (cons a d*)))))))

(defun make-boolean-query (fn l)
  (cond
   ((null l)
    (ecase fn
      (intersection
       t)
      ((union uniond)
       nil)))
   (t
    (let ((l* (make-boolean-query* fn l)))
      (cond
       ((null (rest l*))
        (first l*))
       (t
        (cons fn l*)))))))

(defun make-uniond-query2 (q1 q2)
  (cond
   ((null q1)
    q2)
   ((null q2)
    q1)
   (t
    (make-boolean-query 'uniond (list q1 q2)))))

(defun nodup-append (l1 l2 &optional (l2* nil))
  ;; append l1 and l2 eliminating items in l2 that appear in l1
  (if (null l2)
      (if (null l2*)
	  l1
	  (append l1 (nreverse l2*)))
      (nodup-append l1
		    (rest l2)
		    (if (member (first l2) l1 :test #'equal)
			l2*
			(cons (first l2) l2*)))))

(defun print-path-index (&key terms nodes)
  (let ((path-index *path-index*))
    (terpri-comment-indent)
    (mvlet (((:values current peak added deleted) (counter-values (path-index-entry-counter path-index))))
      (format t "Path-index has ~D entries (~D at peak, ~D added, ~D deleted)."
	      current peak added deleted))
    (terpri-comment-indent)
    (mvlet (((:values current peak added deleted) (counter-values (path-index-node-counter path-index))))
      (format t "Path-index has ~D nodes (~D at peak, ~D added, ~D deleted)."
	      current peak added deleted))
    (when (or nodes terms)
      (print-path-index* (path-index-top-node path-index) nil terms))))

(defun print-path-index* (node revpath print-terms)
  (etypecase node
    (path-index-internal-node1
      (let ((v (path-index-internal-node1-variable-child-node node)))
        (when v
          (print-path-index* v (cons "variable" revpath) print-terms)))
      (map-sparse-vector-with-indexes
       (lambda (v k)
         (print-path-index* v (cons (constant-numbered k) revpath) print-terms))
       (path-index-internal-node1-constant-indexed-child-nodes node)
       :reverse t)
      (map-sparse-vector-with-indexes
       (lambda (v k)
         (print-path-index* v (cons (function-numbered k) revpath) print-terms))
       (path-index-internal-node1-function-indexed-child-nodes node)
       :reverse t))
    (path-index-internal-node2
      (let ((iinodes (path-index-internal-node2-integer-indexed-child-nodes node)))
	(dotimes (i (array-dimension iinodes 0))
	  (let ((v (svref iinodes i)))
	    (when v
	      (print-path-index* v (cons i revpath) print-terms))))))
    (path-index-leaf-node
      (terpri-comment-indent)
      (princ "Path ")
      (print-revpath revpath)
      (princ " has ")
      (princ (sparse-vector-count (path-index-leaf-node-entries node)))
      (princ " entries.")
      (when print-terms
	(prog->
	  (map-sparse-vector (path-index-leaf-node-entries node) ->* entry)
	  (terpri-comment-indent)
	  (princ "   ")
	  (print-term (path-index-entry-term entry)))))))

(defun print-revpath (revpath)
  (princ "[")
  (dolist (x (reverse (rest revpath)))
    (cond
      ((function-symbol-p x)
       (prin1 x))
      (t
       (cl:assert (integerp x))
       (cond
	 ((< x 0)
	  (princ "list")
	  (princ (- x)))
	 (t
	  (princ "arg")
	  (princ (1+ x))))))
    (princ ","))
  (prin1 (first revpath) *standard-output*)
  (princ "]"))

(defun path-index-key-for-value (value table)
  (map-sparse-vector-with-indexes
   (lambda (v k)
     (when (eq value v)
       (return-from path-index-key-for-value (symbol-numbered k))))
   table))

(defun path-index-node-revpath (node)
  (let ((parent-node (path-index-node-parent-node node)))
    (cond
      ((path-index-internal-node1-p parent-node)
       (cons (or (if (eq node (path-index-internal-node1-variable-child-node parent-node)) "variable" nil)
		 (path-index-key-for-value node (path-index-internal-node1-function-indexed-child-nodes parent-node))
		 (path-index-key-for-value node (path-index-internal-node1-constant-indexed-child-nodes parent-node)))
	     (path-index-node-revpath parent-node)))
      ((path-index-internal-node2-p parent-node)
       (cons (position node (path-index-internal-node2-integer-indexed-child-nodes parent-node))
	     (path-index-node-revpath parent-node)))
      (t
       nil))))

(defun print-path-index-query (query &key terms)
  (cond
    ((or (null query) (eq t query))
     (terpri-comment-indent)
     (princ query))
    ((and (consp query) (eq 'intersection (first query)))
     (terpri-comment-indent)
     (princ "(intersection")
     (let ((*terpri-indent* (+ *terpri-indent* 3)))
       (mapc (lambda (q) (print-path-index-query q :terms terms)) (rest query)))
     (princ ")"))
    ((and (consp query) (eq 'union (first query)))
     (terpri-comment-indent)
     (princ "(union")
     (let ((*terpri-indent* (+ *terpri-indent* 3)))
       (mapc (lambda (q) (print-path-index-query q :terms terms)) (rest query)))
     (princ ")"))
    ((and (consp query) (eq 'uniond (first query)))
     (terpri-comment-indent)
     (princ "(uniond")
     (let ((*terpri-indent* (+ *terpri-indent* 3)))
       (mapc (lambda (q) (print-path-index-query q :terms terms)) (rest query)))
     (princ ")"))
    ((path-index-leaf-node-p query)
     (print-path-index* query (path-index-node-revpath query) terms))
    (t
     (terpri-comment-indent)
     (let ((revpath (path-index-node-revpath query)))
       (princ "(all-entries ")
       (print-revpath (cons "..." revpath))
;;     (let ((*terpri-indent* (+ *terpri-indent* 3)))
;;	 (print-path-index* query revpath terms))
       (princ ")"))))
  nil)

;;; path-index.lisp EOF
