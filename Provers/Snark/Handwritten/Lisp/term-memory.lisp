;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: term-memory.lisp
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

(defvar *term-memory*)

(defstruct (term-memory-entry
	     (:include path-index-entry)
	     (:conc-name :tme-)
	     (:copier nil))
  (number (nonce) :read-only t)
  (rows-containing-atom-positively nil)
  (rows-containing-atom-negatively nil)
  (rows-containing-paramodulatable-equality nil)
  (rows-containing-term (make-rowset))
  (rewrites nil)
  size
  depth
  mindepth)

(defstruct (term-memory
	     (:conc-name :tm-)
	     (:constructor make-term-memory0)
	     (:copier nil))
  (retrieve-generalization-calls 0)		;number of generalization retrieval calls
  (retrieve-generalization-count 0)
  (retrieve-instance-calls 0)			;    "     instance          "
  (retrieve-instance-count 0)
  (retrieve-unifiable-calls 0)			;    "     unifiable         "
  (retrieve-unifiable-count 0)
  (retrieve-variant-calls 0)			;    "     variant           "
  (retrieve-variant-count 0)
  (retrieve-all-calls 0)			;    "     all               "
  (retrieve-all-count 0))

(defun make-term-memory (&key indexing-method depth-limit make-printable-nodes-p)
  (declare (ignore indexing-method depth-limit make-printable-nodes-p))
  (make-path-index :entry-constructor (lambda (term)
                                        (make-term-memory-entry
                                         :term term
                                         :size (size term)
                                         :depth (depth term)
                                         :mindepth (mindepth term))))
  (setq *term-memory* (make-term-memory0))
  *term-memory*)

(defun term-memory-entry (term)
  (path-index-entry term))

(defun some-term-memory-entry (term)
  (some-path-index-entry term))

(defun the-term-memory-entry (term)
  (the-path-index-entry term))

(defun tm-store (term)
;;(cl:assert (eql term (hash-term term)))
  (WHEN (VARIABLE-P TERM)
    (ERROR "STORING VARIABLE IN TERM MEMORY"))
  (LET ((V (TEST-OPTION10?)))
    (WHEN V
      (WHEN (COMPOUND-P TERM)
        (COND
         ((EQ :LOG V)
          (PRINT (IF (FUNCTION-BOOLEAN-VALUED-P (HEAD TERM))
                     `(INPUT-WFF ',(TERM-TO-LISP TERM))
                     `(INPUT-TRM ',(TERM-TO-LISP TERM)))))
         (T
          (CANONICAL-COMPOUND-VARIANT TERM NIL (IF (NUMBERP V) V 0)))))))
  (let (entry)
    (cond
      ((setq entry (some-path-index-entry term))
       (cl:assert (eql term (tme-term entry)))
       (values term entry t))
      (t
       (setq entry (path-index-insert term))
       (cl:assert (eql term (tme-term entry)))
       (values term entry)))))

(defun tm-remove-entry (entry)
  (path-index-delete (tme-term entry)))

(defun retrieve-generalization-terms (cc term &optional subst test)
  (WHEN (TEST-OPTION11?)
    (WHEN (DEREFERENCE TERM SUBST :IF-COMPOUND T)
      (CANONICAL-COMPOUND-VARIANT TERM SUBST)))
  (retrieve-generalizations* cc term subst test nil))

(defun retrieve-instance-terms (cc term &optional subst test)
  (WHEN (TEST-OPTION11?)
    (WHEN (DEREFERENCE TERM SUBST :IF-COMPOUND T)
      (CANONICAL-COMPOUND-VARIANT TERM SUBST)))
  (retrieve-instances* cc term subst test nil))

(defun retrieve-unifiable-terms (cc term &optional subst test)
  (WHEN (TEST-OPTION12?)
    (WHEN (DEREFERENCE TERM SUBST :IF-COMPOUND T)
      (CANONICAL-COMPOUND-VARIANT TERM SUBST)))
  (retrieve-unifiables* cc term subst test nil))

(defun retrieve-variant-terms (cc term &optional subst test)
  (retrieve-variants* cc term subst test nil))

(defun retrieve-generalization-entries (cc term &optional subst test)
  (WHEN (TEST-OPTION11?)
    (WHEN (DEREFERENCE TERM SUBST :IF-COMPOUND T)
      (CANONICAL-COMPOUND-VARIANT TERM SUBST)))
  (retrieve-generalizations* cc term subst test t))

(defun retrieve-instance-entries (cc term &optional subst test)
  (WHEN (TEST-OPTION11?)
    (WHEN (DEREFERENCE TERM SUBST :IF-COMPOUND T)
      (CANONICAL-COMPOUND-VARIANT TERM SUBST)))
  (retrieve-instances* cc term subst test t))

(defun retrieve-unifiable-entries (cc term &optional subst test)
  (WHEN (TEST-OPTION12?)
    (WHEN (DEREFERENCE TERM SUBST :IF-COMPOUND T)
      (CANONICAL-COMPOUND-VARIANT TERM SUBST)))
  (retrieve-unifiables* cc term subst test t))

(defun retrieve-variant-entries (cc term &optional subst test)
  (retrieve-variants* cc term subst test t))

;; (defvar *NPRESENT*)
;; (defvar *NABSENT*)
;; (defmethod TEST-OPTION7 :before (&optional (value t))
;;   (setf *npresent* 0)
;;   (setf *nabsent* 0))
;; (defun TEST7 (term subst)
;;   (cond
;;    ((not (test-option7?))
;;     )
;;    ((eq none (some-hash-term (renumber term subst)))
;;     (hash-term (renumber term subst))
;;     (incf *nabsent*))
;;    (t
;;     (incf *npresent*))))

(defun retrieve-generalizations* (cc term subst test retrieve-entries)
  (let ((query-id (cons 'query-id nil)))
    ;; retrieve variants, then generalizations
    ;; use same query-id for both retrievals
;;  (test7 term subst)
    #-ignore (incf (tm-retrieve-variant-calls *term-memory*))
    (if (null test)
	(prog->
	 (map-path-index :variant term subst test retrieve-entries query-id ->* item)
	 #-ignore (incf (tm-retrieve-variant-count *term-memory*))
	 (funcall cc item))
	(prog->
	 (map-path-index :variant term subst test retrieve-entries query-id ->* item test-value)
	 #-ignore (incf (tm-retrieve-variant-count *term-memory*))
	 (funcall cc item test-value)))
    #-ignore (incf (tm-retrieve-generalization-calls *term-memory*))
    (let ((size nil) (depth nil) (mindepth nil))
      (if (null test)
	  (prog->
	    (map-path-index
	      :generalization term subst
	      (lambda (entry)
                (and (<= (tme-size entry) (setq-once size (size term subst)))
                     (<= (tme-depth entry) (setq-once depth (depth term subst)))
                     (<= (tme-mindepth entry) (setq-once mindepth (mindepth term subst)))))
	      retrieve-entries query-id
	      ->* item test-value)
	    (declare (ignore test-value))
	    #-ignore (incf (tm-retrieve-generalization-count *term-memory*))
	    (funcall cc item))
	  (prog->
	    (map-path-index
	      :generalization term subst
	      (lambda (entry)
                (let ((test-value (funcall test entry)))
                  (and test-value
                       (<= (tme-size entry) (setq-once size (size term subst)))
                       (<= (tme-depth entry) (setq-once depth (depth term subst)))
                       (<= (tme-mindepth entry) (setq-once mindepth (mindepth term subst)))
                       test-value)))
	      retrieve-entries query-id
	      ->* item test-value)
	    #-ignore (incf (tm-retrieve-generalization-count *term-memory*))
	    (funcall cc item test-value))))))

(defun retrieve-instances* (cc term subst test retrieve-entries)
;;(test7 term subst)
  #-ignore (incf (tm-retrieve-instance-calls *term-memory*))
  (if (null test)
      (prog->
	(map-path-index :instance term subst test retrieve-entries ->* item)
	#-ignore (incf (tm-retrieve-instance-count *term-memory*))
	(funcall cc item))
      (prog->
	(map-path-index :instance term subst test retrieve-entries ->* item test-value)
	#-ignore (incf (tm-retrieve-instance-count *term-memory*))
	(funcall cc item test-value))))

(defun retrieve-unifiables* (cc term subst test retrieve-entries)
;;(test7 term subst)
  #-ignore (incf (tm-retrieve-unifiable-calls *term-memory*))
  (if (null test)
      (prog->
	(map-path-index :unifiable term subst test retrieve-entries ->* item)
	#-ignore (incf (tm-retrieve-unifiable-count *term-memory*))
	(funcall cc item))
      (prog->
	(map-path-index :unifiable term subst test retrieve-entries ->* item test-value)
	#-ignore (incf (tm-retrieve-unifiable-count *term-memory*))
	(funcall cc item test-value))))

(defun retrieve-variants* (cc term subst test retrieve-entries)
  #-ignore (incf (tm-retrieve-variant-calls *term-memory*))
  (if (null test)
      (prog->
	(map-path-index :variant term subst test retrieve-entries ->* item)
	#-ignore (incf (tm-retrieve-variant-count *term-memory*))
	(funcall cc item))
      (prog->
	(map-path-index :variant term subst test retrieve-entries ->* item test-value)
	#-ignore (incf (tm-retrieve-variant-count *term-memory*))
	(funcall cc item test-value))))

(defun retrieve-all-terms (cc &optional test)
  (retrieve-all* cc test nil))

(defun retrieve-all-entries (cc &optional test)
  (retrieve-all* cc test t))

(defun retrieve-all* (cc test retrieve-entries)
  #-ignore (incf (tm-retrieve-all-calls *term-memory*))
  (if (null test)
      (prog->
	(map-path-index-by-query t test retrieve-entries ->* item)
	#-ignore (incf (tm-retrieve-all-count *term-memory*))
	(funcall cc item))
      (prog->
	(map-path-index-by-query t test retrieve-entries ->* item test-value)
	#-ignore (incf (tm-retrieve-all-count *term-memory*))
	(funcall cc item test-value))))

(defun print-term-memory (&key terms nodes)
  (let ((*print-pretty* nil) (*print-radix* nil) (*print-base* 10.))
    (print-term-hash :terms nil)
    (print-path-index :terms terms :nodes nodes)
    (unless (= (tm-retrieve-variant-calls *term-memory*) 0)
      (terpri-comment)
      (format t "Retrieved ~D variant terms in ~D calls."
              (tm-retrieve-variant-count *term-memory*)
              (tm-retrieve-variant-calls *term-memory*)))
    (unless (= (tm-retrieve-generalization-calls *term-memory*) 0)
      (terpri-comment)
      (format t "Retrieved ~D generalization terms in ~D calls."
              (tm-retrieve-generalization-count *term-memory*)
              (tm-retrieve-generalization-calls *term-memory*)))
    (unless (= (tm-retrieve-instance-calls *term-memory*) 0)
      (terpri-comment)
      (format t "Retrieved ~D instance terms in ~D calls."
              (tm-retrieve-instance-count *term-memory*)
              (tm-retrieve-instance-calls *term-memory*)))
    (unless (= (tm-retrieve-unifiable-calls *term-memory*) 0)
      (terpri-comment)
      (format t "Retrieved ~D unifiable terms in ~D calls."
              (tm-retrieve-unifiable-count *term-memory*)
              (tm-retrieve-unifiable-calls *term-memory*)))
    (unless (= (tm-retrieve-all-calls *term-memory*) 0)
      (terpri-comment)
      (format t "Retrieved ~D unrestricted terms in ~D calls."
              (tm-retrieve-all-count *term-memory*)
              (tm-retrieve-all-calls *term-memory*)))
    (WHEN (TEST-OPTION10?)
      (PRINT-INSTANCE-GRAPHS :TERMS TERMS))))

(defmacro null-or-empty? (x)
  (let ((v (gensym)))
    `(let ((,v ,x))
       (if (null ,v) t (eql 0 (sparse-vector-count ,v))))))

(defun tme-useless-p (entry)
  (and (null-or-empty? (tme-rows-containing-term entry))
       (null-or-empty? (tme-rows-containing-atom-positively entry))
       (null-or-empty? (tme-rows-containing-atom-negatively entry))
       (null (tme-rows-containing-paramodulatable-equality entry))
       (null (tme-rewrites entry))))

(defmacro rows-containing-atom-positively (atom)
  `(tme-rows-containing-atom-positively
    (term-memory-entry ,atom)))

(defmacro rows-containing-atom-negatively (atom)
  `(tme-rows-containing-atom-negatively
    (term-memory-entry ,atom)))

(defmacro rows-containing-paramodulatable-equality (equality)
  `(tme-rows-containing-paramodulatable-equality
    (term-memory-entry ,equality)))

(defmacro rows-containing-term (term)
  `(tme-rows-containing-term
    (term-memory-entry ,term)))

(defun rows-containing-term2 (term)
  (let ((e (some-term-memory-entry term)))
    (and e (tme-rows-containing-term e))))

(defmacro rewrites (term)
  `(tme-rewrites
    (term-memory-entry ,term)))

(defun insert-into-rows-containing-term (row term)
  (let ((e (term-memory-entry term)))
    (rowset-insert row (tme-rows-containing-term e))))

(defun insert-into-rows-containing-atom-positively (row atom)
  (let ((e (term-memory-entry atom)))
    (rowset-insert row (or (tme-rows-containing-atom-positively e)
                           (setf (tme-rows-containing-atom-positively e) (make-rowset))))))

(defun insert-into-rows-containing-atom-negatively (row atom)
  (let ((e (term-memory-entry atom)))
    (rowset-insert row (or (tme-rows-containing-atom-negatively e)
                           (setf (tme-rows-containing-atom-negatively e) (make-rowset))))))

;;; term-memory.lisp EOF
