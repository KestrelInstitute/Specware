;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: term-hash.lisp
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

(defvar *atom-hash-code*)
(defvar *default-term-by-hash-array-size* 50000)
(defvar *term-by-hash-array*)
(defvar *hash-term-uses-variable-numbers* t)
(defvar *hash-term-only-computes-code* nil)
(defvar *hash-term-not-found-action* :add)

(defun initialize-term-hash (&key (size *default-term-by-hash-array-size*))
  (setf *atom-hash-code* 0)
  (setf *term-by-hash-array* (make-array size :initial-element nil))
  nil)

(defun make-atom-hash-code ()
  ;; return a hash-code in [2,1023]
  (if (<= (setf *atom-hash-code* (mod (+ (* 129 *atom-hash-code*) 1) 1024)) 1)
      (make-atom-hash-code)
      *atom-hash-code*))

(defun find-term-by-hash (x hash)
  (let* ((term-by-hash-array *term-by-hash-array*)
	 (k (mod hash (array-dimension term-by-hash-array 0)))
	 (terms (svref term-by-hash-array k)))
    (when terms
      (dolist (term terms)
	(when (eq term x)
	  (return-from find-term-by-hash term)))
      (dolist (term terms)
	(when (equal-p term x)
	  (return-from find-term-by-hash term))))
    (ecase *hash-term-not-found-action*
      (:add
	(setf (svref term-by-hash-array k) (cons x terms))
	x)
      (:throw
	(throw 'hash-term-not-found none))
      (:error
	(error "No hash-term for ~S." x)))))

(defun term-by-hash-array-terms (&optional delete-variants)
  (let ((term-by-hash-array *term-by-hash-array*)
        (terms nil) terms-last)
    (dotimes (k (array-dimension term-by-hash-array 0))
      (let ((l (copy-list (svref term-by-hash-array k))))
        (ncollect (if (and delete-variants (not *hash-term-uses-variable-numbers*))
                      (delete-duplicates l :test #'variant-p)
                      l)
                  terms)))
    (if (and delete-variants *hash-term-uses-variable-numbers*)
        (delete-duplicates terms :test #'variant-p)
        terms)))

(defmacro thvalues (hash x)
  `(if *hash-term-only-computes-code* ,hash (values ,hash ,x)))

(defmacro hash-variable (x)
  (cl:assert (symbolp x))
  `(thvalues (if *hash-term-uses-variable-numbers* (+ 1024 (variable-number ,x)) 0) ,x))

(defmacro hash-constant (x)
  (cl:assert (symbolp x))
  `(thvalues (constant-hash-code ,x) ,x))

(defun hash-term* (x subst)
  (dereference
   x subst
   :if-variable (hash-variable x)
   :if-constant (hash-constant x)
   :if-compound-cons (mvlet* ((a (carc x))
                              (d (cdrc x))
                              ((:values ahash a*) (hash-term* a subst))
                              ((:values dhash d*) (hash-term* d subst)))
                       (thvalues (+ ahash dhash (function-hash-code *cons*))
                                 (if (and (eq d d*) (eql a a*)) x (cons a* d*))))
   :if-compound-appl (mvlet (((:values hash x) (hash-compound x subst)))
                       (thvalues hash (find-term-by-hash x hash)))))

(defun hash-term-code (x &optional subst)
  ;; just return the hash code without finding or creating canonical forms
  (let ((*hash-term-only-computes-code* t))
    (hash-term* x subst)))

(defun hash-term (x &optional subst)
  ;; find or create canonical form of x.subst
  ;; (equal-p x (hash-term x))
  ;; (equal-p x y) => (eql (hash-term x) (hash-term y))
  (mvlet (((:values hash x) (hash-term* x subst)))
    (values x hash)))

(defun some-hash-term (x &optional subst)
  ;; hash-term or none
  (let ((*hash-term-not-found-action* :throw))
    (catch 'hash-term-not-found
      (hash-term x subst))))

(defun the-hash-term (x &optional subst)
  ;; hash-term or error
  (let ((*hash-term-not-found-action* :error))
    (hash-term x subst)))

(defun hash-list (l subst multiplier)
  ;; (a b c ...) -> 2*hash(a) + 3*hash(b) + 4*hash(c) ...
;;(cl:assert (not (null l)))
  (mvlet* ((x (first l))
           ((:values xhash x*) (hash-term* x subst))
           (y (rest l)))
    (when multiplier
      (setf xhash (* multiplier xhash)))
    (if (null y)
        (thvalues xhash (if (eql x x*) l (cons x* nil)))
        (mvlet (((:values yhash y*) (hash-list y subst (and multiplier (1+ multiplier)))))
          (thvalues (+ xhash yhash) (if (and (eq y y*) (eql x x*)) l (cons x* y*)))))))

(defun hash-compound (compd &optional subst)
  ;; this uses a simpler term hashing function than before
  ;; it should be is easier to verify and maintain
  ;;
  ;; for (f t1 ... tn) it computes (+ (# f) (* 2 (# t1)) ... (* (1+ n) (# tn)))
  ;; but uses 0 for (# f) if f is associative (since these symbols may disappear)
  ;; and uses 1 for multipliers if f is associative, commutative, etc.
  ;; and also uses 1 for multipliers if f is cons (overkill to handle :plist and :alist functions)
  ;;
  ;; when *hash-term-uses-variable-numbers* is nil
  ;; it should be the case that (implies (subsumes-p t1 t2) (<= (# t1) (# t2)))
  (let ((head (head compd))
        (args (args compd)))
    (cond
     ((null args)
      (function-hash-code head))
     ((function-index-type head)
      (ecase (function-index-type head)
        (:jepd
         (prog->
           (first args -> arg1)
           (hash-term* arg1 subst -> hash1 arg1*)
           (second args -> arg2)
           (hash-term* arg2 subst -> hash2 arg2*)
           (third args -> arg3)
           (instantiate arg3 subst -> arg3*)
           (thvalues (+ (function-hash-code head) (* 2 hash1) (* 2 hash2))
                     (if (eq arg3 arg3*)
                         (if (eql arg2 arg2*)
                             (if (eql arg1 arg1*)
                                 compd
                                 (make-compound* head arg1* (rest args)))
                             (make-compound* head arg1* arg2* (rest (rest args))))
                         (make-compound head arg1* arg2* arg3*)))))))
     (t
      (mvlet (((:values hash args*)
               (hash-list args subst (and (not (cons-function-symbol-p head))
                                          (not (function-associative head))
                                          (not (function-commutative head))
                                          (not (function-permutations head))
                                          2))))
        (incf hash (function-hash-code head))
        (thvalues hash
                  (find-term-by-hash
                   (if (eq args args*) compd (make-compound* head args*))
                   hash)))))))

(defun print-term-hash (&key terms)
  (let ((*print-pretty* nil) (*print-radix* nil) (*print-base* 10.)
        (size 5) (term-by-hash-array-size (array-dimension *term-by-hash-array* 0)))
    (let ((a (make-array size :initial-element 0)) (npositions 0) (nterms 0))
;;    (terpri-comment-indent)
;;    (format t "Term-hash-array has ~D positions." term-by-hash-array-size)
      (dotimes (position term-by-hash-array-size)
	(let ((len (length (svref *term-by-hash-array* position))))
	  (unless (eql 0 len)
	    (incf npositions)
	    (incf nterms len)
	    (incf (svref a (1- (min size len)))))))
      (terpri-comment-indent)
      (format t "Term-hash-array has ~D positions filled with ~D term~:P in all." npositions nterms)
      (dotimes (len-1 size)
	(let ((n (svref a len-1)))
	  (when (> n 0)
	    (let ((len (1+ len-1)))
	      (terpri-comment-indent)
	      (if (eql len size)
		  (format t "Term-hash-array has ~D position~:P filled with ~D terms or more each." n len)
		  (format t "Term-hash-array has ~D position~:P filled with ~D term~:P each." n len)))))))
    (when terms
      (dotimes (position term-by-hash-array-size)
	(let ((l (svref *term-by-hash-array* position)))
	  (when (if (numberp terms) (>= (length l) (max terms 1)) l)
	    (terpri-comment-indent)
	    (format t "~6D: " position)
	    (print-term (first l))
	    (dolist (term (rest l))
	      (terpri-comment-indent)
	      (princ "        ")
	      (print-term term))))))))

(defvar *default-hash-term-set-count-down-to-hashing* 10)	;can insert this many before hashing

(defstruct (hash-term-set
            (:constructor make-hash-term-set (&optional substitution))
            (:conc-name :hts-))
  (terms nil)					;list or hash-table of terms
  (substitution nil :read-only t)
  (count-down-to-hashing *default-hash-term-set-count-down-to-hashing*))

(defun hts-member-p (term hts)
  (let* ((terms (hts-terms hts))
         (l (if (eql 0 (hts-count-down-to-hashing hts))
               (gethash (hash-term-code term) terms)
               terms)))
    (if (and l (member-p term l (hts-substitution hts))) t nil)))

(defun hts-adjoin-p (term hts)
  ;; if term is a already a member of hts, return NIL
  ;; otherwise add it and return true
  (let* ((terms (hts-terms hts))
         (c (hts-count-down-to-hashing hts))
         h
         (l (if (eql 0 c)
                (gethash (setf h (hash-term-code term)) terms)
                terms)))
    (cond
     ((and l (member-p term l (hts-substitution hts)))
      nil)
     ((eql 0 c)
      (setf (gethash h terms) (cons term l))
      t)
     ((eql 1 c)
      (setf (hts-terms hts) (setf terms (make-hash-table)))
      (setf (gethash (hash-term-code term) terms) (cons term nil))
      (dolist (term l)
        (push term (gethash (hash-term-code term) terms)))
      (setf (hts-count-down-to-hashing hts) 0)
      t)
     (t
      (setf (hts-terms hts) (cons term l))
      (setf (hts-count-down-to-hashing hts) (1- c))
      t))))
  
;;; term-hash.lisp EOF
