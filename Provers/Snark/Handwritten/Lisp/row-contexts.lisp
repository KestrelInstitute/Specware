;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: row-contexts.lisp
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

;;; assertions go into context 1
;;; assumptions and negated conclusions go into (first (current-row-context))
;;; inferred rows go into the maximum of the contexts of the rows they're inferred from

(defvar *number-of-row-contexts* 0)
(defvar *current-row-context*)

(defmacro current-row-context ()
  `*current-row-context*)

(defun initialize-row-contexts ()
  (setf *number-of-row-contexts* 2)
  (setf (current-row-context) (list 2 1))
  nil)

(defun push-row-context ()
  ;; extend the context in (current-row-context)
  ;; by adding a new context number to the front
  (push (incf *number-of-row-contexts*) (current-row-context))
  nil)

(defun pop-row-context ()
  ;; shorten the context in (current-row-context)
  ;; by removing the first context number from the front
  ;; not allowed to pop out of context 1
  (let ((context (current-row-context)))
    (cl:assert (neql 1 (first context)))
    (setf (current-row-context) (rest context))
    (delete-row-if (lambda (row) (not (row-present-in-context-p row))))
    nil))

(defun new-row-context ()
  (pop-row-context)
  (push-row-context))

;;; the row-context slot is an interval of context numbers [start,end)
;;; a row is present in [start,end) intersected with the current row context
;;; end=nil signifies infinity

(defmacro make-row-context (context &optional context-del)
  `(cons ,context ,context-del))

(defmacro row-context-start (rc)
  ;; the context to which the row was added
  `(car ,rc))

(defmacro row-context-end (rc)
  ;; the context from which the row was deleted
  `(cdr ,rc))

(defun row-present-in-context-p1 (cd context)
  (let ((c (row-context-start cd)))
    (and (or (eql 1 c) (member c context))
         (let ((d (row-context-end cd)))
;;         (cl:assert (implies d (< c d)))
           (if (implies d (member d context)) cd (make-row-context c nil))))))

(defun context-intersection-p1 (x y)
  (and x
       y
       (let* ((a (max (row-context-start x) (row-context-start y)))
              (d1 (row-context-end x))
              (d2 (row-context-end y)))
         (cond
          ((null d1)
           (if (or (null d2) (< a d2)) (make-row-context a d2) nil))
          ((or (null d2) (<= d1 d2))
           (if (< a d1) (make-row-context a d1) nil))
          (t
           (if (< a d2) (make-row-context a d2) nil))))))

(defun context-subsumption-p1 (x y)
  (let ((xa (row-context-start x))
	(ya (row-context-start y)))
    (if (<= xa ya)
	t
	(let ((yd (row-context-end y)))
	  (if (or (null yd) (< xa yd))
	      (make-row-context ya xa)
	      nil)))))

;;; when partitions are used
;;; row-context is represented as list of elements of the form
;;; (partition-id . row-context)

(defun input-row-context (context partitions)
  ;; (use-partitions?) is either nil (partitions are not being used)
  ;; or a list of partition ids
  (let ((all-partitions (use-partitions?))
        (v (make-row-context context)))
    (cond
      (all-partitions
       (mapcar (lambda (part)
                 (if (member part all-partitions)
                     (cons part v)
                     (error "~A is not a partition.")))
               (mklist partitions)))
      (t
       v))))

(defun row-present-in-context-p (row &optional (context (current-row-context)))
  (cl:assert context)
  (cond
    ((use-partitions?)
     (mapcan (lambda (pcd)
	       (let* ((cd (cdr pcd))
		      (cd* (row-present-in-context-p1 cd context)))
		 (when cd*
		   (list (if (eq cd cd*) pcd (cons (car pcd) cd*))))))
	     (row-context row)))
    (t
     (row-present-in-context-p1 (row-context row) context))))

(defun context-intersection-p (x y)
  (cond
    ((use-partitions?)
     (mapcan (lambda (pcd)
	       (let* ((part (car pcd))
		      (cd (cdr pcd))
		      (cd* (context-intersection-p1 (cdr (assoc part x)) cd)))
		 (when cd*
		   (list (if (eq cd cd*) pcd (cons part cd*))))))
	     y))
    (t
     (context-intersection-p1 x y))))

(defun context-subsumption-p (x y)
  (cond
   ((use-partitions?)
    (let ((w (mapcan (lambda (pcd)
                       (let* ((part (car pcd))
                              (cd (cdr pcd))
                              (v (cdr (assoc part x))))
                         (cond
                          ((null v)
                           (list pcd))
                          (t
                           (let ((cd* (context-subsumption-p1 v cd)))
                             (cond
                              ((null cd*)
                               (list pcd))
                              ((eq t cd*)
                               nil)
                              (t
                               (list (cons part cd*)))))))))
                     y)))
      (cond
       ((null w)					;x always includes y
        t)
       ((equal x w)					;x never includes y
        nil)
       (t						;x partly includes y
        w)))) 
   (t
    (context-subsumption-p1 x y))))

;;; *rewriting-row-context* is rebound around the code for rewriting to
;;; restrict what rewrites are available and thus prevent application of
;;; a rewrite to a row in a lower context

(defvar *rewriting-row-context* nil)

;;; row-contexts.lisp EOF
