;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: queues.lisp
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

(in-package :mes)

;;; notes:
;;; all operations are constant-time except
;;; dequeue (from-end)
;;; queue-delete
;;; queue-delete/eq
;;; mapnconc-queue
;;; do-queue

(defstruct (queue
             (:include counter)
	     (:constructor make-queue ())
	     (:copier nil))
  (entries nil :type list)
  (entries-last nil :type list))

(defun queue-length (queue)
  (counter-value queue))

(defun queue-empty-p (queue)
  (null (queue-entries queue)))

(defun queue-first (queue)
  ;; returns first item in queue without removing it
  (first (queue-entries queue)))

(defun queue-last (queue)
  ;; returns last item in queue without removing it
  (first (queue-entries-last queue)))

(defun enqueue (item queue &optional at-front)
  ;; inserts item at end (or front) of queue
  (increment-counter queue)
  (let ((entries (and at-front (queue-entries queue))))
    (cond
      (entries
       (setf (queue-entries queue) (cons item entries)))
      (t
       (collect item (queue-entries queue)))))
  queue)

(defun dequeue (queue &optional from-end)
  ;; removes and returns first (or last) item in queue
  (let ((entries (queue-entries queue)))
    (cond
      ((null entries)
       nil)
      ((null (rest entries))
       (decrement-counter queue)
       (setf (queue-entries queue) nil)
       (setf (queue-entries-last queue) nil)
       (first entries))
      (from-end
       (decrement-counter queue)
       (let ((l (nthcdr (1- (counter-value queue)) entries)))	;inefficient
	 (prog1 (second l) (setf (queue-entries-last queue) (rplacd l nil)))))
      (t
       (decrement-counter queue)
       (setf (queue-entries queue) (rest entries))
       (first entries)))))

(defun queue-delete (item queue &key test key)
  (let ((entries (queue-entries queue)))
    (cond
      ((null entries)
       nil)
      ((let ((v (if key (funcall key (first entries)) (first entries))))
	 (if test
	     (funcall test item v)
	     (eql item v)))
       (decrement-counter queue)
       (when (null (setf (queue-entries queue) (rest entries)))
	 (setf (queue-entries-last queue) nil))
       t)
      (t
       (dotails (l entries)
	 (when (and (rest l)
		    (let ((v (if key (funcall key (second l)) (second l))))
		      (if test
			  (funcall test item v)
			  (eql item v))))
           (decrement-counter queue)
	   (when (null (setf (cdr l) (cddr l)))
	     (setf (queue-entries-last queue) l))
	   (return t)))))))

(defun queue-delete/eq (item queue)
  ;; equivalent to (queue-delete item queue :test #'eq)
  (let ((entries (queue-entries queue)))
    (cond
      ((null entries)
       nil)
      ((eq item (first entries))
       (decrement-counter queue)
       (when (null (setf (queue-entries queue) (rest entries)))
         (setf (queue-entries-last queue) nil))
       t)
      (t
       (dotails (l entries)
	 (when (and (rest l)
		    (eq item (second l)))
           (decrement-counter queue)
	   (when (null (setf (cdr l) (cddr l)))
	     (setf (queue-entries-last queue) l))
	   (return t)))))))

(defun mapnconc-queue (function queue)
  (let ((result nil) result-last)
    (dolist (item (queue-entries queue))
      (ncollect (funcall function item) result))
    result))

(defun do-queue (function queue)
  (loop
    (if (queue-empty-p queue)
	(return nil)
	(funcall function (dequeue queue)))))

;;; queues.lisp EOF
