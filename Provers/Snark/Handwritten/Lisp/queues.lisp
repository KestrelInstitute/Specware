;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes-queues -*-
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
;;; Portions created by the Initial Developer are Copyright (C) 1981-2003.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :mes-queues)

;;; notes:
;;; all operations are constant-time except:
;;;   queue-length
;;;   queue-delete
;;;   mapnconc-queue
;;;   do-queue

(defun make-queue ()
  (make-doubly-linked-list))

(defun queue-length (queue)
  (dll-length queue))

(defun queue-empty? (queue)
  (dll-empty? queue))

(defun queue-first (queue)
  ;; returns first item in queue without removing it
  (dll-first queue))

(defun queue-last (queue)
  ;; returns last item in queue without removing it
  (dll-last queue))

(defun enqueue (queue item &optional at-front)
  ;; inserts item at end (or front) of queue
  (if at-front
      (dll-push-first queue item)
      (dll-push-last queue item))
  queue)

(defun dequeue (queue &optional from-end)
  ;; removes and returns first (or last) item in queue
  (if from-end
      (dll-pop-last queue)
      (dll-pop-first queue)))

(defun queue-delete (queue item)
  (dll-delete queue item))

(defun mapnconc-queue (function queue)
  (mapnconc-dll function queue))

(defun do-queue (function queue)
  (loop
    (if (queue-empty? queue)
	(return nil)
	(funcall function (dequeue queue)))))

;;; queues.lisp EOF
