;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: agenda.lisp
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

(defstruct agenda
  (name "" :read-only t)
  (length 0)
  (length-limit 10000000)
  (length-limit-deletion-action #'identity :read-only t)
  (same-item-p #'eql :read-only t)
  (buckets (make-ordered-set
            :key #'agenda-bucket-value
            :test #'agenda-value-lessp
            :make-element #'make-agenda-bucket)))

(defstruct (agenda-bucket
            (:constructor make-agenda-bucket (value)))
  (value nil :read-only t)
  (queue (make-queue) :read-only t))

;;; an agenda value is (list integer_1 ... integer_n) or (list* integer_1 ... integer_n)
;;; which are both treated as the same sequence integer_1 ... integer_n
;;; this includes (list* integer) = integer as an agenda value
;;; agenda values are compared lexicographically in left-to-right order
;;; if one is prefix of another, they must be equal, e.g., can't have (2 18) and (2 18 1)

(defun agenda-value-lessp (x y)
  (cond
   ((or (null x) (null y))
    (not (eq x y)))
   ((atom x)
    (< x (if (atom y) y (car y))))
   ((atom y)
    (< (car x) y))
   (t
    (or (< (car x) (car y))
        (and (= (car x) (car y))
             (agenda-value-lessp (cdr x) (cdr y)))))))

(defun value-insertable-into-agenda (value agenda &optional delete)
  ;; determines if an an item with value 'value' can be inserted into 'agenda'
  ;; (not if 'agenda' is already at its maximum size and 'value' is
  ;;  not less than the value of the last item already in 'agenda')
  ;; optionally deletes the last item in the agenda to make room
  (or (< (agenda-length agenda) (agenda-length-limit agenda))
      (and (eql (agenda-length agenda) (agenda-length-limit agenda))
	   (prog->
	     (agenda-last agenda -> item2 value2 q2)
	     (when (agenda-value-lessp value value2)
	       (when delete
		 (dequeue q2 t)
		 (decf (agenda-length agenda))
		 (funcall (agenda-length-limit-deletion-action agenda) item2))
	       t)))))

(defun agenda-insert (item value agenda &optional at-front)
  (let* ((b (oset-find-key value (agenda-buckets agenda)))
         (q (and b (agenda-bucket-queue b))))
    (unless (and q
                 (not (queue-empty-p q))
                 (funcall (agenda-same-item-p agenda)
                          item
                          (if at-front (queue-first q) (queue-last q))))
      (when (value-insertable-into-agenda value agenda t)
	(unless q
          (setq q (agenda-bucket-queue (oset-insert-key value (agenda-buckets agenda)))))
	(enqueue item q at-front)
	(incf (agenda-length agenda))))))

(defun agenda-delete (item value agenda &optional deletion-action)
  (let ((b (oset-find-key value (agenda-buckets agenda))))
    (when (and b (queue-delete/eq item (agenda-bucket-queue b)))
      (decf (agenda-length agenda)))
    (when deletion-action
      (funcall deletion-action item))))

(defun agenda-first (agenda &optional delete)
  (let ((length (agenda-length agenda)))
    (unless (eql 0 length)
      (let* ((b (oset-find-if (lambda (b) (not (queue-empty-p (agenda-bucket-queue b))))
                              (agenda-buckets agenda)))
             (q (agenda-bucket-queue b)))
        (values
         (cond
          (delete
           (setf (agenda-length agenda) (1- length))
           (dequeue q))
          (t
           (queue-first q)))
         (agenda-bucket-value b)
         q)))))

(defun pop-agenda (agenda)
  (agenda-first agenda t))

(defun agenda-last (agenda &optional delete)
  (let ((length (agenda-length agenda)))
    (unless (eql 0 length)
      (let* ((b (oset-find-if (lambda (b) (not (queue-empty-p (agenda-bucket-queue b))))
                              (agenda-buckets agenda)
                              :reverse t))
             (q (agenda-bucket-queue b)))
        (values
         (cond
          (delete
           (setf (agenda-length agenda) (1- length))
           (dequeue q t))
          (t
           (queue-last q)))
         (agenda-bucket-value b)
         q)))))

(defun mapnconc-agenda (function agenda)
  (prog->
    (mapnconc-oset (agenda-buckets agenda) ->* b)
    (mapnconc-queue (agenda-bucket-queue b) ->* item)
    (funcall function item)))

(defun agenda-delete-if (fn agenda &optional apply-length-limit-deletion-action)
  (prog->
    (and apply-length-limit-deletion-action
         (agenda-length-limit-deletion-action agenda)
         -> deletion-action)
    (mapc-oset (agenda-buckets agenda) ->* b)
    (agenda-bucket-queue b -> q)
    (mapnconc-queue (lambda (item) (when (funcall fn item) (list item))) q -> items)
    (when items
      (agenda-bucket-value b -> value)
      (dolist items ->* item)
      (agenda-delete item value agenda deletion-action))))

(defun limit-agenda-length (agenda limit)
  (let ((length (agenda-length agenda)))
    (setf (agenda-length-limit agenda) limit)
    (when (< limit length)
      (let ((i 0))
	(agenda-delete-if
	 (lambda (item)
           (declare (ignore item))
           (> (incf i) limit))
	 agenda
	 t)))))

(defun agendas-first (agendas &optional delete)
  (dolist (agenda agendas)
    (unless (eql 0 (agenda-length agenda))
      (return (agenda-first agenda delete)))))

(defun pop-agendas (agendas)
  (agendas-first agendas t))

(defvar *agenda*)		;default agenda(s) for print-agenda to display
(defvar *agendas*)

(defun print-agenda (&optional (agenda *agenda*) print-entries)
  (let ((*print-pretty* nil) (*print-radix* nil) (*print-base* 10.))
    (terpri-comment)
    (format t "The agenda of ~A has ~D entr~:@P~A"
            (agenda-name agenda)
            (agenda-length agenda)
            (if (eql 0 (agenda-length agenda)) "." ":"))
    (unless (eql 0 (agenda-length agenda))
      (let ((buckets (mapnconc-oset (lambda (b)
                                      (unless (queue-empty-p (agenda-bucket-queue b))
                                        (list b)))
                                    (agenda-buckets agenda))))
        (do* ((k (length buckets))
              (k1 (if (> 10 k) k (ceiling k 3)))
              (k2 (min k1 (- k k1)))
              (buckets3 (nthcdr (+ k1 k2) buckets))
              (l (nthcdr k1 buckets))	;in SBCL, (nbutlast nil 0) incorrectly yields an error
              (buckets2 (and l (nbutlast l (- k k1 k2))))
              (buckets1 (and buckets (nbutlast buckets k2)))
              b)
             ((null buckets1))
          (setq b (pop buckets1))
          (terpri-comment)
          (format t "~5D with value ~A" (queue-length (agenda-bucket-queue b)) (agenda-bucket-value b))
          (unless (null buckets2)
            (setq b (pop buckets2))
            (format t "~31T~5D with value ~A" (queue-length (agenda-bucket-queue b)) (agenda-bucket-value b))
            (unless (null buckets3)
              (setq b (pop buckets3))
              (format t "~61T~5D with value ~A" (queue-length (agenda-bucket-queue b)) (agenda-bucket-value b))))))
      (when (and print-entries (not (eql 0 (agenda-length agenda))))
        (prog->
          (mapc-oset (agenda-buckets agenda) ->* b)
          (agenda-bucket-queue b -> q)
          (unless (queue-empty-p q)
            (terpri-comment)
            (terpri-comment)
            (format t "Entries with value ~A:" (agenda-bucket-value b))
            (mapnconc-queue (lambda (x)
                            (terpri-comment)
                            (format t "~A" x)
                            nil)
                          q))))))
  nil)

(defun print-agendas (&optional (agendas *agendas*) print-entries)
  (let ((all-empty t))
  (dolist (agenda agendas)
    (unless (eql 0 (agenda-length agenda))
      (setq all-empty nil)
      (print-agenda agenda print-entries)))
  (when all-empty
    (terpri-comment)
    (princ "All agendas are empty."))))

(defun agenda-entries (&optional (agenda *agenda*))
  ;; added for ttp
  ;; is this function necessary?
  ;; inappropriate to directly access queue-entries
  (mapnconc-agenda #'list agenda))

;;; agenda.lisp EOF
