;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes-doubly-linked-list -*-
;;; File: doubly-linked-list.lisp
;;; Copyright (c) 2003 Mark E. Stickel
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a
;;; copy of this software and associated documentation files (the "Software"),
;;; to deal in the Software without restriction, including without limitation
;;; the rights to use, copy, modify, merge, publish, distribute, sublicense,
;;; and/or sell copies of the Software, and to permit persons to whom the
;;; Software is furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included
;;; in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(in-package :mes-doubly-linked-list)

;;; notes:
;;; all operations are constant-time except:
;;;   dll-length
;;;   dll-contains
;;;   dll-delete
;;;   dll-mapnconc

(defmacro make-dll-node (value prev next)
  `(cons ,value (cons ,prev ,next)))

(defmacro dll-node-value (n)
  `(car ,n))

(defmacro dll-node-ptrs (n)
  `(cdr ,n))

(defmacro dll-prev-ptr (p)
  `(car ,p))

(defmacro dll-next-ptr (p)
  `(cdr ,p))

(defmacro dll-prev-node (n)
  `(dll-prev-ptr (dll-node-ptrs ,n)))

(defmacro dll-next-node (n)
  `(dll-next-ptr (dll-node-ptrs ,n)))

(defun dll-insert-after-node (node value)
  (let* ((next-node (dll-next-node node))
         (new-node (make-dll-node value node next-node)))
    (setf (dll-next-node node) new-node)
    (setf (dll-prev-node next-node) new-node)
    new-node))

(defun dll-insert-before-node (node value)
  (let* ((prev-node (dll-prev-node node))
         (new-node (make-dll-node value prev-node node)))
    (setf (dll-prev-node node) new-node)
    (setf (dll-next-node prev-node) new-node)
    new-node))

(defun dll-delete-node (node)
  (when node
    (let ((next-node (dll-next-node node)))
      (when next-node				;guard against double deletion
        (setf (dll-next-node node) nil)
        (let ((prev-node (dll-prev-node node)))
          (setf (dll-next-node prev-node) next-node)
          (setf (dll-prev-node next-node) prev-node)
          t)))))

(defun make-doubly-linked-list ()
  (let ((start-end-node (make-dll-node 'doubly-linked-list nil nil)))
    (setf (dll-prev-node start-end-node) start-end-node)
    (setf (dll-next-node start-end-node) start-end-node)
    start-end-node))

(definline dll-empty? (l)
  (eq l (dll-next-node l)))

(definline dll-push-first (l value)
  ;; returns the value-containing node inserted at the front end of doubly linked list l
  (dll-insert-after-node l value))

(definline dll-push-last (l value)
  ;; returns the value-containing node inserted at the back end of doubly linked list l
  (dll-insert-before-node l value))

(definline dll-pop-first (l)
  ;; removes and returns the value stored at the front end of doubly linked list l
  ;; returns nil if l is empty
  (let ((n (dll-next-node l)))
    (and (not (eq l n)) (progn (dll-delete-node n) (dll-node-value n)))))

(definline dll-pop-last (l)
  ;; removes and returns the value stored at the back end of doubly linked list l
  ;; returns nil if l is empty
  (let ((n (dll-prev-node l)))
    (and (not (eq l n)) (progn (dll-delete-node n) (dll-node-value n)))))

(definline dll-first (l)
  ;; returns the value stored at the front end of doubly linked list l
  ;; returns nil if l is empty
  (let ((n (dll-next-node l)))
    (and (not (eq l n)) (dll-node-value n))))

(definline dll-last (l)
  ;; returns the value stored at the back end of doubly linked list l
  ;; returns nil if l is empty
  (let ((n (dll-prev-node l)))
    (and (not (eq l n)) (dll-node-value n))))

(defun dll-length (l)
  (let ((len 0)
        (n l))
    (loop
      (cond
       ((eq l (setf n (dll-next-node n)))
        (return len))
       (t
        (incf len))))))

(defun dll-contains (l value)
  (let ((n l))
    (loop
      (cond
       ((eq l (setf n (dll-next-node n)))
        (return nil))
       ((eql value (dll-node-value n))
        (return n))))))

(defun dll-delete (l value)
  (dll-delete-node (dll-contains l value)))

(definline dll-mapnconc (l &optional function)
  (mapnconc-dll function l))

(defun mapnconc-dll (function l)
  (let ((result nil) result-last
        (n l))
    (loop
      (cond
       ((eq l (setf n (dll-next-node n)))
        (return result))
       ((null function)
        (collect (dll-node-value n) result))
       (t
        (ncollect (funcall function (dll-node-value n)) result))))))

;;; doubly-linked-list.lisp EOF
