;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: sparse-array4.lisp
;;; Copyright (c) 2002 Mark E. Stickel
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

(in-package :mes)

(defstruct (sparse-vector
            (:constructor make-sparse-vector0 (default-value boolean))
            (:print-function print-sparse-vector3)
            (:copier nil))
  (default-value nil :read-only t)
  (boolean nil :read-only t)
  (type nil)
  (count 0 :type fixnum)
  (positive-trie nil)
  (negative-trie nil)
  (cached-entry nil)
  (entries (initial-sparse-vector-entries boolean) :read-only t))

;;; radix-search-trie nodes are:
;;;  (index               . (prev . next))	;type-T leaf-node for boolean sparse-vector entry
;;;  ((index . value)     . (prev . next))	;type-V leaf-node for nonboolean sparse-vector entry
;;;  ((branch0 . branch1) . bit-number)		;nonleaf-node (for radix-search-trie indexing)
;;;
;;; entries are indexed in radix-search-trie for fast insertion and deletion
;;; and are also linked to each other for fast traversal
;;;
;;; leaf-nodes:     2 conses each for boolean, 3 for nonboolean sparse-vectors
;;; nonleaf-nodes:  2 conses each; there will be (1- #leaf-nodes) nonleaf-nodes
;;;
;;; insertions and deletions made ahead of cursor during traversal will be heeded
;;;
;;; next-svn1 and prev-svn1 should be more efficient

(defmacro svn-leaf? (svn)
  ;; leaf-nodes are distinguished from nonleaf-nodes by whether cdr is a cons
  `(consp (cdrc ,svn)))

(defmacro leaf-svn-boolean? (svn)
  ;; type-T leaf-nodes are distinguished from type-V leaf-nodes by whether car is a cons
  `(not (consp (carc ,svn))))

;;; leaf-node constructors and accessors:

(defmacro make-leaf-svn-t (index prev next)
  `(cons ,index (cons ,prev ,next)))

(defmacro make-leaf-svn-v (index value prev next)
  `(cons (cons ,index ,value) (cons ,prev ,next)))

(defmacro svn-index (svn)
  (let ((v (gensym)))
    `(let ((,v (carc ,svn)))
       (if (consp ,v) (carc ,v) ,v))))

(defmacro svn-value (svn)
  (let ((v (gensym)))
    `(let ((,v (carc ,svn)))
       (if (consp ,v) (cdrc ,v) t))))

(defmacro set-svn-value (value svn)
  (let ((v (gensym)))
    `(let ((,v (carc ,svn)))
       (if (consp ,v) (setf (cdrc ,v) ,value) ,value))))

(defmacro svn-index-t (svn)
  `(carc ,svn))

(defmacro svn-index-v (svn)
  `(caarcc ,svn))

(defmacro svn-value-v (svn)
  `(cdarcc ,svn))

(defmacro svn-value-t (svn)
  `(progn ,svn t))

(defmacro prev-svn (svn)
  `(cadrcc ,svn))

(defmacro next-svn (svn)
  `(cddrcc ,svn))

;;; nonleaf-node constructors and accessors:

(defmacro make-nonleaf-svn (bit branch1 branch0)
  `(cons (cons ,branch0 ,branch1) ,bit))

(defmacro svn-bit (svn)
  `(the fixnum (cdrc ,svn)))

(defmacro svn-branch-0 (svn)
  `(caarcc ,svn))

(defmacro svn-branch-1 (svn)
  `(cdarcc ,svn))

(defun initial-sparse-vector-entries (boolean)
  ;; create the initial doubly linked circular list of entries for fast traversals
  (let ((stop (if boolean
                  (make-leaf-svn-t -999999 nil nil)
                  (make-leaf-svn-v -999999 -999999 nil nil))))
    ;; stop is a dummy entry used as start and stop point for traversals
    (setf (prev-svn stop) stop)
    (setf (next-svn stop) stop)
    stop))

(defun sparef1 (sparse-vector index)
  (macrolet
    ((sv-linear-search (n.svn-index n.svn-value default-value)
       ;; backward linear search for short nonempty sparse-vectors
       `(let* ((stop (sparse-vector-entries sparse-vector))
               (n (prev-svn stop))
               k)
          (loop
            (cond
             ((>= index (setf k ,n.svn-index))
              (return
               (if (eql index k)
                   (progn (setf (sparse-vector-cached-entry sparse-vector) n) ,n.svn-value)
                   ,default-value)))
             ((eq stop (setf n (prev-svn n)))
              (return ,default-value))))))
     (sv-radix-search (n.svn-index n.svn-value default-value)
       `(cond
         ((null (setf n (if (<= 0 index)
                            (sparse-vector-positive-trie sparse-vector)
                            (sparse-vector-negative-trie sparse-vector))))
          ,default-value)
         (t
          (loop
            (if (svn-leaf? n)
                (return
                 (if (eql index ,n.svn-index)
                     (progn (setf (sparse-vector-cached-entry sparse-vector) n) ,n.svn-value)
                     ,default-value))
                (setf n (if (logbitp (svn-bit n) index) (svn-branch-1 n) (svn-branch-0 n))))))))
     (sv-search (n.svn-index n.svn-value default-value)
       `(let ((n (sparse-vector-cached-entry sparse-vector)))
          (cond
           ((and n (eql index ,n.svn-index))
            ,n.svn-value)
           ((>= 10 cnt)
            (sv-linear-search ,n.svn-index ,n.svn-value ,default-value))
           (t
            (sv-radix-search ,n.svn-index ,n.svn-value ,default-value))))))
    (let ((cnt (sparse-vector-count sparse-vector)))
      (declare (type fixnum cnt))
      (cond
       ((>= 1 cnt)
        (if (eql 0 cnt)
            (sparse-vector-default-value sparse-vector)
            (let ((n (or (sparse-vector-cached-entry sparse-vector)
                         (setf (sparse-vector-cached-entry sparse-vector)
                               (next-svn (sparse-vector-entries sparse-vector))))))
              (if (sparse-vector-boolean sparse-vector)
                  (eql index (svn-index-t n))
                  (if (eql index (svn-index-v n))
                      (svn-value-v n)
                      (sparse-vector-default-value sparse-vector))))))
       ((sparse-vector-boolean sparse-vector)
        (sv-search (svn-index-t n) t nil))
       (t
        (sv-search (svn-index-v n) (svn-value-v n) (sparse-vector-default-value sparse-vector)))))))

(definline unlink-svn (n)
  (let ((prev (prev-svn n))
        (next (next-svn n)))
    (setf (next-svn prev) next)
    (setf (prev-svn next) prev)
    (setf (next-svn n) nil)
    (setf (prev-svn n) nil)))

(definline link-svn (prev n next)
  (setf (prev-svn n) prev)
  (setf (next-svn n) next)
  (setf (next-svn prev) n)
  (setf (prev-svn next) n)
  n)

(definline svn-min-leaf (n)
  (loop
    (if (svn-leaf? n)
        (return n)
        (setf n (svn-branch-0 n)))))

(definline svn-max-leaf (n)
  (loop
    (if (svn-leaf? n)
        (return n)
        (setf n (svn-branch-1 n)))))

(definline link-svn-after (n prev)
  (setf prev (svn-max-leaf prev))
  (link-svn prev n (next-svn prev)))

(definline link-svn-before (n next)
  (setf next (svn-min-leaf next))
  (link-svn (prev-svn next) n next))

(defun sparse-vector-setter (value sparse-vector index)
  (macrolet ((default-value? ()
               `(eql value (sparse-vector-default-value sparse-vector)))
             (new-entry ()
               `(progn (incf (sparse-vector-count sparse-vector))
                       (setf (sparse-vector-cached-entry sparse-vector)
                             (if (sparse-vector-boolean sparse-vector)
                                 (make-leaf-svn-t index nil nil)
                                 (make-leaf-svn-v index value nil nil)))))
             (new-node ()
               `(if (logbitp b index)
                    (make-nonleaf-svn b (link-svn-after (new-entry) n) n)
                    (make-nonleaf-svn b n (link-svn-before (new-entry) n))))
             (diff-bit (x)
               `(the fixnum (1- (the fixnum (integer-length (logxor index ,x)))))))
    (labels
      ((setter (n)
         (cond
          ((svn-leaf? n)
           (let ((k (svn-index n)))
             (cond
              ((eql index k)
               (cond
                ((default-value?)
                 (decf (sparse-vector-count sparse-vector))
                 (unlink-svn n)
                 (if (eq n (sparse-vector-cached-entry sparse-vector))
                     (setf (sparse-vector-cached-entry sparse-vector) nil)
                     nil))
                (t
                 (set-svn-value value n)
                 (setf (sparse-vector-cached-entry sparse-vector) n))))
              ((default-value?)
               n)
              (t
               (let ((b (diff-bit k)))
                 (declare (type fixnum b))
                 (new-node))))))
          (t
           (let ((b (diff-bit (svn-index (svn-min-leaf (svn-branch-0 n)))))
                 (b2 (svn-bit n)))
             (declare (type fixnum b b2))
             (cond
              ((> b b2)
               (if (default-value?) n (new-node)))
              ((eql b b2)
               (let ((v (setter (svn-branch-1 n))))
                 (if v (progn (setf (svn-branch-1 n) v) n) (svn-branch-0 n))))
              (t
               (let ((v (setter (svn-branch-0 n))))
                 (if v (progn (setf (svn-branch-0 n) v) n) (svn-branch-1 n))))))))))
      (let ((n (sparse-vector-cached-entry sparse-vector)))
        (cond
         ((and n (eql index (svn-index n)) (not (default-value?)))
          (set-svn-value value n))
         (t
          (if (<= 0 index)
              (if (null (setf n (sparse-vector-positive-trie sparse-vector)))
                  (unless (default-value?)
                    (setf (sparse-vector-positive-trie sparse-vector)
                          (link-svn-before (new-entry) (sparse-vector-entries sparse-vector))))
                  (setf (sparse-vector-positive-trie sparse-vector) (setter n)))
              (if (null (setf n (sparse-vector-negative-trie sparse-vector)))
                  (unless (default-value?)
                    (setf (sparse-vector-negative-trie sparse-vector)
                          (link-svn-after (new-entry) (sparse-vector-entries sparse-vector))))
                  (setf (sparse-vector-negative-trie sparse-vector) (setter n))))
          value))))))

(defmacro next-svn1 (index &optional (svn-index 'svn-index))
  ;; find the first entry that is >= index
  ;; next-svn1 can be used to find the next node after index's is deleted
  (let ((n (gensym)))
    `(let ((k ,index)
           (,n (next-svn stop)))
       (loop
         (if (or (eq stop ,n) (>= (,svn-index ,n) k))
             (return ,n)
             (setf ,n (next-svn ,n)))))))

(defmacro prev-svn1 (index &optional (svn-index 'svn-index))
  ;; find the last entry that is <= index
  ;; prev-svn1 can be used to find the previous node after index's is deleted
  (let ((n (gensym)))
    `(let ((k ,index)
           (,n (prev-svn stop)))
       (loop
         (if (or (eq stop ,n) (<= (,svn-index ,n) k))
             (return ,n)
             (setf ,n (prev-svn ,n)))))))

(defmacro next-svn2 (n &optional (svn-index 'svn-index))
  (cl:assert (symbolp n))
  `(or (next-svn ,n) (next-svn1 (,svn-index ,n) ,svn-index)))

(defmacro prev-svn2 (n &optional (svn-index 'svn-index))
  (cl:assert (symbolp n))
  `(or (prev-svn ,n) (prev-svn1 (,svn-index ,n) ,svn-index)))

(defmacro next-svn3 (min &optional (svn-index 'svn-index))
  (cl:assert (symbolp min))
  `(if ,min (next-svn1 ,min ,svn-index) (next-svn stop)))

(defmacro prev-svn3 (max &optional (svn-index 'svn-index))
  (cl:assert (symbolp max))
  `(if ,max (prev-svn1 ,max ,svn-index) (prev-svn stop)))

(defmacro map-sparse-vector-loop-f (form &optional (svn-index 'svn-index))
  `(let ((n (next-svn3 min ,svn-index)))
     (loop
       (if (eq stop n)
           (return nil)
           (progn ,form (setf n (next-svn2 n ,svn-index)))))))

(defmacro map-sparse-vector-loop-b (form &optional (svn-index 'svn-index))
  `(let ((n (prev-svn3 max ,svn-index)))
     (loop
       (if (eq stop n)
           (return nil)
           (progn ,form (setf n (prev-svn2 n ,svn-index)))))))

(defmacro map-sparse-vector-loop-f2 (form &optional (svn-index 'svn-index))
  `(map-sparse-vector-loop-f (if (< max (,svn-index n)) (return nil) ,form) ,svn-index))

(defmacro map-sparse-vector-loop-b2 (form &optional (svn-index 'svn-index))
  `(map-sparse-vector-loop-b (if (> min (,svn-index n)) (return nil) ,form) ,svn-index))

(defun map-sparse-vector0 (function sparse-vector reverse min max map)
  ;; always returns nil
  (let ((stop (sparse-vector-entries sparse-vector)))
    (if reverse
        (if min
            (cond
             ((null map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-b2 (funcall function (svn-index-t n) t) svn-index-t)
                  (map-sparse-vector-loop-b2 (funcall function (svn-index-v n) (svn-value-v n)) svn-index-v)))
             ((eq :indexes map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-b2 (funcall function (svn-index-t n)) svn-index-t)
                  (map-sparse-vector-loop-b2 (funcall function (svn-index-v n)) svn-index-v)))
             (t
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-b2 (funcall function t) svn-index-t)
                  (map-sparse-vector-loop-b2 (funcall function (svn-value-v n)) svn-index-v))))
            (cond
             ((null map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-b (funcall function (svn-index-t n) t) svn-index-t)
                  (map-sparse-vector-loop-b (funcall function (svn-index-v n) (svn-value-v n)) svn-index-v)))
             ((eq :indexes map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-b (funcall function (svn-index-t n)) svn-index-t)
                  (map-sparse-vector-loop-b (funcall function (svn-index-v n)) svn-index-v)))
             (t
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-b (funcall function t) svn-index-t)
                  (map-sparse-vector-loop-b (funcall function (svn-value-v n)) svn-index-v)))))
        (if max
            (cond
             ((null map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-f2 (funcall function (svn-index-t n) t) svn-index-t)
                  (map-sparse-vector-loop-f2 (funcall function (svn-index-v n) (svn-value-v n)) svn-index-v)))
             ((eq :indexes map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-f2 (funcall function (svn-index-t n)) svn-index-t)
                  (map-sparse-vector-loop-f2 (funcall function (svn-index-v n)) svn-index-v)))
             (t
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-f2 (funcall function t) svn-index-t)
                  (map-sparse-vector-loop-f2 (funcall function (svn-value-v n)) svn-index-v))))
            (cond
             ((null map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-f (funcall function (svn-index-t n) t) svn-index-t)
                  (map-sparse-vector-loop-f (funcall function (svn-index-v n) (svn-value-v n)) svn-index-v)))
             ((eq :indexes map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-f (funcall function (svn-index-t n)) svn-index-t)
                  (map-sparse-vector-loop-f (funcall function (svn-index-v n)) svn-index-v)))
             (t
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-f (funcall function t) svn-index-t)
                  (map-sparse-vector-loop-f (funcall function (svn-value-v n)) svn-index-v))))))))

(defmacro sparse-vector-forward-iterator (form)
  `(lambda ()
     (if (eq stop (setf n (if (null n) (next-svn3 min) (next-svn2 n))))
         (setf n nil)
         ,form)))

(defmacro sparse-vector-backward-iterator (form)
  `(lambda ()
     (if (eq stop (setf n (if (null n) (prev-svn3 max) (prev-svn2 n))))
         (setf n nil)
         ,form)))

(defun make-sparse-vector-iterator (sparse-vector &key reverse min max)
  ;; returns an iterator function such that
  ;; the iterator returns (values t index value) for each entry on successive calls
  ;; the iterator returns nil when first called after the last entry
  ;; the iterator repeats the iteration if called after that
  (let ((stop (sparse-vector-entries sparse-vector))
        (n nil))
    (if reverse
        (if min
            (if (sparse-vector-boolean sparse-vector)
                (sparse-vector-backward-iterator
                 (let ((k (svn-index-t n))) (if (> min k) (setf n nil) (values t k t))))
                (sparse-vector-backward-iterator
                 (let ((k (svn-index-v n))) (if (> min k) (setf n nil) (values t k (svn-value-v n))))))
            (if (sparse-vector-boolean sparse-vector)
                (sparse-vector-backward-iterator (values t (svn-index-t n) t))
                (sparse-vector-backward-iterator (values t (svn-index-v n) (svn-value-v n)))))
        (if max
            (if (sparse-vector-boolean sparse-vector)
                (sparse-vector-forward-iterator
                 (let ((k (svn-index-t n))) (if (< max k) (setf n nil) (values t k t))))
                (sparse-vector-forward-iterator
                 (let ((k (svn-index-v n))) (if (< max k) (setf n nil) (values t k (svn-value-v n))))))
            (if (sparse-vector-boolean sparse-vector)
                (sparse-vector-forward-iterator (values t (svn-index-t n) t))
                (sparse-vector-forward-iterator (values t (svn-index-v n) (svn-value-v n))))))))

(defmacro with-sparse-vector-iterator ((name sparse-vector &rest options) &body body)
  (let ((iterator (gensym)))
    `(let ((,iterator (make-sparse-vector-iterator ,sparse-vector ,@options)))
       (macrolet ((,name () (list 'funcall ',iterator)))
         ,@body
         nil))))

(defmacro first-or-last-sparef (next-or-prev)
  `(let ((n (,next-or-prev stop)))
     (if (eq stop n)
         (values (sparse-vector-default-value sparse-vector) nil)
         (if (sparse-vector-boolean sparse-vector)
             (let ((index (svn-index-t n))) (values index index))
             (values (svn-value-v n) (svn-index-v n))))))

(defun first-sparef (sparse-vector)
  (let ((stop (sparse-vector-entries sparse-vector)))
    (first-or-last-sparef next-svn)))

(defun last-sparef (sparse-vector)
  (let ((stop (sparse-vector-entries sparse-vector)))
    (first-or-last-sparef prev-svn)))

;;; sparse-array4.lisp EOF
