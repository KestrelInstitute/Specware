;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes-sparse-array -*-
;;; File: sparse-vector.lisp
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

(in-package :mes-sparse-array)

;;; more implementation independent sparse-vector functions are defined in sparse-array.lisp

;;; ****s* mes-sparse-array/sparse-vector
;;; NAME
;;;   sparse-vector structure
;;;   sparse-vector type
;;; SOURCE

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
;;; ***

;;; ****f* mes-sparse-array/make-sparse-vector
;;; USAGE
;;;   (make-sparse-vector &key boolean default-value)
;;; RETURN VALUE
;;;   sparse-vector
;;; SOURCE

(defun make-sparse-vector (&key boolean default-value)
  (when boolean
    (unless (null default-value)
      (error "Default-value must be NIL for Boolean sparse-arrays.")))
  (make-sparse-vector0 default-value boolean))
;;; ***

;;; ****f* mes-sparse-array/sparse-vector-p
;;; USAGE
;;;   (sparse-vector-p x)
;;; RETURN VALUE
;;;   true if x if a sparse-vector, false otherwise
;;; SOURCE

      ;;sparse-vector-p is defined by the sparse-vector defstruct
;;; ***

;;; ****f* mes-sparse-array/sparse-vector-boolean
;;; USAGE
;;;   (sparse-vector-boolean sparse-vector)
;;; RETURN VALUE
;;;   true if x is a boolean sparse-vector, false otherwise
;;; SOURCE
      ;;sparse-vector-boolean is defined as a slot in the sparse-vector structure
;;; ***

;;; ****f* mes-sparse-array/sparse-vector-default-value
;;; USAGE
;;;   (sparse-vector-boolean sparse-vector)
;;; RETURN VALUE
;;;   the default-value for unstored entries of sparse-vector
;;; SOURCE
      ;;sparse-vector-default-value is defined as a slot in the sparse-vector structure
;;; ***

;;; ****f* mes-sparse-array/sparse-vector-count
;;; USAGE
;;;   (sparse-vector-count sparse-vector)
;;; RETURN VALUE
;;;   integer number of entries in sparse-vector
;;; SOURCE

      ;;sparse-vector-count is defined as a slot in the sparse-vector structure
;;; ***

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

;;; ****if* mes-sparse-array/svn-leaf?
;;; SOURCE

(defmacro svn-leaf? (svn)
  ;; leaf-nodes are distinguished from nonleaf-nodes by whether cdr is a cons
  `(consp (cdrc ,svn)))
;;; ***

;;; ****if* mes-sparse-array/leaf-svn-boolean?
;;; SOURCE

(defmacro leaf-svn-boolean? (svn)
  ;; type-T leaf-nodes are distinguished from type-V leaf-nodes by whether car is a cons
  `(not (consp (carc ,svn))))
;;; ***

;;; leaf-node constructors and accessors:

;;; ****if* mes-sparse-array/make-leaf-svn-t
;;; SOURCE

(defmacro make-leaf-svn-t (index prev next)
  `(cons ,index (cons ,prev ,next)))
;;; ***

;;; ****if* mes-sparse-array/make-leaf-svn-v
;;; SOURCE

(defmacro make-leaf-svn-v (index value prev next)
  `(cons (cons ,index ,value) (cons ,prev ,next)))
;;; ***

;;; ****if* mes-sparse-array/svn-index
;;; SOURCE

(defmacro svn-index (svn)
  (let ((v (gensym)))
    `(let ((,v (carc ,svn)))
       (if (consp ,v) (carc ,v) ,v))))
;;; ***

;;; ****if* mes-sparse-array/svn-value
;;; SOURCE

(defmacro svn-value (svn)
  (let ((v (gensym)))
    `(let ((,v (carc ,svn)))
       (if (consp ,v) (cdrc ,v) t))))
;;; ***

;;; ****if* mes-sparse-array/set-svn-value
;;; SOURCE

(defmacro set-svn-value (value svn)
  (let ((v (gensym)))
    `(let ((,v (carc ,svn)))
       (if (consp ,v) (setf (cdrc ,v) ,value) ,value))))
;;; ***

;;; ****if* mes-sparse-array/svn-index-t
;;; SOURCE

(defmacro svn-index-t (svn)
  `(carc ,svn))
;;; ***

;;; ****if* mes-sparse-array/svn-index-v
;;; SOURCE

(defmacro svn-index-v (svn)
  `(caarcc ,svn))
;;; ***

;;; ****if* mes-sparse-array/svn-value-v
;;; SOURCE

(defmacro svn-value-v (svn)
  `(cdarcc ,svn))
;;; ***

;;; ****if* mes-sparse-array/prev-svn
;;; SOURCE

(defmacro prev-svn (svn)
  `(cadrcc ,svn))
;;; ***

;;; ****if* mes-sparse-array/next-svn
;;; SOURCE

(defmacro next-svn (svn)
  `(cddrcc ,svn))
;;; ***

;;; nonleaf-node constructors and accessors:

;;; ****if* mes-sparse-array/make-nonleaf-svn
;;; SOURCE

(defmacro make-nonleaf-svn (bit branch1 branch0)
  `(cons (cons ,branch0 ,branch1) ,bit))
;;; ***

;;; ****if* mes-sparse-array/svn-bit
;;; SOURCE

(defmacro svn-bit (svn)
  `(the fixnum (cdrc ,svn)))
;;; ***

;;; ****if* mes-sparse-array/svn-branch-0
;;; SOURCE

(defmacro svn-branch-0 (svn)
  `(caarcc ,svn))
;;; ***

;;; ****if* mes-sparse-array/svn-branch-1
;;; SOURCE

(defmacro svn-branch-1 (svn)
  `(cdarcc ,svn))
;;; ***

;;; ****if* mes-sparse-array/initialize-sparse-vector-entries
;;; SOURCE

(defun initial-sparse-vector-entries (boolean)
  ;; create the initial doubly linked circular list of entries for fast traversals
  (let ((stop (if boolean
                  (make-leaf-svn-t -999999 nil nil)
                  (make-leaf-svn-v -999999 -999999 nil nil))))
    ;; stop is a dummy entry used as start and stop point for traversals
    (setf (prev-svn stop) stop)
    (setf (next-svn stop) stop)
    stop))
;;; ***

;;; ****if* mes-sparse-array/sparef1
;;; USAGE
;;;   (sparef1 sparse-vector index)
;;; NOTES
;;;   (sparef sparse-vector index) macroexpands to this
;;; SOURCE

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
                  (if (eql index (svn-index-t n)) index nil)
                  (if (eql index (svn-index-v n))
                      (svn-value-v n)
                      (sparse-vector-default-value sparse-vector))))))
       ((sparse-vector-boolean sparse-vector)
        (sv-search (svn-index-t n) index nil))
       (t
        (sv-search (svn-index-v n) (svn-value-v n) (sparse-vector-default-value sparse-vector)))))))

;;; ***

;;; ****f* mes-sparse-array/sparef
;;; USAGE
;;;   (sparef sparse-vector index)
;;;   (setf (sparef sparse-vector index) value)
;;;
;;;   (sparef sparse-matrix row-index column-index)
;;;   (setf (sparef sparse-matrix row-index column-index) value)
;;; SOURCE

(defmacro sparef (sparse-array index1 &optional index2)
  (if (null index2)
      `(sparef1 ,sparse-array ,index1)
      `(sparef2 ,sparse-array ,index1 ,index2)))
;;; ***

;;; ****if* mes-sparse-array/unlink-svn
;;; SOURCE

(definline unlink-svn (n)
  (let ((prev (prev-svn n))
        (next (next-svn n)))
    (setf (next-svn prev) next)
    (setf (prev-svn next) prev)
    (setf (next-svn n) nil)
    (setf (prev-svn n) nil)))
;;; ***

;;; ****if* mes-sparse-array/link-svn
;;; SOURCE

(definline link-svn (prev n next)
  (setf (prev-svn n) prev)
  (setf (next-svn n) next)
  (setf (next-svn prev) n)
  (setf (prev-svn next) n)
  n)
;;; ***

;;; ****if* mes-sparse-array/svn-min-leaf
;;; SOURCE

(definline svn-min-leaf (n)
  (loop
    (if (svn-leaf? n)
        (return n)
        (setf n (svn-branch-0 n)))))
;;; ***

;;; ****if* mes-sparse-array/svn-max-leaf
;;; SOURCE

(definline svn-max-leaf (n)
  (loop
    (if (svn-leaf? n)
        (return n)
        (setf n (svn-branch-1 n)))))
;;; ***

;;; ****if* mes-sparse-array/link-svn-after
;;; SOURCE

(definline link-svn-after (n prev)
  (setf prev (svn-max-leaf prev))
  (link-svn prev n (next-svn prev)))
;;; ***

;;; ****if* mes-sparse-array/link-svn-before
;;; SOURCE

(definline link-svn-before (n next)
  (setf next (svn-min-leaf next))
  (link-svn (prev-svn next) n next))
;;; ***

;;; ****if* mes-sparse-array/sparse-vector-setter
;;; USAGE
;;;   (sparse-vector-setter value sparse-vector index)
;;; SOURCE

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

;;; ***

;;; ****if* mes-sparse-array/next-svn1
;;; SOURCE

(defmacro next-svn1 (rel index &optional (svn-index 'svn-index))
  ;; find the first entry that is > or >= index
  ;; next-svn1 can be used to find the next node after index's is deleted
  (let ((n (gensym)))
    `(let ((k ,index)
           (,n (next-svn stop)))
       (loop
         (if (or (eq stop ,n) (,rel (,svn-index ,n) k))
             (return ,n)
             (setf ,n (next-svn ,n)))))))
;;; ***

;;; ****if* mes-sparse-array/prev-svn1
;;; SOURCE

(defmacro prev-svn1 (rel index &optional (svn-index 'svn-index))
  ;; find the last entry that is < or <= index
  ;; prev-svn1 can be used to find the previous node after index's is deleted
  (let ((n (gensym)))
    `(let ((k ,index)
           (,n (prev-svn stop)))
       (loop
         (if (or (eq stop ,n) (,rel (,svn-index ,n) k))
             (return ,n)
             (setf ,n (prev-svn ,n)))))))
;;; ***

;;; ****if* mes-sparse-array/next-svn2
;;; SOURCE

(defmacro next-svn2 (n &optional (svn-index 'svn-index))
  (cl:assert (symbolp n))
  `(or (next-svn ,n) (next-svn1 > (,svn-index ,n) ,svn-index)))
;;; ***

;;; ****if* mes-sparse-array/prev-svn2
;;; SOURCE

(defmacro prev-svn2 (n &optional (svn-index 'svn-index))
  (cl:assert (symbolp n))
  `(or (prev-svn ,n) (prev-svn1 < (,svn-index ,n) ,svn-index)))
;;; ***

;;; ****if* mes-sparse-array/next-svn3
;;; SOURCE

(defmacro next-svn3 (min &optional (svn-index 'svn-index))
  (cl:assert (symbolp min))
  `(if ,min (next-svn1 >= ,min ,svn-index) (next-svn stop)))
;;; ***

;;; ****if* mes-sparse-array/prev-svn3
;;; SOURCE

(defmacro prev-svn3 (max &optional (svn-index 'svn-index))
  (cl:assert (symbolp max))
  `(if ,max (prev-svn1 <= ,max ,svn-index) (prev-svn stop)))
;;; ***

;;; ****if* mes-sparse-array/map-sparse-vector-loop-f
;;; SOURCE

(defmacro map-sparse-vector-loop-f (form &optional (svn-index 'svn-index))
  `(let ((n (next-svn3 min ,svn-index)))
     (loop
       (if (eq stop n)
           (return nil)
           (progn ,form (setf n (next-svn2 n ,svn-index)))))))
;;; ***

;;; ****if* mes-sparse-array/map-sparse-vector-loop-b
;;; SOURCE

(defmacro map-sparse-vector-loop-b (form &optional (svn-index 'svn-index))
  `(let ((n (prev-svn3 max ,svn-index)))
     (loop
       (if (eq stop n)
           (return nil)
           (progn ,form (setf n (prev-svn2 n ,svn-index)))))))
;;; ***

;;; ****if* mes-sparse-array/map-sparse-vector-loop-f2
;;; SOURCE

(defmacro map-sparse-vector-loop-f2 (form &optional (svn-index 'svn-index))
  `(map-sparse-vector-loop-f (if (< max (,svn-index n)) (return nil) ,form) ,svn-index))
;;; ***

;;; ****if* mes-sparse-array/map-sparse-vector-loop-b2
;;; SOURCE

(defmacro map-sparse-vector-loop-b2 (form &optional (svn-index 'svn-index))
  `(map-sparse-vector-loop-b (if (> min (,svn-index n)) (return nil) ,form) ,svn-index))
;;; ***

;;; ****if* mes-sparse-array/map-sparse-vector0
;;; USAGE
;;;   (map-sparse-vector0 function sparse-vector reverse min max map)
;;; SOURCE

(defun map-sparse-vector0 (function sparse-vector reverse min max map)
  ;; always returns nil
  (let ((stop (sparse-vector-entries sparse-vector)))
    (if reverse
        (if min
            (cond
             ((null map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-b2 (let ((v (svn-index-t n))) (funcall function v v)) svn-index-t)
                  (map-sparse-vector-loop-b2 (funcall function (svn-value-v n) (svn-index-v n)) svn-index-v)))
             ((sparse-vector-boolean sparse-vector)
              (map-sparse-vector-loop-b2 (funcall function (svn-index-t n)) svn-index-t))
             ((eq :indexes map)
              (map-sparse-vector-loop-b2 (funcall function (svn-index-v n)) svn-index-v))
             (t
              (map-sparse-vector-loop-b2 (funcall function (svn-value-v n)) svn-index-v)))
            (cond
             ((null map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-b (let ((v (svn-index-t n))) (funcall function v v)) svn-index-t)
                  (map-sparse-vector-loop-b (funcall function (svn-value-v n) (svn-index-v n)) svn-index-v)))
             ((sparse-vector-boolean sparse-vector)
              (map-sparse-vector-loop-b (funcall function (svn-index-t n)) svn-index-t))
             ((eq :indexes map)
              (map-sparse-vector-loop-b (funcall function (svn-index-v n)) svn-index-v))
             (t
              (map-sparse-vector-loop-b (funcall function (svn-value-v n)) svn-index-v))))
        (if max
            (cond
             ((null map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-f2 (let ((v (svn-index-t n))) (funcall function v v)) svn-index-t)
                  (map-sparse-vector-loop-f2 (funcall function (svn-value-v n) (svn-index-v n)) svn-index-v)))
             ((sparse-vector-boolean sparse-vector)
              (map-sparse-vector-loop-f2 (funcall function (svn-index-t n)) svn-index-t))
             ((eq :indexes map)
              (map-sparse-vector-loop-f2 (funcall function (svn-index-v n)) svn-index-v))
             (t
              (map-sparse-vector-loop-f2 (funcall function (svn-value-v n)) svn-index-v)))
            (cond
             ((null map)
              (if (sparse-vector-boolean sparse-vector)
                  (map-sparse-vector-loop-f (let ((v (svn-index-t n))) (funcall function v v)) svn-index-t)
                  (map-sparse-vector-loop-f (funcall function (svn-value-v n) (svn-index-v n)) svn-index-v)))
             ((sparse-vector-boolean sparse-vector)
              (map-sparse-vector-loop-f (funcall function (svn-index-t n)) svn-index-t))
             ((eq :indexes map)
              (map-sparse-vector-loop-f (funcall function (svn-index-v n)) svn-index-v))
             (t
              (map-sparse-vector-loop-f (funcall function (svn-value-v n)) svn-index-v)))))))
;;; ***

;;; ****f* mes-sparse-array/map-sparse-vector
;;; USAGE
;;;   (map-sparse-vector function sparse-vector &key reverse min max)
;;; RETURN VALUE
;;;   nil
;;; DESCRIPTION
;;;   The map-sparse-vector function applies its unary-function argument to
;;;   each value (or index, if sparse-vector is boolean) in sparse-vector.
;;;
;;;   The function is applied only to values whose index is >= min
;;;   and <= max if they are specified.  If reverse is nil, the
;;;   function is applied to values in ascending order by index;
;;;   otherwise, the order is reversed.
;;; SOURCE

(definline map-sparse-vector (function sparse-vector &key reverse min max)
  (map-sparse-vector0 function sparse-vector reverse min max :values))
;;; ***

;;; ****f* mes-sparse-array/map-sparse-vector-with-indexes
;;; USAGE
;;;   (map-sparse-vector-with-indexes function sparse-vector &key reverse min max)
;;; RETURN VALUE
;;;   nil
;;; DESCRIPTION
;;;   The map-sparse-vector-with-indexes function is like map-sparse-vector,
;;;   but applies its binary-function argument to each value and index in sparse-vector.
;;; SEE ALSO
;;;   map-sparse-vector
;;; SOURCE

(definline map-sparse-vector-with-indexes (function sparse-vector &key reverse min max)
  (map-sparse-vector0 function sparse-vector reverse min max nil))
;;; ***

;;; ****f* mes-sparse-array/map-sparse-vector-indexes-only
;;; USAGE
;;;   (map-sparse-vector-indexes-only function sparse-vector &key reverse min max)
;;; RETURN VALUE
;;;   nil
;;; DESCRIPTION
;;;   The map-sparse-vector-indexes-only function is like map-sparse-vector,
;;;   but applies its unary-function argument to each index in sparse-vector.
;;;   map-sparse-vector and map-sparse-vector-indexes-only operate identically
;;;   on boolean sparse-vectors.
;;; SEE ALSO
;;;   map-sparse-vector
;;; SOURCE

(definline map-sparse-vector-indexes-only (function sparse-vector &key reverse min max)
  (map-sparse-vector0 function sparse-vector reverse min max :indexes))
;;; ***

;;; ****if* mes-sparse-array/sparse-vector-forward-iterator
;;; SOURCE

(defmacro sparse-vector-forward-iterator (form)
  `(lambda ()
     (if (eq stop (setf n (if (null n) (next-svn3 min) (next-svn2 n))))
         (values (sparse-vector-default-value sparse-vector) (setf n nil))
         ,form)))
;;; ***

;;; ****if* mes-sparse-array/sparse-vector-backward-iterator
;;; SOURCE

(defmacro sparse-vector-backward-iterator (form)
  `(lambda ()
     (if (eq stop (setf n (if (null n) (prev-svn3 max) (prev-svn2 n))))
         (values (sparse-vector-default-value sparse-vector) (setf n nil))
         ,form)))
;;; ***

;;; ****if* mes-sparse-array/make-sparse-vector-iterator
;;; USAGE
;;;   (make-sparse-vector-iterator sparse-vector &key reverse min max)
;;; SOURCE

(defun make-sparse-vector-iterator (sparse-vector &key reverse min max)
  ;; returns an iterator function such that
  ;; the iterator returns (values value index) for each entry on successive calls
  ;; the iterator returns (values default-value nil) when first called after the last entry
  ;; the iterator repeats the iteration if called after that
  (let ((stop (sparse-vector-entries sparse-vector))
        (n nil))
    (if reverse
        (if min
            (if (sparse-vector-boolean sparse-vector)
                (sparse-vector-backward-iterator
                 (let ((k (svn-index-t n)))
                   (if (> min k)
                       (values (sparse-vector-default-value sparse-vector) (setf n nil))
                       (values k k))))
                (sparse-vector-backward-iterator
                 (let ((k (svn-index-v n)))
                   (if (> min k)
                       (values (sparse-vector-default-value sparse-vector) (setf n nil))
                       (values (svn-value-v n) k)))))
            (if (sparse-vector-boolean sparse-vector)
                (sparse-vector-backward-iterator (let ((k (svn-index-t n))) (values k k)))
                (sparse-vector-backward-iterator (values (svn-value-v n) (svn-index-v n)))))
        (if max
            (if (sparse-vector-boolean sparse-vector)
                (sparse-vector-forward-iterator
                 (let ((k (svn-index-t n)))
                   (if (< max k)
                       (values (sparse-vector-default-value sparse-vector) (setf n nil))
                       (values k k))))
                (sparse-vector-forward-iterator
                 (let ((k (svn-index-v n)))
                   (if (< max k)
                       (values (sparse-vector-default-value sparse-vector) (setf n nil))
                       (values (svn-value-v n) k)))))
            (if (sparse-vector-boolean sparse-vector)
                (sparse-vector-forward-iterator (let ((k (svn-index-t n))) (values k k)))
                (sparse-vector-forward-iterator (values (svn-value-v n) (svn-index-v n))))))))
;;; ***

;;; ****f* mes-sparse-array/with-sparse-vector-iterator
;;; USAGE
;;;   (with-sparse-vector-iterator (name sparse-vector &key reverse min max)
;;;     form*)
;;; SEE ALSO
;;;   map-sparse-vector-with-indexes
;;; SOURCE

(defmacro with-sparse-vector-iterator ((name sparse-vector &rest options) &body body)
  (let ((iterator (gensym)))
    `(let ((,iterator (make-sparse-vector-iterator ,sparse-vector ,@options)))
       (macrolet ((,name () (list 'funcall ',iterator)))
         ,@body))))
;;; ***

;;; ****if* mes-sparse-array/first-or-last-sparef
;;; SOURCE

(defmacro first-or-last-sparef (next-or-prev)
  `(let ((n (,next-or-prev stop)))
     (if (eq stop n)
         (values (sparse-vector-default-value sparse-vector) nil)
         (if (sparse-vector-boolean sparse-vector)
             (let ((index (svn-index-t n))) (values index index))
             (values (svn-value-v n) (svn-index-v n))))))
;;; ***

;;; ****f* mes-sparse-array/first-sparef
;;; USAGE
;;;   (first-sparef sparse-vector)
;;; RETURN VALUE
;;;   (values (sparef sparse-vector first-index) first-index) or
;;;   (values default-value nil) if sparse-vector is empty
;;; SEE ALSO
;;;   pop-first-sparef
;;; SOURCE

(defun first-sparef (sparse-vector)
  (let ((stop (sparse-vector-entries sparse-vector)))
    (first-or-last-sparef next-svn)))
;;; ***

;;; ****f* mes-sparse-array/last-sparef
;;; USAGE
;;;   (last-sparef sparse-vector)
;;; RETURN VALUE
;;;   (values (sparef sparse-vector last-index) last-index) or
;;;   (values default-value nil) if sparse-vector is empty
;;; SEE ALSO
;;;   pop-last-sparef
;;; SOURCE

(defun last-sparef (sparse-vector)
  (let ((stop (sparse-vector-entries sparse-vector)))
    (first-or-last-sparef prev-svn)))
;;; ***

;;; ****f* mes-sparse-array/pop-first-sparef
;;; USAGE
;;;   (pop-first-sparef sparse-vector)
;;; RETURN VALUE
;;;   (values (sparef sparse-vector first-index) first-index) or
;;;   (values default-value nil) if sparse-vector is empty
;;; SIDE EFFECTS
;;;   removes it from sparse-vector
;;; SEE ALSO
;;;   first-sparef
;;; SOURCE

(defun pop-first-sparef (sparse-vector)
  (multiple-value-bind (value index) (first-sparef sparse-vector)
    (when index
      (sparse-vector-setter (sparse-vector-default-value sparse-vector) sparse-vector index))
    (values value index)))
;;; ***

;;; ****f* mes-sparse-array/pop-last-sparef
;;; USAGE
;;;   (pop-last-sparef sparse-vector)
;;; RETURN VALUE
;;;   (values (sparef sparse-vector last-index) last-index) or
;;;   (values default-value nil) if sparse-vector is empty
;;; SIDE EFFECTS
;;;   removes it from sparse-vector
;;; SEE ALSO
;;;   last-sparef
;;; SOURCE

(defun pop-last-sparef (sparse-vector)
  (multiple-value-bind (value index) (last-sparef sparse-vector)
    (when index
      (sparse-vector-setter (sparse-vector-default-value sparse-vector) sparse-vector index))
    (values value index)))
;;; ***

;;; ****if* mes-sparse-array/print-sparse-vector3
;;; USAGE
;;;   (print-sparse-vector3 sparse-vector stream depth)
;;; NOTES
;;;   specified as print-function in the sparse-vector defstruct
;;; SOURCE

(defun print-sparse-vector3 (sparse-vector stream depth)
  (declare (ignore depth))
  (print-unreadable-object (sparse-vector stream :type t :identity t)
    (princ (sparse-vector-count sparse-vector) stream)))
;;; ***

;;; sparse-vector.lisp EOF
