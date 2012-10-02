;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: ordered-sets.lisp
;;; Copyright (c) 1999-2002 Mark E. Stickel
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
(eval-when (:compile-toplevel :load-toplevel :execute)
  (export
   '(ordered-set make-ordered-set ordered-set-p
     oset-insert oset-insert-key
     oset-member oset-delete
     oset-find-key oset-delete-key
     oset-first oset-delete-first 
     oset-last oset-delete-last
     oset-find-if oset-delete-if
     oset-delete-all-if oset-delete-all
     mapc-oset mapcar-oset mapnconc-oset
     oset-elements oset-size
     oset-first* oset-last* oset-next* oset-prev*
     oset-member* oset-find-key* oset-delete* oset-element*
     oset-equal-p oset-subset-p oset-intersection oset-union oset-difference
     )))

;;; operations on sets where each element has a unique key
;;; and keys are totally ordered
;;;
;;; ordered sets use the red-black tree algorithms described in
;;; Cormen, Leiserson, and Rivest's "Introduction to Algorithms"
;;;
;;; stickel@ai.sri.com 2002-06-14

(defparameter oset-default-key nil)			;nil is interpreted as #'identity
(defparameter oset-default-test nil)			;nil is interpreted as #'<
(defparameter oset-default-make-element 'no-oset-make-element)

(defstruct (ordered-set
            (:constructor make-ordered-set (&key (key oset-default-key)
                                                 (test oset-default-test)
                                                 (make-element oset-default-make-element)))
            (:print-function print-ordered-set3)
            (:copier nil))
  (key oset-default-key :read-only t)			;function to get key from element
  (test oset-default-test :read-only t)			;less-than comparison of keys
  (make-element oset-default-make-element :read-only t)	;make new element from key, for only insert-key
  (root nil)
  (size 0 :type integer))

(defstruct (oset-node
            (:constructor make-oset-node (element* parent*))
            (:print-function print-oset-node3)
            (:conc-name :oset-)
            (:copier nil))
  (element* nil :read-only t)
  (left* nil)
  (right* nil)
  parent*
  color*)

(definline assert-ordered-set-p (x)
  (unless (ordered-set-p x)
    (error "~S is not an ordered set." x)))

(definline oset-leftmost* (node)
  (let (parent)
    (loop
      (when (null (setf node (oset-left* (setf parent node))))
        (return parent)))))

(definline oset-rightmost* (node)
  (let (parent)
    (loop
      (when (null (setf node (oset-right* (setf parent node))))
        (return parent)))))

(defmacro funcall-key (x)
  ;; avoid funcall if key is nil
  `(if (null key) ,x (funcall key ,x)))

(defmacro funcall-test (x y)
  ;; avoid funcall if test is nil
  `(if (null test) (< ,x ,y) (funcall test ,x ,y)))

(defmacro oset-mapper (action)
  `(if reverse
       (let ((node (oset-last* oset max)))
         (and (not (null node))
              (let ((key (and (neq :none min) (ordered-set-key oset)))
                    (test (and (neq :none min) (ordered-set-test oset)))
                    (result nil) result-last element)
                (declare (ignorable result-last))
                (loop
                  (setf element (oset-element* node))
                  (when (and (neq :none min) (funcall-test (funcall-key element) min))
                    (return result))
                  ,action
                  (when (null (setf node (oset-prev* node)))
                    (return result))))))
       (let ((node (oset-first* oset min)))
         (and (not (null node))
              (let ((key (and (neq :none max) (ordered-set-key oset)))
                    (test (and (neq :none max) (ordered-set-test oset)))
                    (result nil) result-last element)
                (declare (ignorable result-last))
                (loop
                  (setf element (oset-element* node))
                  (when (and (neq :none max) (funcall-test max (funcall-key element)))
                    (return result))
                  ,action
                  (when (null (setf node (oset-next* node)))
                    (return result))))))))

(defun oset-insert (element oset)
  "(oset-insert element oset) inserts element into oset and returns t or returns nil if it was already in oset."
  (let* ((key (ordered-set-key oset))
         (test (ordered-set-test oset))
         (node (ordered-set-root oset))
         (element-key (funcall-key element)))
    (cond
     ((null node)
      (setf (ordered-set-size oset) 1)
      (setf (oset-color* (setf (ordered-set-root oset) (make-oset-node element nil))) 'black)
      t)
     (t
      (loop
        (let ((node-key (funcall-key (oset-element* node))))
          (cond
           ((funcall-test element-key node-key)
            (let ((node1 (oset-left* node)))
              (cond
               ((null node1)
                (incf (ordered-set-size oset))
                (rb-insert-fixup oset (setf (oset-left* node) (make-oset-node element node)))
                (return t))
               (t
                (setf node node1)))))
           ((funcall-test node-key element-key)
            (let ((node1 (oset-right* node)))
              (cond
               ((null node1)
                (incf (ordered-set-size oset))
                (rb-insert-fixup oset (setf (oset-right* node) (make-oset-node element node)))
                (return t))
               (t
                (setf node node1)))))
           (t
            (assert (eql element (oset-element* node)))
            (return nil)))))))))

(defun oset-insert-key (element-key oset)
  ;; creates an element from the key
  (let* ((key (ordered-set-key oset))
         (test (ordered-set-test oset))
         (node (ordered-set-root oset))
         element)
    (cond
     ((null node)
      (setf element (funcall (ordered-set-make-element oset) element-key))
      (setf (ordered-set-size oset) 1)
      (setf (oset-color* (setf (ordered-set-root oset) (make-oset-node element nil))) 'black)
      (values element t))
     (t
      (loop
        (let ((node-key (funcall-key (oset-element* node))))
          (cond
           ((funcall-test element-key node-key)
            (let ((node1 (oset-left* node)))
              (cond
               ((null node1)
                (setf element (funcall (ordered-set-make-element oset) element-key))
                (incf (ordered-set-size oset))
                (rb-insert-fixup oset (setf (oset-left* node) (make-oset-node element node)))
                (return (values element t)))
               (t
                (setf node node1)))))
           ((funcall-test node-key element-key)
            (let ((node1 (oset-right* node)))
              (cond
               ((null node1)
                (setf element (funcall (ordered-set-make-element oset) element-key))
                (incf (ordered-set-size oset))
                (rb-insert-fixup oset (setf (oset-right* node) (make-oset-node element node)))
                (return (values element t)))
               (t
                (setf node node1)))))
           (t
            (return (values (oset-element* node) nil))))))))))

(defun oset-member (element oset)
  "(oset-member element oset) returns t if element is in oset or returns nil if not."
  (not (null (oset-member* element oset))))

(defun oset-delete (element oset)
  "(oset-delete element oset) deletes element from oset and returns t or returns nil if it was not in oset."
  (let ((node (oset-member* element oset)))
    (and (not (null node)) (progn (oset-delete* node oset) t))))

(defun oset-first (oset &optional (min :none))
  "(oset-first oset) returns the first element in oset or returns nil if oset is empty."
  (let ((node (oset-first* oset min)))
    (if (not (null node))
        (values (oset-element* node) t)
        (values nil nil))))

(defun oset-delete-first (oset &optional (min :none))
  "(oset-delete-first oset) deletes and returns the first element in oset or returns nil if oset is empty."
  (let ((node (oset-first* oset min)))
    (if (not (null node))
        (values (prog1 (oset-element* node) (oset-delete* node oset)) t)
        (values nil nil))))

(defun oset-last (oset &optional (max :none))
  "(oset-last oset) returns the last element in oset or returns nil if oset is empty."
  (let ((node (oset-last* oset max)))
    (if (not (null node))
        (values (oset-element* node) t)
        (values nil nil))))

(defun oset-delete-last (oset &optional (max :none))
  "(oset-delete-last oset) deletes and returns the last element in oset or returns nil if oset is empty."
  (let ((node (oset-last* oset max)))
    (if (not (null node))
        (values (prog1 (oset-element* node) (oset-delete* node oset)) t)
        (values nil nil))))

(defun oset-find-if (pred oset &key (min :none) (max :none) reverse)
  "(oset-find-if pred oset &key min max reverse) returns the first/last element bounded by min and max in oset for which pred is true or returns nil if there is no such element."
  (oset-mapper
   (when (funcall pred element)
     (return-from oset-find-if (values element t))))
  (values nil nil))

(defun oset-delete-if (pred oset &key (min :none) (max :none) reverse)
  "(oset-delete-if pred oset &key min max reverse) deletes and returns the first/last element bounded by min and max in oset for which pred is true or returns nil if there is no such element."
  (oset-mapper
   (when (funcall pred element)
     (oset-delete* node oset)
     (return-from oset-delete-if (values element t))))
  (values nil nil))

(defun oset-delete-all-if (pred oset &key (min :none) (max :none) reverse count)
  (when (or (null count) (plusp count))
    (oset-mapper
     (when (funcall pred element)
       (oset-delete* node oset)
       (unless (or (null count) (plusp (decf count)))
         (return)))))
  oset)

(defun oset-delete-all (oset)
  "(oset-delete-all oset) deletes all elements from oset leaving it empty."
  (setf (ordered-set-size oset) 0)
  (setf (ordered-set-root oset) nil)
  oset)

(defun mapc-oset (function oset &key (min :none) (max :none) reverse)
  "(mapc-oset function oset &key min max reverse) applies function to each element of oset and returns oset."
  (oset-mapper (funcall function element))
  oset)

(defun mapcar-oset (function oset &key (min :none) (max :none) reverse)
  "(mapcar-oset function oset &key min max reverse) applies function to each element of oset and returns a list of the results."
  (oset-mapper (collect (funcall function element) result)))

(defun mapnconc-oset (function oset &key (min :none) (max :none) reverse)
  "(mapnconc-oset function oset &key min max reverse) applies function to each element of oset and returns the result of nconcing the results."
  (oset-mapper (ncollect (funcall function element) result)))

(defun oset-elements (oset &key (min :none) (max :none) reverse)
  "(oset-elements oset &key min max reverse) returns the elements of oset as a list like (mapcar-oset #'identity oset ...)."
  (oset-mapper (collect element result)))

(defun oset-size (oset)
  "(oset-size oset) returns the number of elements in oset."
  (ordered-set-size oset))

;;; operations on oset nodes
;;;
;;; oset-first* + oset-next* + oset-element* enable forward iteration
;;; oset-last* + oset-prev* + oset-element* enable backward iteration

(defun oset-first* (oset &optional (min :none))
  "(oset-first* oset) returns the first node in oset or returns nil if oset is empty."
  (let ((node (ordered-set-root oset)))
    (and (not (null node))
         (if (eq :none min)
             (oset-leftmost* node)
             (let ((key (ordered-set-key oset))
                   (test (ordered-set-test oset))
                   (node1 nil))
               ;; return the node whose key is the minimum that is greater than
               ;; or equal to min or returns nil if there is no such node
               (loop
                 (if (null node)
                     (return node1)
                     (let ((node-key (funcall-key (oset-element* node))))
                       (cond
                        ((funcall-test min node-key)
                         (setf node (oset-left* (setf node1 node))))
                        ((funcall-test node-key min)
                         (setf node (oset-right* node)))
                        (t
                         (return node)))))))))))

(defun oset-last* (oset &optional (max :none))
  "(oset-last* oset) returns the last node in oset or returns nil if oset is empty."
  (let ((node (ordered-set-root oset)))
    (and (not (null node))
         (if (eq :none max)
             (oset-rightmost* node)
             (let ((key (ordered-set-key oset))
                   (test (ordered-set-test oset))
                   (node1 nil))
               ;; return the node whose key is the maximum that is less than
               ;; or equal to max or returns nil if there is no such node
               (loop
                 (if (null node)
                     (return node1)
                     (let ((node-key (funcall-key (oset-element* node))))
                       (cond
                        ((funcall-test max node-key)
                         (setf node (oset-left* node)))
                        ((funcall-test node-key max)
                         (setf node (oset-right* (setf node1 node))))
                        (t
                         (return node)))))))))))

(defun oset-next* (node)
  "(oset-next* node) returns the node after node or returns nil if there is no successor."
  (let ((node1 (oset-right* node)))
    (cond
     ((null node1)
      (loop
        (when (or (null (setf node (oset-parent* (setf node1 node))))
                  (eq node1 (oset-left* node)))
          (return node))))
     ((eq :deleted node1)				;deleted node has :deleted in right slot
      (let* ((oset (oset-parent* node))			;deleted node has oset in parent slot
             (key (ordered-set-key oset)))
        (oset-first* oset (funcall-key (oset-element* node)))))
     (t
      (oset-leftmost* node1)))))

(defun oset-prev* (node)
  "(oset-prev* node) returns the node before node or returns nil if there is no predecessor."
  (let ((node1 (oset-left* node)))
    (cond
     ((null node1)
      (loop
        (when (or (null (setf node (oset-parent* (setf node1 node))))
                  (eq node1 (oset-right* node)))
          (return node))))
     ((eq :deleted node1)				;deleted node has :deleted in left slot
      (let* ((oset (oset-parent* node))			;deleted node has oset in parent slot
             (key (ordered-set-key oset)))
        (oset-last* oset (funcall-key (oset-element* node)))))
     (t
      (oset-rightmost* node1)))))

(definline oset-find-key0 (element-key oset node key)
  (let ((test (ordered-set-test oset)))
    (loop
      (let ((node-key (funcall-key (oset-element* node))))
        (cond
         ((funcall-test element-key node-key)
          (when (null (setf node (oset-left* node)))
            (return nil)))
         ((funcall-test node-key element-key)
          (when (null (setf node (oset-right* node)))
            (return nil)))
         (t
          (return node)))))))

(defun oset-member* (element oset)
  "(oset-member* element oset) returns the node in oset that contains element or nil if there is no such node."
  (let ((node (ordered-set-root oset)))
    (and (not (null node))
         (unless (null (setf node (let ((key (ordered-set-key oset)))
                                    (oset-find-key0 (funcall-key element) oset node key))))
           (assert (eql element (oset-element* node)))
           node))))

(definline oset-find-key** (element-key oset)
  (let ((node (ordered-set-root oset)))
    (and (not (null node)) (oset-find-key0 element-key oset node (ordered-set-key oset)))))

(defun oset-find-key* (element-key oset)
  "(oset-find-key* key oset) returns the node in oset that contains an element whose key is key or nil if there is no such node."
  (oset-find-key** element-key oset))

(defun oset-find-key (element-key oset)
  "(oset-find-key key oset) returns the element in oset whose key is key or returns nil if there is no such element."
  (let ((node (oset-find-key** element-key oset)))
    (if (not (null node))
        (values (oset-element* node) t)
        (values nil nil))))

(defun oset-delete-key (element-key oset)
  "(oset-delete-key key oset) is like (oset-find-key key oset) except it also deletes the element whose key is key if present."
  (let ((node (oset-find-key** element-key oset)))
    (if (not (null node))
        (values (prog1 (oset-element* node) (oset-delete* node oset)) t)
        (values nil nil))))

(defun oset-delete* (node oset)
  "(oset-delete* node oset) deletes node from oset and returns oset."
  (decf (ordered-set-size oset))
  (rb-delete oset node))

(defun oset-equal-p (oset1 oset2)
  ;; tests if oset1 and oset2 have the same elements (using eql)
  ;; they may be in different order if different key or test are used for oset1 and oset2
  (or (eq oset1 oset2)
      (and (eql (oset-size oset1) (oset-size oset2))
           (do ((n1 (oset-first* oset1) (oset-next* n1)))
               ((null n1)
                t)
             (unless (oset-member* (oset-element* n1) oset2)
               (return nil))))))

(defun oset-subset-p (oset1 oset2)
  ;; tests if every element of oset1 is an element of oset2 (using eql)
  ;; they may be in different order if different key or test are used for oset1 and oset2
  (or (eq oset1 oset2)
      (and (<= (oset-size oset1) (oset-size oset2))
           (do ((n1 (oset-first* oset1) (oset-next* n1)))
               ((null n1)
                t)
             (unless (oset-member* (oset-element* n1) oset2)
               (return nil))))))

(defun oset-intersection (oset1 oset2)
  (do ((n1 (oset-first* oset1) (oset-next* n1)))
      ((null n1)
       oset1)
    (unless (oset-member* (oset-element* n1) oset2)
      (oset-delete* n1 oset1))))

(defun oset-union (oset1 oset2)
  (mapc-oset (lambda (element) (oset-insert element oset1)) oset2)
  oset1)

(defun oset-difference (oset1 oset2)
  (mapc-oset (lambda (element) (oset-delete element oset1)) oset2)
  oset1)

(defun left-rotate (oset x)
  (let ((y (oset-right* x)))
    (let ((ly (oset-left* y)))
      (setf (oset-right* x) ly)
      (unless (null ly)
        (setf (oset-parent* ly) x)))
    (let ((px (oset-parent* x)))
      (setf (oset-parent* y) px)
      (if (null px)
          (setf (ordered-set-root oset) y)
          (if (eq x (oset-left* px)) (setf (oset-left* px) y) (setf (oset-right* px) y))))
    (setf (oset-left* y) x)
    (setf (oset-parent* x) y)))

(defun right-rotate (oset y)
  (let ((x (oset-left* y)))
    (let ((rx (oset-right* x)))
      (setf (oset-left* y) rx)
      (unless (null rx)
        (setf (oset-parent* rx) y)))
    (let ((py (oset-parent* y)))
      (setf (oset-parent* x) py)
      (if (null py)
          (setf (ordered-set-root oset) x)
          (if (eq y (oset-left* py)) (setf (oset-left* py) x) (setf (oset-right* py) x))))
    (setf (oset-right* x) y)
    (setf (oset-parent* y) x)))

(defun rb-insert-fixup (oset x)
  (setf (oset-color* x) 'red)
  (loop
    (cond
     ((and (neq x (ordered-set-root oset)) (eq 'red (oset-color* (oset-parent* x))))
      (let* ((px (oset-parent* x)) (ppx (oset-parent* px)))
        (if (eq px (oset-left* ppx))
            (let ((y (oset-right* ppx)))
              (if (and (not (null y)) (eq 'red (oset-color* y)))
                  (setf (oset-color* y) 'black x ppx)
                  (progn
                    (when (eq x (oset-right* px))
                      (setf x px)
                      (left-rotate oset x)
                      (setf px (oset-parent* x) ppx (oset-parent* px)))
                    (right-rotate oset ppx))))
            (let ((y (oset-left* ppx)))
              (if (and (not (null y)) (eq 'red (oset-color* y)))
                  (setf (oset-color* y) 'black x ppx)
                  (progn
                    (when (eq x (oset-left* px))
                      (setf x px)
                      (right-rotate oset x)
                      (setf px (oset-parent* x) ppx (oset-parent* px)))
                    (left-rotate oset ppx)))))
        (setf (oset-color* px) 'black)
        (setf (oset-color* ppx) 'red)))
     (t
      (return))))
  (setf (oset-color* (ordered-set-root oset)) 'black))

(defun rb-delete (oset z)
  (let (x)
    (cond
     ((null (setf x (oset-left* z)))		;z has no left child, maybe no right child x
      (let ((pz (oset-parent* z)))
        (setf x (oset-right* z))
        (unless (null x)
          (setf (oset-parent* x) pz))
        (if (null pz)
            (setf (ordered-set-root oset) x)
            (if (eq z (oset-left* pz)) (setf (oset-left* pz) x) (setf (oset-right* pz) x)))
        (unless (and (null pz) (null x))	;oset is empty
          (when (eq 'black (oset-color* z))
            (rb-delete-fixup oset x pz)))))
     ((null (oset-right* z))			;z has no right child, but there is left child x
      (let ((pz (oset-parent* z)))
        (setf (oset-parent* x) pz)
        (if (null pz)
            (setf (ordered-set-root oset) x)
            (if (eq z (oset-left* pz)) (setf (oset-left* pz) x) (setf (oset-right* pz) x)))
        (when (eq 'black (oset-color* z))
          (rb-delete-fixup oset x pz))))
     (t						;z has two children
      (let* ((y (oset-next* z))
             (py (oset-parent* y))
             (cy (oset-color* y)))
        ;; splice out y, which has no left child
        (setf x (oset-right* y))
        (unless (null x)
          (setf (oset-parent* x) py))
        (if (null py)
            (setf (ordered-set-root oset) x)
            (if (eq y (oset-left* py)) (setf (oset-left* py) x) (setf (oset-right* py) x)))
        ;; replace z in rb-tree by y instead of doing (setf (oset-element* z) (oset-element* y))
        (let ((pz (oset-parent* z)))
          (let ((v (oset-left* z)))
            (setf (oset-left* y) v)
            (unless (null v)
              (setf (oset-parent* v) y)))
          (let ((v (oset-right* z)))
            (setf (oset-right* y) v)
            (unless (null v)
              (setf (oset-parent* v) y)))
          (setf (oset-parent* y) pz)
          (if (null pz)
              (setf (ordered-set-root oset) y)
              (if (eq z (oset-left* pz)) (setf (oset-left* pz) y) (setf (oset-right* pz) y)))
          (setf (oset-color* y) (oset-color* z)))
        (when (eq 'black cy)
          (rb-delete-fixup oset x (if (eq py z) y py)))))))
  ;; fix z so that successor and predecessor can continue from it
  (setf (oset-left* z) :deleted)
  (setf (oset-right* z) :deleted)
  (setf (oset-parent* z) oset))			;returns oset

(defmacro oset-color2 (node)
  (let ((n (gensym)))
    `(let ((,n ,node))
       (if (null ,n) 'black (oset-color* ,n)))))

(defun rb-delete-fixup (oset x px)
  (loop
    (cond
     ((and (neq x (ordered-set-root oset)) (eq 'black (oset-color2 x)))
      (if (eq x (oset-left* px))
          (let ((w (oset-right* px)))
            (when (eq 'red (oset-color* w))
              (setf (oset-color* w) 'black)
              (setf (oset-color* px) 'red)
              (left-rotate oset px)
              (setf w (oset-right* px)))
            (if (and (eq 'black (oset-color2 (oset-left* w)))
                     (eq 'black (oset-color2 (oset-right* w))))
                (progn
                  (setf (oset-color* w) 'red)
                  (setf x px px (oset-parent* x)))
                (progn
                  (when (eq 'black (oset-color2 (oset-right* w)))
                    (setf (oset-color* (oset-left* w)) 'black)
                    (setf (oset-color* w) 'red)
                    (right-rotate oset w)
                    (setf w (oset-right* px)))
                  (setf (oset-color* w) (oset-color* px))
                  (setf (oset-color* px) 'black)
                  (setf (oset-color* (oset-right* w)) 'black)
                  (left-rotate oset px)
                  (setf x (ordered-set-root oset)))))
          (let ((w (oset-left* px)))
            (when (eq 'red (oset-color* w))
              (setf (oset-color* w) 'black)
              (setf (oset-color* px) 'red)
              (right-rotate oset px)
              (setf w (oset-left* px)))
            (if (and (eq 'black (oset-color2 (oset-left* w)))
                     (eq 'black (oset-color2 (oset-right* w))))
                (progn
                  (setf (oset-color* w) 'red)
                  (setf x px px (oset-parent* x)))
                (progn
                  (when (eq 'black (oset-color2 (oset-left* w)))
                    (setf (oset-color* (oset-right* w)) 'black)
                    (setf (oset-color* w) 'red)
                    (left-rotate oset w)
                    (setf w (oset-left* px)))
                  (setf (oset-color* w) (oset-color* px))
                  (setf (oset-color* px) 'black)
                  (setf (oset-color* (oset-left* w)) 'black)
                  (right-rotate oset px)
                  (setf x (ordered-set-root oset)))))))
     (t
      (return))))
  (setf (oset-color* x) 'black))

(defun oset-height (oset)
  (labels
    ((HEIGHT (node)
       (if (null node) 0 (1+ (max (height (oset-left* node)) (height (oset-right* node)))))))
     (height (ordered-set-root oset))))

(defun oset-proper-red-black-tree-p (oset)
  (let ((black-height nil))
    (labels
      ((TRAVERSE (node bh)
         (if (null node)
             (if black-height
                 (eql black-height bh)
                 (setf black-height bh))
             (let* ((black (ecase (oset-color* node) (black t) (red nil)))
                    (bh1 (if black (1+ bh) bh))
                    (l (oset-left* node))
                    (r (oset-right* node)))
               (and (or black
                        (and (or (null l) (eq 'black (oset-color* l)))
                             (or (null r) (eq 'black (oset-color* r)))))
                    (traverse l bh1)
                    (traverse r bh1))))))
      (and (traverse (ordered-set-root oset) 0) black-height))))

(defun no-oset-make-element (element-key)
  (declare (ignore element-key))
  (error "No make-element function was specified for this ordered set."))

(defun print-ordered-set3 (oset stream depth)
  (declare (ignore depth))
  (print-unreadable-object (oset stream :type t :identity t)
    (princ "size " stream)
    (princ (ordered-set-size oset) stream)))

(defun print-oset-node3 (node stream depth)
  (declare (ignore depth))
  (print-unreadable-object (node stream :type t :identity t)))

(defun oset-test1 ()
  ;; test insertion
  (let ((oset (make-ordered-set))
        (result0 nil)
        (result1 nil))
    (loop
      (let ((x (random 5000)))
        (pushnew x result0)
        (oset-insert x oset)
        (assert (oset-proper-red-black-tree-p oset))
        (when (eql 2000 (oset-size oset))
          (return))))
    (setf result0 (sort result0 #'<))
    (setf result1 (oset-elements oset))
    (assert (equal result0 result1))
    oset))

(defun oset-test2 ()
  ;; test deletion (and insertion)
  (let* ((oset (oset-test1))
         (l (nreverse (oset-elements oset :reverse t))))
    (loop
      (when (null l)
        (return oset))
      (let ((x (nth (random (oset-size oset)) l)))
        (setf l (delete x l))
        (oset-delete x oset)
        (assert (oset-proper-red-black-tree-p oset))
        (assert (equal l (oset-elements oset)))))))

(defun oset-test3 ()
  ;; test insertion during traversal
  (let ((oset (make-ordered-set))
        (result0 nil) result0-last
        (result1 nil)
        (result2 nil))
    (dotimes (i 100)
      (collect i result0)
      (when (evenp i)
        (oset-insert i oset)))
    (setf result1 (mapnconc-oset (lambda (x)
                                   (when (evenp x)
                                     (oset-insert (1+ x) oset))
                                   (list x))
                                 oset))
    (setf result2 (mapnconc-oset #'list oset))
    (assert (oset-proper-red-black-tree-p oset))
    (assert (equal result0 result1))
    (assert (equal result0 result2))
    result0))

(defun oset-test4 ()
  ;; test deletion during traversal
  (let ((oset (make-ordered-set)))
    (dotimes (i 10)
      (oset-insert i oset))
    (assert (equal '(0 2 4 6 8)
                   (mapnconc-oset (lambda (x)
                                    (cond
                                     ((oddp x)
                                      (oset-delete x oset)
                                      nil)
                                     (t
                                      (list x))))
                                  oset)))
    (dotimes (i 10)
      (oset-insert i oset))
    (assert (equal '(8 6 4 2 0)
                   (mapnconc-oset (lambda (x)
                                    (cond
                                     ((oddp x)
                                      (oset-delete x oset)
                                      nil)
                                     (t
                                      (list x))))
                                  oset :reverse t)))))

;;; ordered-sets.lisp EOF
