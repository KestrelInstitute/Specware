;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: sparse-array.lisp
;;; Copyright (c) 2001-2002 Mark E. Stickel
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
(eval-when (:compile-toplevel :load-toplevel)
  (export '(sparef))
  (export '(sparse-vector sparse-matrix))
  (export '(make-sparse-vector make-sparse-matrix))
  (export '(sparse-vector-p sparse-matrix-p))
  (export '(sparse-vector-count sparse-matrix-count))
  (export '(sparse-matrix-row sparse-matrix-column sparse-matrix-rows sparse-matrix-columns))
  (export '(map-sparse-vector map-sparse-vector-indexes map-sparse-vector-values))
  (export '(map-sparse-matrix map-sparse-matrix-indexes map-sparse-matrix-values))
  (export '(with-sparse-vector-iterator))
  (export '(first-sparef last-sparef))
  (export '(pop-first-sparef pop-last-sparef)))

(defstruct (sparse-matrix
            (:constructor make-sparse-matrix0 (default-value boolean rows columns))
            (:print-function print-sparse-matrix3))
  (default-value nil :read-only t)
  (boolean nil :read-only t)
  (rows nil :read-only t)
  (columns nil :read-only t))

(defun make-sparse-vector (&key boolean default-value)
  (when boolean
    (setf boolean t)
    (when default-value
      (error "Default-value must be NIL for Boolean sparse-arrays.")))
  (make-sparse-vector0 default-value boolean))

(defun make-sparse-matrix (&key boolean default-value (rows t rows-supplied) (columns t columns-supplied))
  (when boolean
    (setf boolean t)
    (when default-value
      (error "Default-value must be NIL for Boolean sparse-arrays.")))
  (let ((rows (and (or (not columns) (if rows-supplied rows (not columns-supplied)))
                   (make-sparse-vector0 nil nil)))
        (columns (and (or (not rows) (if columns-supplied columns (not rows-supplied)))
                      (make-sparse-vector0 nil nil))))
    (let ((sparse-matrix (make-sparse-matrix0 default-value boolean rows columns)))
      (when rows
        (setf (sparse-vector-type rows) `(rows ,sparse-matrix)))
      (when columns
        (setf (sparse-vector-type columns) `(columns ,sparse-matrix)))
      sparse-matrix)))

(defmacro sparef (sparse-array index1 &optional index2)
  (if (null index2)
      `(sparef1 ,sparse-array ,index1)
      `(sparef2 ,sparse-array ,index1 ,index2)))

(defun sparef2 (sparse-matrix row-index col-index)
  (let ((rows (sparse-matrix-rows sparse-matrix)))
    (if rows
        (let ((row (sparef rows row-index)))
          (if row (sparef row col-index) (sparse-matrix-default-value sparse-matrix)))
        (let ((col (sparef (sparse-matrix-columns sparse-matrix) col-index)))
          (if col (sparef col row-index) (sparse-matrix-default-value sparse-matrix))))))

(defun (setf sparse-matrix-row) (value sparse-matrix index)
  (let ((rows (sparse-matrix-rows sparse-matrix)))
    (cond
     (rows
      (setf (sparef rows index) value))
     (t
      (error "No row vectors for sparse-matrix ~A." sparse-matrix)))))

(defun (SETF SPARSE-MATRIX-COLUMN) (value sparse-matrix index)
  (let ((cols (sparse-matrix-columns sparse-matrix)))
    (cond
     (cols
      (setf (sparef cols index) value))
     (t
      (error "No column vectors for sparse-matrix ~A." sparse-matrix)))))

(defun sparse-matrix-row (sparse-matrix index &optional create)
  (let ((rows (sparse-matrix-rows sparse-matrix)))
    (cond
     (rows
      (or (sparef rows index) (and create (setf (sparef rows index) t))))
     (create
      (error "No row vectors for sparse-matrix ~A." sparse-matrix))
     (t
      nil))))

(defun sparse-matrix-column (sparse-matrix index &optional create)
  (let ((cols (sparse-matrix-columns sparse-matrix)))
    (cond
     (cols
      (or (sparef cols index) (and create (setf (sparef cols index) t))))
     (create
      (error "No column vectors for sparse-matrix ~A." sparse-matrix))
     (t
      nil))))

(defun add-sparse-matrix-row-or-column (rows-or-cols index new-row-or-col)
  (let ((type (sparse-vector-type rows-or-cols))
        sparse-matrix cols-or-rows)
    (ecase (first type)
      (rows
       (setf sparse-matrix (second type))
       (setf cols-or-rows (sparse-matrix-columns sparse-matrix))
       (setf type `(row ,sparse-matrix ,index)))
      (columns
       (setf sparse-matrix (second type))
       (setf cols-or-rows (sparse-matrix-rows sparse-matrix))
       (setf type `(column ,sparse-matrix ,index))))
    (unless (eql 0 (sparse-vector-count new-row-or-col))
      (when cols-or-rows
        (map-sparse-vector
         (lambda (index2 value)
           (sparse-vector-setter
            value (or (sparef cols-or-rows index2) (setf (sparef cols-or-rows index2) t)) index))
         new-row-or-col)))
    (setf (sparse-vector-type new-row-or-col) type)
    (sparse-vector-setter new-row-or-col rows-or-cols index)))

(defun delete-sparse-matrix-row-or-column (rows-or-cols index &optional keep)
  ;; removes indexth sparse-vector from rows-or-cols
  ;; and deletes its entries from cols-or-rows
  ;; but leaves contents of removed sparse-vector intact
  (let ((sparse-vector (sparef rows-or-cols index)))
    (when sparse-vector
      (unless (eql 0 (sparse-vector-count sparse-vector))
        (let ((cols-or-rows (let ((type (sparse-vector-type rows-or-cols)))
                              (ecase (first type)
                                (rows (sparse-matrix-columns (second type)))
                                (columns (sparse-matrix-rows (second type))))))
              (default-value (sparse-vector-default-value sparse-vector)))
          (map-sparse-vector-indexes
           (lambda (index2)
             (sparse-vector-setter default-value (sparef cols-or-rows index2) index))
           sparse-vector)))
      (setf (sparse-vector-type sparse-vector) nil)
      (unless keep
        (sparse-vector-setter keep rows-or-cols index)))))

(defun (setf sparef1) (value sparse-vector index)
  (let ((type (sparse-vector-type sparse-vector)))
    (if (null type)
        (sparse-vector-setter value sparse-vector index)
        (ecase (first type)
          (row
           (let ((matrix (second type))
                 (row-index (third type)))
             (if (eql value (sparse-vector-default-value sparse-vector))
                 (let ((col (sparse-matrix-column matrix index)))
                   (when col
                     (sparse-vector-setter value col row-index)))
                 (when (sparse-matrix-columns matrix)
                   (sparse-vector-setter value (sparse-matrix-column matrix index t) row-index))))
           (sparse-vector-setter value sparse-vector index))
          (column
           (let ((matrix (second type))
                 (col-index (third type)))
             (if (eql value (sparse-vector-default-value sparse-vector))
                 (let ((row (sparse-matrix-row matrix index)))
                   (when row
                     (sparse-vector-setter value row col-index)))
                 (when (sparse-matrix-rows matrix)
                   (sparse-vector-setter value (sparse-matrix-row matrix index t) col-index))))
           (sparse-vector-setter value sparse-vector index))
          ((rows columns)
           (cond
            ((null value)
             (delete-sparse-matrix-row-or-column sparse-vector index nil))
            (t
             (let ((matrix (second type)))
               (cond
                ((eq t value)
                 (setf value (make-sparse-vector0
                              (sparse-matrix-default-value matrix)
                              (sparse-matrix-boolean matrix))))
                (t
                 (cl:assert (and (sparse-vector-p value)
                                 (null (sparse-vector-type value))
                                 (if (sparse-vector-boolean value)
                                     (sparse-vector-boolean matrix)
                                     (and (not (sparse-vector-boolean matrix))
                                          (eql (sparse-vector-default-value value)
                                               (sparse-vector-default-value matrix)))))))))
             (delete-sparse-matrix-row-or-column sparse-vector index t)
             (add-sparse-matrix-row-or-column sparse-vector index value))))))))

(defun (setf sparef2) (value sparse-matrix row-index col-index)
  (let ((rows (sparse-matrix-rows sparse-matrix))
        (cols (sparse-matrix-columns sparse-matrix)))
    (cond
     ((eql value (sparse-matrix-default-value sparse-matrix))
      (let ((col (and cols (sparef cols col-index))))
        (when col
          (sparse-vector-setter value col row-index)))
      (let ((row (and rows (sparef rows row-index))))
        (if row
            (sparse-vector-setter value row col-index)
            value)))
     (t
      (when cols
        (sparse-vector-setter value (sparse-matrix-column sparse-matrix col-index t) row-index))
      (if rows
          (sparse-vector-setter value (sparse-matrix-row sparse-matrix row-index t) col-index)
          value)))))

(defun map-sparse-vector (function sparse-vector &key reverse min max)
  (map-sparse-vector0 function sparse-vector reverse min max nil))

(defun map-sparse-vector-indexes (function sparse-vector &key reverse min max)
  (map-sparse-vector0 function sparse-vector reverse min max :indexes))

(defun map-sparse-vector-values (function sparse-vector &key reverse min max)
  (map-sparse-vector0 function sparse-vector reverse min max :values))

(define-compiler-macro map-sparse-vector (function sparse-vector &key reverse min max)
  `(map-sparse-vector0 ,function ,sparse-vector ,reverse ,min ,max nil))

(define-compiler-macro map-sparse-vector-indexes (function sparse-vector &key reverse min max)
  `(map-sparse-vector0 ,function ,sparse-vector ,reverse ,min ,max :indexes))

(define-compiler-macro map-sparse-vector-values (function sparse-vector &key reverse min max)
  `(map-sparse-vector0 ,function ,sparse-vector ,reverse ,min ,max :values))

(defun sparse-matrix-count (sparse-matrix)
  (let ((n 0))
    (prog->
      (or (sparse-matrix-rows sparse-matrix) (sparse-matrix-columns sparse-matrix) -> rows-or-cols)
      (map-sparse-vector-values rows-or-cols ->* v)
      (incf n (sparse-vector-count v)))
    n))

(defun map-sparse-matrix (function sparse-matrix &key reverse)
  (let ((rows (sparse-matrix-rows sparse-matrix)))
    (if rows
        (prog->
          (map-sparse-vector rows :reverse reverse ->* row-index row)
          (map-sparse-vector row :reverse reverse ->* col-index value)
          (funcall function row-index col-index value))
        (prog->
          (map-sparse-vector (sparse-matrix-columns sparse-matrix) :reverse reverse ->* col-index col)
          (map-sparse-vector col :reverse reverse ->* row-index value)
          (funcall function row-index col-index value)))))

(defun map-sparse-matrix-indexes (function sparse-matrix &key reverse)
  (let ((rows (sparse-matrix-rows sparse-matrix)))
    (if rows
        (prog->
          (map-sparse-vector rows :reverse reverse ->* row-index row)
          (map-sparse-vector-indexes row :reverse reverse ->* col-index)
          (funcall function row-index col-index))
        (prog->
          (map-sparse-vector (sparse-matrix-columns sparse-matrix) :reverse reverse ->* col-index col)
          (map-sparse-vector-indexes col :reverse reverse ->* row-index)
          (funcall function row-index col-index)))))

(defun map-sparse-matrix-values (function sparse-matrix &key reverse)
  (let ((rows (sparse-matrix-rows sparse-matrix)))
    (if rows
        (prog->
          (map-sparse-vector-values rows :reverse reverse ->* row)
          (map-sparse-vector-values row :reverse reverse ->* value)
          (funcall function value))
        (prog->
          (map-sparse-vector-values (sparse-matrix-columns sparse-matrix) :reverse reverse ->* col)
          (map-sparse-vector-values col :reverse reverse ->* value)
          (funcall function value)))))

(defun pop-first-sparef (sparse-vector)
  (multiple-value-bind (value index) (first-sparef sparse-vector)
    (when index
      (sparse-vector-setter (sparse-vector-default-value sparse-vector) sparse-vector index))
    (values value index)))

(defun pop-last-sparef (sparse-vector)
  (multiple-value-bind (value index) (last-sparef sparse-vector)
    (when index
      (sparse-vector-setter (sparse-vector-default-value sparse-vector) sparse-vector index))
    (values value index)))

(defun print-sparse-vector3 (x stream depth)
  (declare (ignore depth))
  (print-unreadable-object (x stream :type t :identity t)
    (princ (sparse-vector-count x) stream)))

(defun print-sparse-matrix3 (x stream depth)
  (declare (ignore depth))
  (print-unreadable-object (x stream :type t :identity t)
    (let ((rows (sparse-matrix-rows x)))
      (princ (if rows (sparse-vector-count rows) "?") stream))
    (princ " X " stream)
    (let ((cols (sparse-matrix-columns x)))
      (princ (if cols (sparse-vector-count cols) "?") stream))))

;;; sparse-array.lisp EOF
