;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: numbering.lisp
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
  (export '(nonce
            initialize-numberings make-numbering
            *standard-eql-numbering* *standard-equal-numbering*)))

(defvar *nonce*)
(defvar *standard-eql-numbering*)
(defvar *standard-equal-numbering*)

(defun nonce ()
  ;; each call returns a new positive value in ascending order
  (incf *nonce*))

(defun initialize-numberings ()
  (setf *nonce* 0)
  (setf *standard-eql-numbering* (make-numbering :test #'eql))
  (setf *standard-equal-numbering* (make-numbering :test #'equal))
  nil)

(defun make-numbering (&key (test #'eql) (inverse t))
  ;; make-numbering returns a function f such that
  ;; (f :lookup object) returns a unique number for object, adding one if necessary
  ;; (f :lookup? object) returns the number for object or nil if there isn't one
  ;; (f :delete object) deletes an object from the numbering
  ;; (f :inverse number) returns an object by its number
  ;; (f :map fn) applies binary function fn to each object and its number
  (let ((table (make-hash-table :test test)))
    (if inverse
        (let* ((not-there (cons nil nil))
               (invtable (make-sparse-vector :default-value not-there)))
          (lambda (action arg)
            (ecase action
              (:lookup
               (or (gethash arg table)
                   (let ((number (nonce)))
                     (setf (sparef invtable number) arg (gethash arg table) number))))
              (:lookup?
               (gethash arg table))
              (:delete
               (let ((number (gethash arg table)))
                 (when number
                   (remhash arg table)
                   (setf (sparef invtable number) not-there)
                   number)))
              (:map
               (map-sparse-vector arg invtable))
              (:inverse
               (let ((object (sparef invtable arg)))
                 (if (eq not-there object) (error "No object numbered ~D." arg) object))))))
        (lambda (action arg)
          (ecase action
            (:lookup
             (or (gethash arg table)
                 (let ((number (nonce)))
                   (setf (gethash arg table) number))))
            (:lookup?
             (gethash arg table))
            (:delete
             (let ((number (gethash arg table)))
               (when number
                 (remhash arg table)
                 number))))))))

#+cmu
(eval-when (:load-toplevel)
  (initialize-numberings))

;;; numbering.lisp EOF
