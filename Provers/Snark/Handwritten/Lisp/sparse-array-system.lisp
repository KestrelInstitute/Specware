;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: common-lisp-user -*-
;;; File: sparse-array-system.lisp
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

(in-package :common-lisp-user)

(defpackage :mes-sparse-array
  (:use :common-lisp :mes-definline :mes-progc)
  (:export
   "SPAREF"
   "SPARSE-VECTOR" "MAKE-SPARSE-VECTOR" "SPARSE-VECTOR-P"
   "SPARSE-VECTOR-BOOLEAN" "SPARSE-VECTOR-DEFAULT-VALUE"
   "SPARSE-VECTOR-COUNT"
   "MAP-SPARSE-VECTOR" "MAP-SPARSE-VECTOR-WITH-INDEXES" "MAP-SPARSE-VECTOR-INDEXES-ONLY"
   "WITH-SPARSE-VECTOR-ITERATOR"
   "FIRST-SPAREF" "LAST-SPAREF" "POP-FIRST-SPAREF" "POP-LAST-SPAREF"
   "SPARSE-MATRIX" "MAKE-SPARSE-MATRIX" "SPARSE-MATRIX-P"
   "SPARSE-MATRIX-BOOLEAN" "SPARSE-MATRIX-DEFAULT-VALUE"
   "SPARSE-MATRIX-COUNT"
   "SPARSE-MATRIX-ROW" "SPARSE-MATRIX-COLUMN" "SPARSE-MATRIX-ROWS" "SPARSE-MATRIX-COLUMNS"
   "MAP-SPARSE-MATRIX" "MAP-SPARSE-MATRIX-WITH-INDEXES" "MAP-SPARSE-MATRIX-INDEXES-ONLY"))

(dolist (name '("sparse-vector" "sparse-array"))
  (let ((file (make-pathname :name name :defaults *load-truename*)))
    (declare (special *compile-me*))
    (load (if (and (boundp '*compile-me*) *compile-me*)
              (compile-file file)
              (or (probe-file (compile-file-pathname file)) file)))))

;;; sparse-array-system.lisp EOF
