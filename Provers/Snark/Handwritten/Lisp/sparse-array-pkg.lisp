;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: common-lisp-user -*-
;;; File: sparse-array-pkg.lisp
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

(in-package :common-lisp-user)

;;; package definition for mes-sparse-array system

(defpackage :mes-sparse-array
  (:use :common-lisp))

(in-package :mes-sparse-array)
(export
 '(sparef
   sparse-vector make-sparse-vector sparse-vector-p
   sparse-vector-boolean sparse-vector-default-value
   sparse-vector-count
   map-sparse-vector map-sparse-vector-with-indexes map-sparse-vector-indexes-only
   with-sparse-vector-iterator
   first-sparef last-sparef pop-first-sparef pop-last-sparef
   sparse-matrix make-sparse-matrix sparse-matrix-p
   sparse-matrix-boolean sparse-matrix-default-value
   sparse-matrix-row sparse-matrix-column sparse-matrix-rows sparse-matrix-columns))

;;; sparse-array-pkg.lisp EOF
