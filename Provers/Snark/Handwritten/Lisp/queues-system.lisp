;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: common-lisp-user -*-
;;; File: queues-system.lisp
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

(defpackage :mes-queues
  (:use :common-lisp :mes-doubly-linked-list)
  (:export
   "MAKE-QUEUE" "QUEUE-LENGTH" "QUEUE-EMPTY?"
   "QUEUE-FIRST" "QUEUE-LAST"
   "ENQUEUE" "DEQUEUE"
   "QUEUE-DELETE"
   "MAPNCONC-QUEUE" "DO-QUEUE"))

(dolist (name '("queues"))
  (let ((file (make-pathname :name name :defaults *load-truename*)))
    (declare (special *compile-me*))
    (if (and (boundp '*compile-me*) *compile-me*)
	(SPECWARE::compile-and-load-lisp-file file)
    (load (or (probe-file (compile-file-pathname file)) file)))))

;;; queues-system.lisp EOF
