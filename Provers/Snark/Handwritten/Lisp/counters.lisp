;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: counters.lisp
;;; Copyright (c) 2000-2001 Mark E. Stickel
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
  (export '(make-counter
            increment-counter decrement-counter
            counter-value counter-values
            princf)))

(defstruct (counter
            (:constructor MAKE-COUNTER (&optional (increments 0)))
            (:copier nil))
  (increments 0 :type integer)
  (decrements 0 :type integer)
  (previous-peak-value 0 :type integer))

(defun increment-counter (counter &optional (n 1))
  (declare (type integer n))
;;(cl:assert (<= 0 n))
  (incf (counter-increments counter) n)
  nil)

(defun decrement-counter (counter &optional (n 1))
  (declare (type integer n))
;;(cl:assert (<= 0 n))
  (let* ((d (counter-decrements counter))
         (v (- (counter-increments counter) d)))
    (when (> v (counter-previous-peak-value counter))
      (setf (counter-previous-peak-value counter) v))
    (setf (counter-decrements counter) (+ d n))
    nil))

(defun counter-value (counter)
  (- (counter-increments counter) (counter-decrements counter)))

(defun counter-values (counter)
  ;; returns 4 values: current value, peak value, #increments, #decrements
  (let* ((i (counter-increments counter))
         (d (counter-decrements counter))
         (v (- i d)))
  (values v (max v (counter-previous-peak-value counter)) i d)))

(defvar *show-count-values* '(1000000 100000 10000 1000 100 10 1))

(defun show-count-p (n)
  (dolist (v *show-count-values*)
    (when (>= n v)
      (return (eql 0 (rem n v))))))

(defun show-count (n)
  (princ #\Space)
  (princ n)
  (princ #\Space)
  n)

(defun show-count0 (n)
  (if (show-count-p n) n (show-count n)))

(defun show-count1 (n)
  (if (show-count-p n) (show-count n) n))

(defmacro princf (place &optional (delta 1))
  ;; increment counter and maybe print it
  ;; if delta is 0, print the counter unless the previous increment did
  (cl:assert (member delta '(0 1)))
  (if (eql 0 delta)
      `(show-count0 ,place)
      `(show-count1 (incf ,place))))

;;; counters.lisp EOF
