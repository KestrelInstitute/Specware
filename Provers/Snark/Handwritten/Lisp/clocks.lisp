;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: clocks.lisp
;;; The contents of this file are subject to the Mozilla Public License
;;; Version 1.1 (the "License"); you may not use this file except in
;;; compliance with the License. You may obtain a copy of the License at
;;; http://www.mozilla.org/MPL/
;;;
;;; Software distributed under the License is distributed on an "AS IS"
;;; basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See the
;;; License for the specific language governing rights and limitations
;;; under the License.
;;;
;;; The Original Code is SNARK.
;;; The Initial Developer of the Original Code is SRI International.
;;; Portions created by the Initial Developer are Copyright (C) 1981-2002.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :mes)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *clocks* nil))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun make-clock-variable (name)
    (cl:assert (symbolp name))
    (let* ((s (symbol-name name))
	   (v (intern (concatenate
		       'string
		       "*%"
		       s
		       (if (let ((n (length s)))
			     (and (<= 5 n) (equal (subseq s (- n 5)) (symbol-name :-time))))
			   ""
			   (symbol-name :-time))
                       "%*")
		     :mes)))
      (unless (member v *clocks*)
	(setq *clocks* (nconc *clocks* (list v)))
	(proclaim `(special ,v)))
      v)))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (mapc #'make-clock-variable
	'(
	  resolution
	  paramodulation
	  factoring
          equality-factoring
          condensing
	  forward-subsumption
	  backward-subsumption
          clause-to-clause-subsumption-tests
	  forward-simplification
	  backward-simplification
	  equality-ordering
	  sortal-reasoning
          temporal-reasoning
	  constraint-simplification
	  term-hashing
	  path-indexing
          instance-graph-insertion
	  kif-input
          satisfiability-testing
	  printing
	  halted
	  test1
	  test2
	  test3
	  other
	  )))

(defvar *excluded-clocks* '(*%printing-time%* *%halted-time%*))

(defvar *running-clocks* nil)
(defvar *first-time-value* 0)
(defvar *last-time-value* 0)
(declaim (type integer *first-time-value* *last-time-value*))

(defun initialize-clocks (&optional (excluded-clocks *excluded-clocks*))
  (cl:assert (null *running-clocks*))
  (setq *first-time-value* (get-internal-run-time))
  (setq *excluded-clocks* excluded-clocks)
  (dolist (clk *clocks*)
    (set clk 0)))

(defmacro with-clock-on (clock &body body)
  (setq clock (make-clock-variable clock))
  `(let* ((running-clocks *running-clocks*)
          (*running-clocks* (cons ',clock running-clocks)))
     (declare (dynamic-extent *running-clocks*))
     (if running-clocks
         (decf (symbol-value (first running-clocks))
               (- *last-time-value* (setq *last-time-value* (get-internal-run-time))))
         (setq *last-time-value* (get-internal-run-time)))
     (unwind-protect
       (progn ,@body)
       (decf (symbol-value ',clock)
             (- *last-time-value* (setq *last-time-value* (get-internal-run-time)))))))

(defmacro with-clock-off (clock &body body)
  ;; dummy with-clock-on
  (setq clock (make-clock-variable clock))
  `(progn ,@body))

(defun clock-name (clock)
  (let ((name (symbol-name clock)))
    (nsubstitute #\  #\- (subseq name 2 (- (length name) 7)))))

(defun print-clocks (&optional (excluded-clocks *excluded-clocks*))
  (let ((*print-pretty* nil) (*print-radix* nil) (*print-base* 10.)
        (total-ticks (- (get-internal-run-time) *first-time-value*))
        total-seconds
	(time-included 0)
        (time-excluded 0))
    (terpri-comment)
    (format t "Run time in seconds")
    (dolist (clk *clocks*)
      (let ((v (symbol-value clk)))
	(cond
	  ((eql 0 v)
	   )
	  ((eq '*%other-time%* clk)
	   )
	  ((member clk excluded-clocks)
           (cond
	     ((eql 0 time-excluded)
	      (format t " excluding ~(~A~)" (clock-name clk)))
	     (t
	      (format t ", ~(~A~)" (clock-name clk))))
	   (incf time-excluded v))
	  (t
	   (incf time-included v)))))
    (unless (eql 0 time-excluded)
      (decf total-ticks time-excluded)
      (format t " time"))
    (princ ":")
    (setq *%other-time%* (- total-ticks time-included))
    (setq total-seconds (/ total-ticks float-internal-time-units-per-second))
    (dolist (clk *clocks*)
      (unless (and (neq '*%other-time%* clk) (member clk excluded-clocks))
	(let ((run-time (symbol-value clk)))
	  (unless (eql 0 run-time)
            (terpri-comment)
            (if (> 9.95 total-seconds)
                (format t "~8,1F" (/ run-time float-internal-time-units-per-second))
                (format t "~8D" (round run-time float-internal-time-units-per-second)))
	    (format t " ~3D%   ~@(~A~)"
                    (percentage run-time total-ticks)
		    (clock-name clk))))))
    (terpri-comment)
    (if (> 9.95 total-seconds)
        (format t "~8,1F" total-seconds)
        (format t "~8D" (round total-seconds)))
    (format t "        Total")
    total-seconds))

(defun total-run-time (&optional (excluded-clocks *excluded-clocks*))
  (let ((total-ticks (- (get-internal-run-time) *first-time-value*)))
    (dolist (clk *clocks*)
      (when (and (neq '*%other-time%* clk) (member clk excluded-clocks))
        (decf total-ticks (symbol-value clk))))
    (/ total-ticks float-internal-time-units-per-second)))

(defun print_total_run_time-0 (&optional (excluded-clocks *excluded-clocks*))
  (let ((total-seconds (total-run-time excluded-clocks)))
    (if (> 9.95 total-seconds)
        (format nil "~,1F" total-seconds)
        (format nil "~D" (round total-seconds)))))

;;; clocks.lisp EOF
