;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: tptp.lisp
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

(in-package :snark)

(defun print-row-in-tptp-format (row &optional fof)
  (let ((wff (row-wff row)))
    (cl:assert (not (or (eq false wff) (eq true wff))))
    (cond
     (fof
      (print-fof-in-tptp-format (row-wff row) (row-name-or-number row) (row-reason row)))
     (t
      (cl:assert (clause-p row))
      (print-clause-in-tptp-format (row-wff row) (row-name-or-number row) (row-reason row))))
    row))

(defun print-clause-in-tptp-format (clause name-or-number &optional reason)
  (princ "input_clause(")
  (print-row-name-or-number-in-tptp-format name-or-number nil)
  (princ ",")
  (print-row-reason-in-tptp-format reason nil)
  (princ ",")
  (terpri)
  (princ "    [")
  (prog->
    (quote t -> first)
    (map-atoms-in-clause clause ->* atom polarity)
    (if first (setf first nil) (progn (princ ",") (terpri) (princ "     ")))
    (princ (ecase polarity (:pos "++") (:neg "--")))
    (print-term-in-tptp-format atom))
  (princ "])."))

(defun print-fof-in-tptp-format (wff name-or-number &optional reason)
  (declare (ignore wff name-or-number reason))
  (unimplemented))

(defun print-row-name-or-number-in-tptp-format (name-or-number fof)
  (etypecase name-or-number
    (number
     (princ (if fof "formula_" "clause_")) 
     (princ name-or-number))
    (symbol
     (princ (cl:substitute #\_ #\- (string-downcase (string name-or-number)))))))

(defun print-row-reason-in-tptp-format (reason fof)
  (declare (ignore fof))
  (princ (case reason
           (assertion "axiom")
           (assumption "hypothesis")
           (~conclusion "conjecture")
           (otherwise "axiom"))))

(defun print-term-in-tptp-format (term &optional subst)
  (dereference
   term subst
   :if-constant (let ((*print-case* :downcase))
                  (princ term))
   :if-variable (progn
                  (cl:assert (eq true (variable-sort term)))
                  (princ (subseq (string (var-to-lisp2 term)) 1)))
   :if-compound (progn
                  (let ((head (head term)))
                    (cond
                     ((eq *=* head)
                      (princ "equal"))
                     (t
                      (let ((*print-case* :downcase))
                        (princ (function-name head))))))
                  (princ "(")
                  (print-args-in-tptp-format (args term))
                  (princ ")"))))

(defun print-args-in-tptp-format (args)
  (prog->
    (quote t -> first)
    (dolist args ->* arg)
    (if first (setf first nil) (princ ","))
    (print-term-in-tptp-format arg)))

;;; tptp.lisp EOF
