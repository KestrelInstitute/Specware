;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: variables.lisp
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

(in-package :snark)

;;(defconstant top-sort 'true)

(defconstant $number-of-variable-blocks 100)
(defconstant $number-of-variables-per-block 600)
(defconstant $number-of-variables-in-blocks (* $number-of-variable-blocks $number-of-variables-per-block))

(defvar *variables*)				;table to translate (number sort) pairs to variables
(defvar *next-variable-number* 0)		;next number to use for new unique variable
(declaim (type integer *next-variable-number*))

(defun initialize-variables ()
  (setf *variables* (make-sparse-matrix :rows t))
  (setf *next-variable-number* $number-of-variables-in-blocks)
  nil)

(defun make-variable (&optional sort number)
  ;; if number is specified, return canonical variable for that sort and number
  ;; if number is not specified, create a new unique variable with that sort
  ;; variable identity must be testable by EQ
  ;; this variable representation must also be understood by dereference
  ;;
  ;; don't create last variable in a block; when incrementing variable numbers,
  ;; the following variable would be in the next block creating confusion
  (let ((s (and (neq top-sort sort) sort)))
    (cond
     (number
      (let ((s# (funcall *standard-equal-numbering* :lookup s)))
        (or (sparef *variables* number s#)
            (progn
              (cl:assert (<= 0 number))
              (cl:assert (< number $number-of-variables-in-blocks))
              (cl:assert (/= 0 (mod (1+ number) $number-of-variables-per-block)))
              (setf (sparef *variables* number s#) (cons '%vari (if s (cons s number) number)))))))
     (t
      (setf *next-variable-number* (1+ (setf number *next-variable-number*)))
      (cons '%vari (if s (cons s number) number))))))

(defun variable-sort (var)
  (let ((v (cdr var)))
    (if (consp v) (carc v) top-sort)))

(defun variable-number (var)
  (let ((v (cdr var)))
    (if (consp v) (cdrc v) v)))

(defun declare-variable-symbol (name &key (sort top-sort sort-supplied-p))
  ;; return same variable every time for same input free variable
  (assert-can-be-variable-name-p name)
  (when (neq top-sort sort)
    (setq sort (input-sort2 sort))
    ;; SNARK output uses ?X, ?Y, ?Z, ?U, ?V, ?W, ?X1, ?Y1, ?Z1, ?U1, ?V1, ?W1, ...
    ;; as unsorted variables; to enable SNARK to faithfully input its own output,
    ;; don't allow these variables to be declared with a sort
    (cl:assert (not (let ((s (symbol-name name)))
                      (and (eql #\? (char s 0))
                           (member (char s 1) '(#\X #\Y #\Z #\U #\V #\W))
                           (every #'digit-char-p (subseq s 2)))))
               ()
               "Cannot declare ~A as variable of sort ~A; ~A is unsorted."
               name (sort-name sort) name))
  (let ((v (input-variable name)))
    (cond
     ((eq none (variable-sort v))		;new variable
      (when (and (not sort-supplied-p) (use-variable-name-sorts?))
        (setq sort (sort-from-variable-name name)))
      (setf (cdr v) (if (neq top-sort sort)
                        (cons sort (variable-number v))
                        (variable-number v))))
     (sort-supplied-p
      (cl:assert (same-sort-p sort (variable-sort v)) ()
                 "Cannot declare ~A as variable of sort ~A; ~A is of sort ~A."
                 name (sort-name sort) name (sort-name (variable-sort v)))))
    v))

(defun sort-from-variable-name (name)
  (let* ((sort top-sort)
         (s (symbol-name name))
         (m (if (char-equal #\? (char s 0)) 1 0))
         (n (1+ (position-if-not #'digit-char-p s :from-end t))))
    (when (eql #\% (char s (1- n)))
      (decf n))
    (when (<= 2 (- n m))
      (mvlet (((:values sym found) (intern (subseq s m n) (symbol-package name))))
        (cond
         (found
          (let ((v (find-symbol-table-entry sym :sort)))
            (when (neq none v)
              (setq sort v))))
         (t
          (unintern sym)))))
    sort))

(defun variable-block (n)
  (declare (fixnum n))
  (cl:assert (< 0 n $number-of-variable-blocks))
  (* $number-of-variables-per-block n))

(defun variable-block-0-p (varnum)
  (declare (fixnum varnum))
  (> $number-of-variables-per-block varnum))

;;; variables.lisp EOF
