;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: constants.lisp
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
;;; Portions created by the Initial Developer are Copyright (C) 1981-2003.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :snark)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter constant-and-function-slots
    '((number (nonce) :read-only t)
      (hash-code (make-atom-hash-code))
      (boolean-valued-p nil)		;overloaded to be input name of the proposition
      (complement nil)			;complement of proposition symbol P is the proposition symbol ~P
      (magic t)				;nil means don't make magic-set goal for this proposition
      (skolem-p nil)
      (created-p nil)
      (constructor nil)
      (allowed-in-answer t)
      (kbo-weight 1)
      (weight 1)
      (constraint-theory nil)
      (in-use nil)
      (plist nil))))			;property list for more properties

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter constant-slots
    (append constant-and-function-slots
            '((sort top-sort)
              ))))

(defstruct constant-info
  . #.constant-slots)

(defvar *constant-info-table*)

(definline get-constant-info (const)
  (or (gethash const *constant-info-table*)
      (init-constant-info const)))

(defun init-constant-info (const)
  (assert-can-be-constant-name-p const)
  (init-constant-info1 const))

(defun init-constant-info1 (const)
  (setf (gethash const *constant-info-table*) (make-constant-info)))

(progn
  . #.(mapcan
       (lambda (x)
         (let* ((slot-name (if (consp x) (first x) x))
                (constant-slot (intern (format nil "CONSTANT-~A" slot-name) :snark))
                (set-constant-slot (list 'setf constant-slot))
                (constant-info-slot (intern (format nil "CONSTANT-INFO-~A" slot-name) :snark)))
           (append 
            (unless (member slot-name '())
              (list
               `(defun ,CONSTANT-SLOT (const)
                  (,constant-info-slot (get-constant-info const)))))
            (unless (member slot-name '(number hash-code))
              (list
               `(defun ,SET-CONSTANT-SLOT (value const)
                  (setf (,constant-info-slot (get-constant-info const)) value)))))))
       constant-slots))

(defun constant-name (const)
  (or (constant-boolean-valued-p const) const))

(defun constant-alias-or-name (const)
  (let ((aliases (constant-aliases const)))
    (if aliases (first aliases) (constant-name const))))

(defun constant-aliases (const)
  (getf (constant-plist const) :aliases))

(defun constant-documentation (const)
  (getf (constant-plist const) :documentation))

(defun constant-author (const)
  (getf (constant-plist const) :author))

(defun constant-source (const)
  (getf (constant-plist const) :source))

(defun (setf constant-aliases) (value const)
  (setf (getf (constant-plist const) :aliases) value))

(defun (setf constant-documentation) (value const)
  (setf (getf (constant-plist const) :documentation) value))

(defun (setf constant-author) (value const)
  (setf (getf (constant-plist const) :author) value))

(defun (setf constant-source) (value const)
  (setf (getf (constant-plist const) :source) value))

(defun initialize-constants ()
  (setq *constant-info-table* (make-hash-table))
  nil)

(defun map-constants (&optional function)
  (let ((result nil) result-last)
    (prog->
      (maphash *constant-info-table* ->* k v)
      (declare (ignore v))
      (if function (funcall function k) (collect k result)))
    result))

(defun declare-constant-symbol* (symbol
                                 &key
                                 alias
                                 (sort nil)
                                 (documentation nil documentation-supplied)
                                 (author nil author-supplied)
                                 (source nil source-supplied)
                                 (complement nil complement-supplied)
                                 (magic t magic-supplied)
                                 (skolem-p nil skolem-p-supplied)
                                 (created-p nil created-p-supplied)
                                 (constructor nil constructor-supplied)
                                 (allowed-in-answer nil allowed-in-answer-supplied)
                                 (kbo-weight nil kbo-weight-supplied)
                                 (weight nil weight-supplied)
                                 )
  ;; doesn't do anything if no keywords are supplied
  (macrolet
      ((set-constant-slot (slot)
	 (let ((slot-supplied (intern (concatenate 'string
						   (symbol-name slot)
						   "-SUPPLIED")
				      :snark))
	       (function-slot (intern (concatenate 'string
						   "CONSTANT-"
						   (symbol-name slot))
				      :snark)))
	   `(when ,slot-supplied
	     (setf (,function-slot symbol) ,slot)))))
    (when alias
      (create-aliases-for-symbol alias symbol))
    (when sort
      (declare-constant-sort symbol (input-sort2 sort)))
    (set-constant-slot documentation)
    (set-constant-slot author)
    (set-constant-slot source)
    (set-constant-slot complement)
    (set-constant-slot magic)
    (set-constant-slot skolem-p)
    (set-constant-slot created-p)
    (when constructor-supplied
      (cl:assert (implies (or (characterp symbol) (stringp symbol)) constructor))
      (setf (constant-constructor symbol) constructor))
    (set-constant-slot allowed-in-answer)
    (set-constant-slot kbo-weight)
    (set-constant-slot weight)
    symbol))

(defun declare-constant-symbol1 (symbol keys-and-values)
  (get-constant-info symbol)
  (if keys-and-values
      (apply #'declare-constant-symbol* symbol keys-and-values)
      symbol))

(defun declare-constant-symbol (&rest args)
  (declare (dynamic-extent args))
  (apply 'declare-constant args))

(defun declare-constant (name &rest keys-and-values)
  (declare (dynamic-extent keys-and-values))
  (mvlet (((:values symbol new) (input-constant-symbol name)))
    (cond
     (new
      (declare-constant-symbol1 symbol keys-and-values))
     (t
      (when (print-symbol-in-use-warning? name keys-and-values)
        (warn "Declaring constant symbol ~S, which is already in use." name))
      (declare-constant-symbol1 symbol keys-and-values)))))

(defun declare-proposition-symbol (&rest args)
  (declare (dynamic-extent args))
  (apply 'declare-proposition args))

(defun declare-proposition (name &rest keys-and-values)
  (declare (dynamic-extent keys-and-values))
  (mvlet (((:values symbol new) (input-proposition-symbol name)))
    (cond
     (new
      (declare-constant-symbol1 symbol keys-and-values))
     (t
      (when (print-symbol-in-use-warning? name keys-and-values)
        (warn "Declaring proposition symbol ~S, which is already in use." name))
      (declare-constant-symbol1 symbol keys-and-values)))))

(defun constant-constructor1 (const)
  (or (numberp const)
      (stringp const)
      (characterp const)
      (constant-constructor const)))

(defun constant-constructor2 (const)
  (or (and (or (use-numbers-as-constructors?)
	       (use-code-for-numbers?))
	   (numberp const))
      (stringp const)
      (characterp const)
      (constant-constructor const)))

(defun if-constant-constructor-then-false (term)
  (if (constant-constructor1 term) false none))

;;; constants.lisp EOF
