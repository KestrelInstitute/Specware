;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: rewrite-code-chars.lisp
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

(declare-snark-option use-code-for-characters nil nil)

(defmethod use-code-for-characters :before (&optional (value t))
  (cond
   (value
    (use-lisp-types-as-sorts t)
    (mapc #'declare-function-rewrite-code
          '((char-code 1 char-code-term-rewriter :sort nonnegative-integer)
            (code-char 1 code-char-term-rewriter :sort character)
            (char-string-to-list 1 char-string-to-list-term-rewriter :sort list)
            (char-list-to-string 1 char-list-to-string-term-rewriter :sort string)
            ))
    (mapc #'declare-predicate-rewrite-code
          '((character 1 character-atom-rewriter)
            (string 1 string-atom-rewriter)
            )))))

(defmacro when-using-code-for-characters (&body body)
  `(if (use-code-for-characters?) (progn ,@body) none))

(defun char-list-p (x &optional subst)
  (dereference
    x subst
    :if-constant (null x)
    :if-compound-cons (and (let ((a (carc x)))
                             (dereference a subst :if-constant (characterp a)))
                           (char-list-p (cdrc x) subst))))

(defun char-code-term-rewriter (term subst)
  ;; (char-code #\a) -> 97
  (when-using-code-for-characters
    (let ((x (arg1 term)))
      (if (dereference x subst :if-constant (characterp x))
          (declare-constant-symbol (char-code x))
          none))))

(defun code-char-term-rewriter (term subst)
  ;; (code-char 97) -> #\a
  (when-using-code-for-characters
    (let ((x (arg1 term)))
      (if (dereference x subst :if-constant (naturalp x))
          (declare-constant-symbol (code-char x))
          none))))

(defun char-string-to-list-term-rewriter (term subst)
  ;; (char-string-to-list "abc") -> (list #\a #\b #\c)
  (when-using-code-for-characters
    (let ((x (arg1 term)))
      (dereference
       x subst
       :if-variable none       
       :if-constant (if (stringp x)
                        (mapc #'declare-constant-symbol (coerce x 'list))
                        none)
       :if-compound none))))

(defun char-list-to-string-term-rewriter (term subst)
  ;; (char-list-to-string (list #\a #\b #\c)) -> "abc"
  (when-using-code-for-characters
    (let ((x (arg1 term)))
      (dereference
       x subst
       :if-variable none
       :if-constant (if (null x)
                        (declare-constant-symbol "")
                        none)
       :if-compound-cons (if (char-list-p x subst)
                             (declare-constant-symbol (coerce (instantiate x subst) 'string))
                             none)
       :if-compound-appl none))))

(defun character-atom-rewriter (atom subst)
  (when-using-code-for-characters
    (let ((term (arg1 atom)))
      (dereference
       term subst
       :if-variable none			;could check variable-sort
       :if-constant (if (characterp term) true (if-constant-constructor-then-false term))
       :if-compound-cons none
       :if-compound-appl (if (function-constructor (heada term)) false none)))))

(defun string-atom-rewriter (atom subst)
  (when-using-code-for-characters
    (let ((term (arg1 atom)))
      (dereference
       term subst
       :if-variable none			;could check variable-sort
       :if-constant (if (stringp term) true (if-constant-constructor-then-false term))
       :if-compound-cons none
       :if-compound-appl (if (function-constructor (heada term)) false none)))))

;;; rewrite-code-chars.lisp EOF
