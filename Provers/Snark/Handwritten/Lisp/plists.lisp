;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: plists.lisp
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

;;; a function or predicate whose arity is declared to be :plist
;;; takes as arguments keys (SNARK constants) and values (SNARK terms)
;;; in alternating order
;;;
;;; the keys and values comprise an even number of arguments
;;; a wild-card variable can be specified as a final argument to match
;;; otherwise unmatched keys and values during unification
;;;
;;; during unification, values of matching keys are unified
;;;
;;; if matching key is absent, key-value pair is included in
;;; final argument variable of the matching expression
;;;
;;; ordinarily, positive occurrences of plist-argument expressions
;;; would not have the extra variable argument, since it would
;;; allow any additional keys and values to be ascribed to the
;;; expression; negative occurrences would ordinarily be expected
;;; to have the extra variable argument
;;;
;;; internal representation: same as alists
;;; functions with arity :plist have one argument that is a plist

(defun can-be-plist-key-name-p (x)
  (and (symbolp x)
       (not (null x))
       (neq t x)					;used in function/predicate sort declarations
       (can-be-constant-name-p x)))

(defun assert-can-be-plist-key-name-p (x)
  (or (can-be-plist-key-name-p x)
      (error "~S cannot be the name of a property-list key." x)))

(defun assert-can-be-plist-key-name-p2 (x plist)
  (or (can-be-plist-key-name-p x)
      (error "~S cannot be the name of a property-list key in ~S." x plist)))

(defun assert-can-be-plist-p (x)
  (labels
    ((can-be-plist-p (v)
       (if (atom v)
           (or (null v)
               (wild-card-p v)
               (error "Property-list ~S does not end with NIL or ?." x))
           (and (assert-can-be-plist-key-name-p2 (car v) x)
                (consp (cdr v))
                (can-be-plist-p (cddr v))
                (do ((l (cddr v) (cddr l)))
                    ((atom l)
                     t)
                  (when (eq (car v) (car l))
                    (error "Property-list ~S has repeated key ~S." x (car v))))))))
    (unless (can-be-plist-p x)
      (error "Property-list ~S is ill formed." x))))

(defun input-plist-args (head args polarity)
  (labels
    ((input-plist (l)
       (cond
        ((null l)
         nil)
        ((atom l)
         (input-term l polarity))
        (t
         (cons (cons (input-term (first l) polarity)	;plist->alist
                     (input-term (second l) polarity))
               (input-plist (rest (rest l))))))))
    (assert-can-be-plist-p args)
    (make-compound head (input-plist args))))

(defun plist-test1 (&optional case)
  ;; 2000-09-22: checked
  (initialize)
  (print-options-when-starting nil)
  (print-summary-when-finished nil)
  (use-resolution)
  (declare-predicate-symbol 'p :plist)
  (declare-predicate-symbol 'values :any)
  (assert '(p a 1 b 2 c 3))
  (when (implies case (eql 1 case))
    (new-row-context)
    (print (prove '(p b 2)))
    (cl:assert (null (proof))))
  (when (implies case (eql 2 case))
    (new-row-context)
    (print (prove '(p b 2 . ?)))
    (cl:assert (proof)))
  (when (implies case (eql 3 case))
    (new-row-context)
    (print (prove '(p b 2 c ?z a ?x) :answer '(values ?x ?z)))
    (cl:assert (equal '(values 1 3) (answer))))
  (when (implies case (eql 4 case))
    (new-row-context)
    (print (prove '(p b 2 a ?x . ?) :answer '(values ?x)))
    (cl:assert (equal '(values 1) (answer))))
  nil)

;;; plists.lisp EOF
