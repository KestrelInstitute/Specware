;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: resolve-code.lisp
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

(defun reflexivity-satisfier (cc atom subst)
  ;; example: this is called when trying to resolve away (not (rel a b)) after
  ;; doing (declare-relation 'rel 2 :satisfy-code 'reflexivity-satisfier)
  ;; (rel a b) -> true after unifying a and b
  (mvlet (((:list a b) (args atom)))
    (unify cc a b subst)))			;call cc with substitution

(defun irreflexivity-falsifier (cc atom subst)
  ;; example: this is called when trying to resolve away (rel a b) after
  ;; doing (declare-relation 'rel 2 :falsify-code 'irreflexivity-falsifier)
  ;; (rel a b) -> false after unifying a and b
  (mvlet (((:list a b) (args atom)))
    (unify cc a b subst)))			;call cc with substitution

(defun equality-satisfier (cc atom subst)
  (when (use-code-for-equality?)
    (reflexivity-satisfier cc atom subst)))

(defun variable-satisfier (cc atom subst)
  (let ((x (arg1 atom)))
    (dereference
     x subst
     :if-variable (funcall cc subst))))

(defun nonvariable-satisfier (cc atom subst)
  (let ((x (arg1 atom)))
    (dereference
     x subst
     :if-constant (funcall cc subst)
     :if-compound (funcall cc subst))))

(defun resolve-code-example1 (&optional (case 1))
  (let ((mother-table (print '((alice betty)
                               (alice barbara)
                               (betty carol)
                               (betty claudia)))))
    (flet ((mother-satisfier (cc atom subst)
             ;; the two definitions below are equivalent
             #+ignore
             (let ((args (args atom)))
               (mapc (lambda (pair) (unify cc args pair subst))
                     mother-table))
             (prog->
               (args atom -> args)
               (mapc mother-table ->* pair)
               (unify args pair subst ->* subst2)
               (funcall cc subst2))))
      (initialize)
      (print-options-when-starting nil)
      (print-rows-when-derived nil)
      (print-summary-when-finished nil)
      (case case
        (1
         (use-resolution t))
        (2
         (use-hyperresolution t))
        (3
         (use-negative-hyperresolution t)))
      (declare-relation 'mother 2 :satisfy-code #'mother-satisfier)
      (prove '(mother betty ?x) :answer '(values ?x) :name 'who-is-bettys-child?)
      (loop
        (when (eq :agenda-empty (closure))
          (return)))
      (mapcar (lambda (x) (arg1 x)) (answers)))))

;;; resolve-code.lisp EOF
