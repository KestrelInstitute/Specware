;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: alists.lisp
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

;;; a function or relation whose arity is declared to be :alist
;;; takes as arguments keys (SNARK constants) and values (SNARK terms)
;;; in pairs
;;;
;;; a wild-card variable can be specified as a final argument to match
;;; otherwise unmatched keys and values during unification
;;;
;;; during unification, values of matching keys are unified
;;;
;;; if matching key is absent, key-value pair is included in
;;; final argument variable of the matching expression
;;;
;;; ordinarily, positive occurrences of alist-argument expressions
;;; would not have the extra variable argument, since it would
;;; allow any additional keys and values to be ascribed to the
;;; expression; negative occurrences would ordinarily be expected
;;; to have the extra variable argument
;;;
;;; internal representation: alist = nil | variable | (cons (cons key value) alist)
;;; functions with arity :alist have one argument that is an alist

(defun can-be-alist-key-name-p (x)
  (and (symbolp x)
       (not (null x))
       (neq t x)					;used in function/relation sort declarations
       (can-be-constant-name-p x)))

(defun assert-can-be-alist-key-name-p (x)
  (or (can-be-alist-key-name-p x)
      (error "~S cannot be the name of an association-list key." x)))

(defun assert-can-be-alist-key-name-p2 (x alist)
  (or (can-be-alist-key-name-p x)
      (error "~S cannot be the name of an association-list key in ~S." x alist)))

(defun assert-can-be-alist-p (x)
  (labels
    ((can-be-alist-p (v)
       (if (atom v)
           (or (null v)
               (wild-card-p v)
               (error "Association-list ~S does not end with NIL or ?." x))
           (and (consp (car v))
                (assert-can-be-alist-key-name-p2 (caar v) x)
                (can-be-alist-p (cdr v))
                (do ((l (cdr v) (cdr l)))
                    ((atom l)
                     t)
                  (when (eq (caar v) (caar l))
                    (error "Association-list ~S has repeated key ~S." x (caar v))))))))
    (unless (can-be-alist-p x)
      (error "Association-list ~S is ill formed." x))))

(defun input-alist-args (head args polarity)
  (labels
    ((input-alist (l)
       (cond
        ((null l)
         nil)
        ((atom l)
         (input-term1 l polarity))
        (t
         (lcons (lcons (input-term1 (car (first l)) polarity)
                       (input-term1 (cdr (first l)) polarity)
                       (first l))
                (input-alist (rest l))
                l)))))
    (assert-can-be-alist-p args)
    (make-compound head (input-alist args))))

(defun flatten-alist (term subst)
  ;; ((a . b) (c . d) . ?x) -> ((a . b) (c . d) ?x)
  (dereference
   term subst
   :if-variable (list term)
   :if-constant term
   :if-compound-cons (lcons (car term)
                            (flatten-alist (cdr term) subst)
                            term)))

(defun equal-alist-args-p (terms1 terms2 subst fn)
  (declare (ignore fn))
  (equal-alist-p (first terms1) (first terms2) subst))

(defun variant-alist-args (cc terms1 terms2 subst matches fn)
  (declare (ignore fn))
  (variant-alist cc (first terms1) (first terms2) subst matches))

(defun unify-alist-args (cc terms1 terms2 subst fn)
  (declare (ignore fn))
  (unify-alist cc (first terms1) (first terms2) subst))

(defun equal-alist-p (alist1 alist2 subst)
  (and
   (do ((p1 alist1 (rest p1))
        (p2 alist2 (rest p2)))
       (nil)
     (dereference
      p1 subst
      :if-variable (return (dereference p2 subst :if-variable (eq p1 p2)))
      :if-constant (return (dereference p2 subst :if-constant t))
      :if-compound-cons (unless (dereference p2 subst :if-compound t)
                          (return nil))))
   (do ((p1 alist1 (rest p1)))
       (nil)
     (dereference
      p1 subst
      :if-variable (return t)
      :if-constant (return t)
      :if-compound-cons (unless (do ((p2 alist2 (rest p2)))
                                    (nil)
                                  (dereference
                                   p2 subst
                                   :if-variable (return nil)
                                   :if-constant (return nil)
                                   :if-compound-cons (when (eql (car (first p1)) (car (first p2)))
                                                       (return (equal-p (cdr (first p1)) (cdr (first p2)) subst)))))
                          (return nil))))))

(defun variant-alist (cc alist1 alist2 subst matches)
  (let ((vals1 nil)
        (vals2 nil))
    (and
     (do ((p1 alist1 (rest p1))
          (p2 alist2 (rest p2)))
         (nil)
       (dereference
        p1 subst
        :if-variable (if (dereference p2 subst :if-variable t)
                         (progn (push p1 vals1) (push p2 vals2) (return t))
                         (return nil))
        :if-constant (return (dereference p2 subst :if-constant t))
        :if-compound-cons (unless (dereference p2 subst :if-compound t)
                            (return nil))))
     (do ((p1 alist1 (rest p1)))
         (nil)
       (dereference
        p1 subst
        :if-variable (return t)
        :if-constant (return t)
        :if-compound-cons (unless (do ((p2 alist2 (rest p2)))
                                      (nil)
                                    (dereference
                                     p2 subst
                                     :if-variable (return nil)
                                     :if-constant (return nil)
                                     :if-compound-cons (when (eql (car (first p1)) (car (first p2)))
                                                         (push (cdr (first p1)) vals1)
                                                         (push (cdr (first p2)) vals2)
                                                         (return t)))))))
     (variantl cc vals1 vals2 subst matches))))

(defun unify-alist (cc alist1 alist2 subst)
  (let ((var1 nil) (var2 nil) frozen1 frozen2)
    (do ((p1 alist1 (rest p1)))
        (nil)
      (dereference
       p1 subst
       :if-variable (progn (setq frozen1 (variable-frozen-p (setq var1 p1))) (return))
       :if-constant (return)))
    (do ((p2 alist2 (rest p2)))
        (nil)
      (dereference
       p2 subst
       :if-variable (progn (setq frozen2 (variable-frozen-p (setq var2 p2))) (return))
       :if-constant (return)))
    (let (unmatched1 unmatched2)
      (cond
       ((eq var1 var2)
        (setq unmatched1 (setq unmatched2 none)))
       ((and var1 (not frozen1) var2 (not frozen2))
        (setq unmatched1 (setq unmatched2 (make-variable))))
       ((and var1 (not frozen1))
        (setq unmatched1 none unmatched2 var2))
       ((and var2 (not frozen2))
        (setq unmatched2 none unmatched1 var1))
       ((or var1 var2)
        (return-from unify-alist)))
      (let ((vals1 nil) (vals2 nil))
        (do ((p1 alist1 (rest p1)))
            (nil)
          (dereference
           p1 subst
           :if-variable (return)
           :if-constant (return)
           :if-compound (do ((p2 alist2 (rest p2)))
                            (nil)
                          (cond
                           ((dereference p2 subst :if-compound t)
                            (when (eql (car (first p1)) (car (first p2)))
                              (return)))
                           ((eq none unmatched1)
                            (return-from unify-alist))
                           (t
                            (setq unmatched1 (cons (first p1) unmatched1))
                            (return))))))
        (do ((p2 alist2 (rest p2)))
            (nil)
          (dereference
           p2 subst
           :if-variable (return)
           :if-constant (return)
           :if-compound (do ((p1 alist1 (rest p1)))
                            (nil)
                          (cond
                           ((dereference p1 subst :if-compound t)
                            (when (eql (car (first p1)) (car (first p2)))
                              (push (cdr (first p1)) vals1)
                              (push (cdr (first p2)) vals2)
                              (return)))
                           ((eq none unmatched2)
                            (return-from unify-alist))
                           (t
                            (setq unmatched2 (cons (first p2) unmatched2))
                            (return))))))
        (unless (eq none unmatched1)
          (push unmatched1 vals1)
          (push var2 vals2))
        (unless (eq none unmatched2)
          (push unmatched2 vals2)
          (push var1 vals1))
        (unify cc vals1 vals2 subst)))))

(defun conjoin-alists (alist1 alist2)
  (let ((result nil) result-last)
    (dolist (x alist1)
      (let ((x1 (car x)))
        (dolist (y alist2 (collect x result))
          (when (eql x1 (car y))
            (collect (cons x1 (conjoin (cdr x) (cdr y))) result)
            (return)))))
    (dolist (y alist2)
      (let ((y1 (car y)))
        (dolist (x alist1 (collect y result))
          (when (eql y1 (car x))
            (return)))))
    result))

(defun conjoin-alist1 (key value alist)
  (if (assoc key alist)
      (conjoin-alist1* key value alist)
      (acons key value alist)))

(defun conjoin-alist1* (key value alist)
  (let ((p (first alist)))
    (if (eql key (car p))
        (cons (cons key (conjoin (cdr p) value)) (rest alist))
        (cons p (conjoin-alist1* key value (rest alist))))))

(defun alist-test1 (&optional case)
  ;; 2003-04-13: checked
  (initialize)
  (print-options-when-starting nil)
  (print-summary-when-finished nil)
  (use-resolution)
  (declare-relation 'p :alist)
  (declare-relation 'values :any)
  (assert '(p (a . 1) (b . 2) (c . 3)))
  (when (implies case (eql 1 case))
    (new-row-context)
    (print (prove '(p (b . 2))))
    (cl:assert (null (proof))))
  (when (implies case (eql 2 case))
    (new-row-context)
    (print (prove '(p (b . 2) . ?)))
    (cl:assert (proof)))
  (when (implies case (eql 3 case))
    (new-row-context)
    (print (prove '(p (b . 2) (c . ?z) (a . ?x)) :answer '(values ?x ?z)))
    (cl:assert (equal '(values 1 3) (answer t))))
  (when (implies case (eql 4 case))
    (new-row-context)
    (print (prove '(p (b . 2) (a . ?x) . ?) :answer '(values ?x)))
    (cl:assert (equal '(values 1) (answer t))))
  nil)

(defun alist-test2 ()
  ;; 2003-04-13: checked
  (initialize)
  (print-options-when-starting nil)
  (print-summary-when-finished nil)
  (use-resolution)
  (assert '(p ?x ?x) :answer '(values ?x))
  (print (prove '(p (alist (a . 1) (b . 2) . ?) (alist (b . 2) (c . 3) . ?))))
  (cl:assert (equal '(values (alist (a . 1) (b . 2) (c . 3) . ?x)) (answer t))))

(defun alist-test3 ()
  ;; 2003-04-13: checked
  (initialize)
  (print-options-when-starting nil)
  (print-summary-when-finished nil)
  (use-well-sorting)
  (declare-sort 'cat)
  (declare-sort 'dog)
  (declare-sort 'fish)
  (declare-relation 'p :alist :sort '((:a cat) (:b dog) (t fish)))
  (assert '(p (:b . ?y) (:c . ?z) (:a . ?x) (:d . ?dog)))
  (closure)
  (cl:assert (equal '(p (:b . ?dog) (:c . ?fish) (:a . ?cat) (:d . ?dog&fish))
                    (term-to-lisp (row-wff (last-row))))))

;;; alists.lisp EOF
