;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: rewrite-code-lists.lisp
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

(declare-snark-option use-code-for-lists nil nil)

(defmethod use-code-for-lists :before (&optional (value t))
  (when value
    (use-lisp-types-as-sorts t)
    (mapc #'declare-function-rewrite-code
          '((first     1 first-term-rewriter)
            (rest      1 rest-term-rewriter :sort list)
            (last      1 last-term-rewriter)
            (butlast   1 butlast-term-rewriter :sort list)
            (append    :any append-term-rewriter :sort list)	;KIF allows only 2 arguments
            (revappend 2 revappend-term-rewriter :sort list)
            (reverse   1 reverse-term-rewriter :sort list)
;;          (adjoin    2 adjoin-term-rewriter :sort cons)
;;          (remove    2 remove-term-rewriter :sort list)
;;          (subst     3 subst-term-rewriter :sort list)
            (length    1 length-term-rewriter :sort nonnegative-integer)
            (nth       2 nth-term-rewriter)			;CL style
            (nthrest   2 nthrest-term-rewriter :sort list)	;CL style
            ))
    (mapc #'declare-predicate-rewrite-code
          '((list    1 listp-atom-rewriter :alias listp)	;KIF uses 'list', a SNARK constructor
            (cons    1 consp-atom-rewriter :alias consp)
            (null    1 null-atom-rewriter)
            (single  1 single-atom-rewriter)
            (double  1 double-atom-rewriter)
            (triple  1 triple-atom-rewriter)
            (item    2 item-atom-rewriter :satisfy-code item-atom-satisfier)
;;          (sublist 2 sublist-atom-rewriter)
            ))))

(defmacro when-using-code-for-lists (&body body)
  `(if (use-code-for-lists?) (progn ,@body) none))

(defun list-term1 (term subst)
  (dereference
   term subst
   :if-compound-cons true
   :if-compound-appl (if (function-constructor (heada term)) false none)
   :if-constant (if (null term) true (if-constant-constructor-then-false term))
   :if-variable none))

(defun cons-term1 (term subst)
  (dereference
   term subst
   :if-compound-cons true
   :if-compound-appl (if (function-constructor (heada term)) false none)
   :if-constant (if (null term) false (if-constant-constructor-then-false term))
   :if-variable none))

(defun null-term1 (term subst)
  (dereference
   term subst
   :if-compound-cons false
   :if-compound-appl (if (function-constructor (heada term)) false none)
   :if-constant (if (null term) true (if-constant-constructor-then-false term))
   :if-variable none))

(defun single-term1 (term subst)
  (dereference
   term subst
   :if-compound-cons (null-term1 (cdrc term) subst)
   :if-compound-appl (if (function-constructor (heada term)) false none)
   :if-constant (if (null term) false (if-constant-constructor-then-false term))
   :if-variable none))

(defun double-term1 (term subst)
  (dereference
   term subst
   :if-compound-cons (single-term1 (cdrc term) subst)
   :if-compound-appl (if (function-constructor (heada term)) false none)
   :if-constant (if (null term) false (if-constant-constructor-then-false term))
   :if-variable none))

(defun triple-term1 (term subst)
  (dereference
   term subst
   :if-compound-cons (double-term1 (cdrc term) subst)
   :if-compound-appl (if (function-constructor (heada term)) false none)
   :if-constant (if (null term) false (if-constant-constructor-then-false term))
   :if-variable none))

(defun listp-atom-rewriter (atom subst)
  (when-using-code-for-lists
    (list-term1 (arg1 atom) subst)))

(defun consp-atom-rewriter (atom subst)
  (when-using-code-for-lists
    (cons-term1 (arg1 atom) subst)))

(defun null-atom-rewriter (atom subst)
  (when-using-code-for-lists
    (null-term1 (arg1 atom) subst)))

(defun single-atom-rewriter (atom subst)
  (when-using-code-for-lists
    (single-term1 (arg1 atom) subst)))

(defun double-atom-rewriter (atom subst)
  (when-using-code-for-lists
    (double-term1 (arg1 atom) subst)))

(defun triple-atom-rewriter (atom subst)
  (when-using-code-for-lists
    (triple-term1 (arg1 atom) subst)))

(defun first-term-rewriter (term subst)
  (when-using-code-for-lists
    (let ((x (arg1 term)))
      (dereference
       x subst
       :if-variable none
       :if-constant (if (null x) nil none)	;(first nil) -> nil
       :if-compound-cons (carc x)
       :if-compound-appl none))))

(defun rest-term-rewriter (term subst)
  (when-using-code-for-lists
    (let ((x (arg1 term)))
      (dereference
       x subst
       :if-variable none
       :if-constant (if (null x) nil none)	;(rest nil) -> nil
       :if-compound-cons (cdrc x)
       :if-compound-appl none))))

(defun last-term-rewriter (term subst)
  (when-using-code-for-lists
    (do ((x (arg1 term) (cdr x))
         (value nil (car x)))			;(last nil) -> nil
        (nil)
      (dereference
       x subst
       :if-variable (return none)
       :if-constant (return (if (null x) value none))
       :if-compound-appl (return none)))))

(defun butlast-term-rewriter (term subst)
  (when-using-code-for-lists
   (do ((x (arg1 term) (cdr x))
        (value nil (cons (car x) value)))	;(butlast nil) -> nil
       (nil)
     (dereference
      x subst
      :if-variable (return none)
      :if-constant (return (if (null x) (nreverse (cdr value)) none))
      :if-compound-appl (return none)))))

(defun item-atom-rewriter (atom subst)
  (when-using-code-for-lists
    (mvlet (((:list x l) (args atom)) (l* nil) (val none))
      (loop
        (dereference
         l subst
         :if-variable (return)
         :if-constant (if (and (null l) (null l*))
                          (return-from item-atom-rewriter false)
                          (return))
         :if-compound-cons (let* ((y (pop l))
                                  (v (equality-rewrite* x y subst)))
                             (cond
                              ((eq true v)
                               (return-from item-atom-rewriter true))
                              ((eq false v)
                               (setq val nil))
                              (t
                               (push y l*))))
         :if-compound-appl (return)))
      (or val (make-compound (head atom) x (revappend l* l))))))

(defun item-atom-satisfier (cc atom subst)
  (when-using-code-for-lists
    (mvlet (((:list x l) (args atom)))
      (loop
        (dereference
         l subst
         :if-variable (return)
         :if-constant (return)
         :if-compound-cons (unify cc x (pop l) subst)
         :if-compound-appl (return))))))

(defun append-term-rewriter (term subst)
  (when-using-code-for-lists
    (let ((append-fn (head term))
          (args (args term))
          (args* nil))
      (let ((args args)
            (list nil)
            arg)
        (loop
          (cond
           ((null args)
            (when list
              (push (nreverse list) args*))
            (setq args* (nreverse args*))
            (return))
           (t
            (setq arg (pop args))
            (loop
              (dereference
               arg subst
               :if-variable (progn
                              (when list
                                (push (nreverse list) args*)
                                (setq list nil))
                              (push arg args*)
                              (return))
               :if-constant (progn
                              (when arg
                                (when list
                                  (push (nreverse list) args*)
                                  (setq list nil))
                                (push arg args*))
                              (return))
               :if-compound-appl (let ((head (head arg)))
                                   (cond
                                    ((eq append-fn head)
                                     (setq args (append (args arg) args))
                                     (return))
                                    (t
                                     (when list
                                       (push (nreverse list) args*)
                                       (setq list nil))
                                     (push arg args*)
                                     (return))))
               :if-compound-cons (push (pop arg) list)))))))
      (cond
       ((and (same-length-p args args*)
             (every (lambda (x y) (equal-p x y subst)) args args*))
        none)
       ((null args*)
        nil)
       ((null (rest args*))
        (first args*))
       (t
        (make-compound* append-fn args*))))))

(defun revappend-term-rewriter (term subst)
  (when-using-code-for-lists
    (mvlet (((:list x y) (args term)))
      (do ((x x (cdr x))
           (value y (cons (car x) value)))
          (nil)
        (dereference
         x subst
         :if-variable (return none)
         :if-constant (return (if (null x) value none))
         :if-compound-appl (return none))))))

(defun reverse-term-rewriter (term subst)
  (revappend-term-rewriter term subst))

(defun length-term-rewriter (term subst)
  (when-using-code-for-lists
   (let ((n (list-term-length (arg1 term) subst)))
     (if n (declare-constant-symbol n) none))))

(defun list-term-length (x subst)
  (do ((x x (cdr x))
       (value 0 (1+ value)))
      (nil)
    (dereference
     x subst
     :if-variable (return nil)
     :if-constant (return (if (null x) value nil))
     :if-compound-appl (return nil))))

(defun nth-term-rewriter (term subst)
  ;; (nth n list) with n starting at 0 as in CL
  ;; KIF uses (nth list n) with n starting at 1
  (let ((x (nthrest-term-rewriter term subst)))
    (if (eq none x)
        none
        (dereference
         x subst
         :if-variable none
         :if-constant (if (null x) nil none)
         :if-compound-cons (carc x)
         :if-compound-appl none))))

(defun nthrest-term-rewriter (term subst)
  ;; (nthrest n list) uses argument order of CL nthcdr
  (when-using-code-for-lists
    (mvlet (((:list n x) (args term)))
      (if (dereference n subst :if-constant (naturalp n))
          (do ((x x (cdr x))
               (n n (1- n)))
              ((eql 0 n)
               x)
            (dereference
             x subst
             :if-variable (return none)
             :if-constant (return (if (null x) nil none))
             :if-compound-appl (return none)))
          none))))

(defun term-to-list-rewriter (term subst)
  ;; (F a b) -> (list f a b)
  (let ((x (arg1 term)))
    (dereference
     x subst
     :if-variable none
     :if-constant x
     :if-compound-cons (list 'cons (carc x) (cdrc x))
     :if-compound-appl (cons (function-name (check-usable-head1 (heada x))) (argsa x)))))

(defun list-to-term-rewriter (term subst &optional to-atom)
  ;; (list f a b) -> (F a b)
  (let ((x (arg1 term)))
    (dereference
     x subst
     :if-variable none
     :if-constant (if to-atom (input-proposition-symbol x) x)
     :if-compound-appl none
     :if-compound-cons (let ((nargs (list-term-length (cdrc x) subst)))
                         (if nargs
                             (let ((fn (carc x)))
                               (dereference
                                fn subst
                                :if-variable none
                                :if-compound none
                                :if-constant (check-well-sorted
                                              (make-compound*
                                               (check-usable-head1
                                                (if to-atom
                                                    (input-predicate-symbol fn nargs t)
                                                    (input-function-symbol fn nargs)))
                                               (INSTANTIATE (cdrc x) subst)))))
                             none)))))

(defun list-to-atom-rewriter (atom subst)
  (list-to-term-rewriter atom subst t))

;;; rewrite-code-lists.lisp EOF
