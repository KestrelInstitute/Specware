;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: output.lisp
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

(defun print-sort (sort &optional (stream *standard-output*) depth)
  (declare (ignore depth))
  (prin1 (sort-name sort) stream)
  sort)

(defun print-function-symbol (fn &optional (stream *standard-output*) depth)
  (declare (ignore depth))
  (prin1 (function-name fn) stream)
  fn)

(defun print-term (term &optional subst (stream *standard-output*) depth)
  (cond
   ((eq :string stream)
    (with-output-to-string (s)
      (print-term term subst s depth)
      s))
   (t
    (let ((term* (term-to-lisp term subst))
	  (*print-case* :downcase))
      (when (and (print-row-length-limit?)
	         (consp term*)
	         (eq 'or (first term*))
	         (< (print-row-length-limit?) (length (rest term*))))
        (setq term* (cons (first term*)
			  (nconc (firstn (rest term*) (print-row-length-limit?))
			         '(---)))))
      #+ignore
      (when (and (consp term*)
	         (eq 'or (first term*))
	         (every (lambda (x)
                          (if (consp x)
                              (eq 'not (first x))
                              (eq '--- x)))
		        (rest term*)))
        (setq term* (list 'not
			  (cons 'and
			        (mapcar (lambda (x)
                                          (if (consp x)
                                              (second x)
                                              '---))
				        (rest term*))))))
      (prin1 term* stream))
    term)))

(defun print-terms (terms &optional subst (stream *standard-output*) depth)
  (declare (ignore depth))
  (princ "(" stream)
  (when terms
    (print-term (first terms) subst stream)
    (dolist (term (rest terms))
      (princ " " stream)
      (print-term term subst stream)))
  (princ ")" stream)
  terms)

(defun pprint-term (term &optional subst (stream *standard-output*) depth)
  (let ((*print-pretty* t))
    (print-term term subst stream depth)))

(defun print-row-term (term &optional subst (stream *standard-output*) depth)
  (let ((*print-pretty* (and (print-rows-prettily?) (print-row-wffs-prettily?))))
    (print-term term subst stream depth)))

(defun terprint-term (term &optional subst (stream *standard-output*) depth)
  (terpri stream)
  (print-term term subst stream depth))

(defmethod print-given-row (row)
  (case (print-rows-when-given?)
    ((nil)
     (when (eq :signal (print-rows-when-derived?))
       (comment)
       (princ #\|)))
    (:signal
     (comment)
     (princ #\|))
    (:indicate				;ttp 7/13/93
     (with-clock-on printing
       (terpri)
       (terpri-comment)
       (format t "*** Inferences from ~A *** " (row-name-or-number row))))
    (otherwise
     (with-clock-on printing
       (when (print-time-used?)
	 (print-incremental-time-used))
       (dotimes (dummy (1- (case (print-rows-when-derived?)
			     ((:signal nil)
			      (print-given-row-lines-signalling?))
			     (otherwise
			      (print-given-row-lines-printing?)))))
	 (declare (ignorable dummy))
	 (terpri))
       (terpri)
       (print-row row "Infer from row ")
       (princ " "))))
  row)

(defmethod print-derived-row (row)
  (case (print-rows-when-derived?)
    ((nil)
     )
    (:signal
     (comment)
     (princ #\+))
    #+ignore
    (:fact
     (when (let ((wff (row-wff row)))
             (dereference wff nil :if-compound (eq fact-relation (head wff))))
       (with-clock-on printing
         (when (print-time-used?)
           (print-incremental-time-used))
         (terpri)
         (print-row row)
         (princ " "))))
    (:indicate				;ttp 7/29/93
     (with-clock-on printing
       (comment)
       (princ " ")
       (princ (row-name-or-number row))))
    (otherwise
     (with-clock-on printing
       (when (print-time-used?)
	 (print-incremental-time-used))
       (terpri)
       (print-row row)
       (princ " "))))
  row)

(defun print-processed-row (row)
  (case (print-rows-when-processed?)
    ((nil :signal :indicate)
     )
    (otherwise
     (with-clock-on printing
       (when (print-time-used?)
	 (print-incremental-time-used))
       (terpri)
       (print-row row "Processing row ")
       (princ " "))))
  row)

(defvar *printing-deleted-messages* nil)

(defun print-deleted-wff (row msg)
  (case (print-rows-when-derived?)
    ((nil)
     )
    (:signal
     (comment)
     (princ (if (equal "deleted because agenda full" msg) #\d #\-)))
    #+ignore
    (:fact
     (when (let ((wff (row-wff row)))
             (dereference wff nil :if-compound (eq fact-relation (head wff))))
       (with-clock-on printing
         (terpri-comment)
         (format t "     ~A ~A" msg (row-name-or-number row)))))
    (otherwise
     (with-clock-on printing
       (cond
        ((equal *printing-deleted-messages* msg)
         (format t ",~A" (row-name-or-number row)))
        (t
         (terpri-comment)
         (format t "~A ~A" msg (row-name-or-number row))
         (setq *printing-deleted-messages* msg))))))
  row)

(defun print-unorientable-wff (equality-or-equivalence)
  (case (print-unorientable-rows?)
    ((nil :signal :indicate)
     )
    (otherwise
     (with-clock-on printing
       (warn "Could not orient ~S." (print-term equality-or-equivalence nil :string)))))
  equality-or-equivalence)

(defun print-final-row (row)
  (case (print-final-rows?)
    ((nil)
     )
    ((:signal :indicate)
     (comment)
     (princ #\.))
    (otherwise
     (with-clock-on printing
       (terpri)
       (terpri)
       (princ "(Refutation")
       (print-ancestry row)
       (terpri)
       (princ ")"))))
  row)

(defun replace-rows-by-name-or-number (x)
  (cond
   ((consp x)
    (lcons (replace-rows-by-name-or-number (car x)) (replace-rows-by-name-or-number (cdr x)) x))
   ((row-p x)
    (row-name-or-number x))
   (t
    x)))

(defun print-row-reason (row)
  (let* ((reason (row-reason row))
         (rewrites (row-rewrites-used row))
         (reason1 (replace-rows-by-name-or-number reason))
         (reason2 (cond
                   ((null rewrites)
                    reason1)
                   ((and (consp reason1) (eq 'rewrite (first reason1)))
                    (append reason1 (reverse (replace-rows-by-name-or-number rewrites))))
                   (t
                    (list* 'rewrite reason1 (reverse (replace-rows-by-name-or-number rewrites)))))))
    (let ((*print-case* :downcase))
      (prin1 reason2))
    nil))

(defun print-row3 (row *standard-output* depth)
  "this function is used in the defstruct for ROW to print rows."
  (declare (ignore depth))
  (let-options ((print-rows-shortened nil)
		(print-rows-prettily nil)
                (print-row-reasons nil)
		(print-row-answers nil)
		(print-row-constraints nil)
                (print-row-partitions nil))
    (print-row row)))

(defun print-row-length-limit1 (row)
  (let ((n1 (print-rows-shortened?)))
    (and n1
         (let* ((reason (row-reason row))
                (n2 (and (consp reason)
	                 (eq 'resolve (first reason))
	                 (row-p (third reason))
	                 (clause-p (row-wff (third reason)))
	                 (wff-length (row-wff (third reason))))))
           (if (numberp n1)
               (if n2 (min n1 n2) n1)
               n2)))))

(defun print-row (row &optional (string "Row "))
  (when row
    (let ((*print-pretty* nil) (*print-radix* nil) (*print-base* 10.))
      (princ "(")
      (princ string)
      (let ((*print-case* :downcase))
        (prin1 (row-name-or-number row)))
      (cond
       ((print-rows-prettily?)
        (terpri)
        (princ "   "))
       (t
        (princ " ")))
      (let-options ((print-row-length-limit (print-row-length-limit1 row)))
        (print-row-term
         (cond
          ((not (print-row-goals?))
           (prog->
             (map-atoms-in-wff-and-compose-result (row-wff row) ->* atom polarity)
             (declare (ignore polarity))
             (dereference
              atom nil
              :if-constant (if (proposition-magic-goal-p atom) true atom)
              :if-compound (if (relation-magic-goal-p (head atom)) true atom))))
          (t
           (row-wff row)))))
      (when (print-row-reasons?)
        (cond
         ((print-rows-prettily?)
          (terpri)
          (princ "   "))
         (t
          (format t "~70T")))
        (print-row-reason row))
      (when (print-row-constraints?)
        (dolist (x (row-constraints row))
          (unless (eq true (cdr x))
            (terpri)
            (princ "   ")
            (princ (string-capitalize (car x)))
            (princ "-Constraint ")
            (print-row-term (cdr x)))))
      (when (print-row-answers?)
        (let ((answer (row-answer row)))
          (unless (eq false answer)
            (terpri)
            (princ "   Answer ")
            (print-row-term answer))))
      (when (and (use-partitions?) (print-row-partitions?))
        (terpri)
        (princ "   Partitions ")
        (prin1 (mapcar #'car (row-context row))))
      (princ ")")))
  row)

(defun variable-to-lisp (var)
  (let ((variable-to-lisp-function (variable-to-lisp-function?)))
    (if variable-to-lisp-function
        (funcall variable-to-lisp-function var)
        var)))

(defun var-to-lisp (var)
  ;; historical ad hoc default term-to-lisp translation for variables
  (let ((sort (variable-sort var)))
    (if (neq top-sort sort)
	`(var ,(variable-number var) ,sort)
	`(var ,(variable-number var)))))

(defun var-to-lisp2 (var)
  (let ((varsort (variable-sort var))
	(varnum (variable-number var)))
    (cond
      ((neq top-sort varsort)
       (let* ((name (string (sort-name varsort)))
	      (len (length name))
	      (sep (if (digit-char-p (char name (1- len))) "%" "")))
	 (case varnum
	   (0 (intern (format nil "?~A~A" name sep) *package*))
	   (t (intern (format nil "?~A~A~D" name sep varnum) *package*)))))
      (t
       (mvlet (((:values i j) (floor varnum 6)))
         (setq j (case j (0 '?X) (1 '?Y) (2 '?Z) (3 '?U) (4 '?V) (5 '?W)))
         (if (eql 0 i)
             j
             (intern (format nil "~A~D" j i) *package*)))))))

(defun var-to-lisp2a (var)
  (let ((varsort (variable-sort var))
        (varnum (1+ (variable-number var))))
    (cond
      ((neq top-sort varsort)
       (let* ((name (string (sort-name varsort)))
	      (len (length name))
	      (sep (if (digit-char-p (char name (1- len))) "%" "")))
	 (intern (format nil "?~A~A~D" name sep varnum) *package*)))
      (t
       (intern (format nil "?V~D" varnum) *package*)))))

(defun symbol-to-lisp (x)
  (cond
   ((variable-p x)
    (variable-to-lisp x))
   ((function-symbol-p x)
    (function-name x))
   (t
    (constant-name x))))

(defvar *propositional-abstraction-term-to-lisp* nil)

(defun term-to-lisp (term &optional subst)
  "Return a Lisp data structure for the given term."
  ;; returns (f a b c) for SNARK term f(a,b,c)
  ;; returns (list a b c) for SNARK term [a,b,c]
  ;;  use variable-p, variable-number, variable-sort
  ;;  sort information is invalid after SNARK is reinitialized
  (labels
    ((term-to-lisp* (term)
       (dereference
	term subst
	:if-constant (if (or (can-be-free-variable-name-p term) (wild-card-p term))
			 (kwote term)
                         (constant-name term))
	:if-variable (variable-to-lisp term)
	:if-compound-appl (let ((head (heada term)))
                            (cond
                             ((and *propositional-abstraction-term-to-lisp*
                                   (not (function-logical-symbol-p head)))
                              (list (function-name head) (function-arity head)))
                             ((loop for fn in (function-to-lisp-code head)
                                    thereis (funcall fn head (argsa term) subst))
                              )
			     ((or (eq *forall* head)
			          (eq *exists* head))
			      (list (function-name head)
			            (mapcar (lambda (var-spec)
                                              (if (variable-p var-spec)
                                                  (term-to-lisp* var-spec)
                                                  (mapcar #'term-to-lisp* var-spec)))
                                            (arg1 term))
			            (term-to-lisp* (arg2 term))))
                             (t
                              (case (function-arity head)
                                (:alist
                                 (cons (function-name head)
                                       (alist-args-to-lisp (arg1 term))))
                                (:plist
                                 (cons (function-name head)
                                       (plist-args-to-lisp (arg1 term))))
			        (:list*
			         (cons (function-name head)
			               (list*-args-to-lisp (arg1 term))))
                                (otherwise
                                 (cons (function-name head)
                                       (mapcar #'term-to-lisp* (args term))))))))
        :if-compound-cons (let ((x (term-to-lisp* (carc term)))
                                (y (term-to-lisp* (cdrc term))))
                            (cond
                             ((null y)
                              (list 'list x))
                             ((and (consp y) (eq 'cons (first y)))
                              (if (null (third y))
                                  (list 'list x (second y))
                                  (list* 'list* x (rest y))))
                             ((and (consp y) (or (eq 'list (first y)) (eq 'list* (first y))))
                              (list* (first y) x (rest y)))
                             (t
                              (list 'list* x y))))))
     (alist-args-to-lisp (args)
       (dereference
        args subst
        :if-constant nil
        :if-variable (term-to-lisp* args)
        :if-compound (lcons (let ((v (term-to-lisp* (car args))))
                              (ecase (first v)
                                (list
                                 (if (null (cddr v))
                                     (cdr v)
                                     (cons (second v) (cons 'list (cddr v)))))
                                (list*
                                 (if (null (cdddr v))
                                     (cons (second v) (third v))
                                     (cons (second v) (cons 'list* (cddr v)))))))
                            (alist-args-to-lisp (cdr args))
                            args)))
     (plist-args-to-lisp (args)
       (dereference
        args subst
        :if-constant nil
        :if-variable (term-to-lisp* args)
        :if-compound (let ((v (term-to-lisp* (car args)))
                           (l (plist-args-to-lisp (cdr args))))
                       (ecase (first v)
                         (list
                          (if (null (cddr v))
                              (list* (second v) nil l)
                              (list* (second v) (cons 'list (cddr v)) l)))
                         (list*
                          (if (null (cdddr v))
                              (list* (second v) (third v) l)
                              (list* (second v) (cons 'list* (cddr v)) l)))))))
     (list*-args-to-lisp (args)
       (let ((v (term-to-lisp* args)))
	 (cond
          ((and (consp v) (eq 'list* (first v)))
           (rest v))
          ((and (consp v) (eq 'list (first v)))
           (append (rest v) (list nil)))
          (t
           (list v))))))
    (term-to-lisp* term)))

(defun row-sorts (row &optional sorts)
  (prog->
   (map-terms-in-wff (row-wff row) ->* term polarity)
   (declare (ignore polarity))
   (let ((sort (term-sort term)))
     (unless (eq top-sort sort)
       (pushnew (term-sort term) sorts :test #'same-sort-p))))
  sorts)

(defun derivation-sorts (row)
  (let ((sorts nil))
    (dolist (row (row-ancestry row))
      (setq sorts (row-sorts row sorts)))
    sorts))

(defun subsort-forms (sorts)
  (let ((result nil))
    (dotails (l sorts)
      (let ((sort1 (first l)))
	(dolist (sort2 (rest l))
	  (cond
	    ((subsort-p sort1 sort2)
	     (push `(subsort ,(sort-name sort1) ,(sort-name sort2)) result))
	    ((subsort-p sort2 sort1)
	     (push `(subsort ,(sort-name sort2) ,(sort-name sort1)) result))))))
    result))

(defun derivation-subsort-forms (row)
  (subsort-forms (derivation-sorts row)))

;;; output.lisp EOF
