;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: backward-compatibility.lisp
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

(defconstant true-wff true)
(defconstant false-wff false)
(defconstant empty-subst nil)

(defvar *cons-function*)
(defvar *standard-equality-predicate*)
(defvar *standard-negation-connective*)
(defvar *standard-conjunction-connective*)
(defvar *standard-disjunction-connective*)
(defvar *standard-implication-connective*)
(defvar *standard-reverse-implication-connective*)
(defvar *standard-equivalence-connective*)
(defvar *standard-exclusive-or-connective*)
(defvar *standard-conditional-connective*)
(defvar *standard-universal-quantifier*)
(defvar *standard-existential-quantifier*)

(progn
(pushnew '*cons-function* *snark-globals*)
(pushnew '*standard-equality-predicate* *snark-globals*)
(pushnew '*standard-negation-connective* *snark-globals*)
(pushnew '*standard-conjunction-connective* *snark-globals*)
(pushnew '*standard-disjunction-connective* *snark-globals*)
(pushnew '*standard-implication-connective* *snark-globals*)
(pushnew '*standard-reverse-implication-connective* *snark-globals*)
(pushnew '*standard-equivalence-connective* *snark-globals*)
(pushnew '*standard-exclusive-or-connective* *snark-globals*)
(pushnew '*standard-conditional-connective* *snark-globals*)
(pushnew '*standard-universal-quantifier* *snark-globals*)
(pushnew '*standard-existential-quantifier* *snark-globals*)
nil)

(defmacro new-function-name (old-name new-name)
  `(progn
     (export '(,old-name) :snark)
     (defmacro ,old-name (&rest args)
       (warn "~A is obsolete; the current name for this function is ~A."
             ',old-name ',new-name)
       (cons ',new-name args))))

(defmacro new-option-name (old-name new-name)
  `(progn
     (new-function-name ,old-name ,new-name)
     (new-function-name ,(intern (concatenate 'string (symbol-name old-name) "?") :snark)
                        ,(intern (concatenate 'string (symbol-name new-name) "?") :snark))
     (new-function-name ,(intern (concatenate 'string "DEFAULT-" (symbol-name old-name)) :snark)
                        ,(intern (concatenate 'string "DEFAULT-" (symbol-name new-name)) :snark))
     (new-function-name ,(intern (concatenate 'string "DEFAULT-" (symbol-name old-name) "?") :snark)
                        ,(intern (concatenate 'string "DEFAULT-" (symbol-name new-name) "?") :snark))))

(new-function-name id identity)
(new-function-name wff-form row-wff)
(new-function-name empty-subst-p null)
(new-function-name wff-name-or-number row-name-or-number)
(new-function-name wff-named row)
(new-function-name wff-numbered row)
(new-function-name row-named row)
(new-function-name row-numbered row)
(new-function-name wff-weight+depth+ row-weight+depth)
(new-function-name name-a-wff name-row)
(new-function-name declare-subsort-p declare-subsort)
(new-function-name declare-sort-disjoint declare-disjoint-sorts)
(new-function-name print-wff-anc print-row)
(new-function-name print-row-anc print-row)
(new-function-name declare-free-variable declare-variable)
(new-function-name can-be-variable-p can-be-variable-name-p)
(new-function-name can-be-free-variable-p can-be-free-variable-name-p)
(new-function-name can-be-constant-p can-be-constant-name-p)
(new-function-name can-be-sort-p can-be-sort-name-p)
(new-function-name first-item-in-agendas agendas-first)
(new-function-name pop-first-item-from-agendas pop-agendas)
(new-function-name ground-term-p ground-p)
(new-function-name input-constant input-constant-symbol)
(new-function-name map-atoms-of-wff map-atoms-in-wff)
(new-function-name map-atoms-of-wff-and-compose-result map-atoms-in-wff-and-compose-result)
(new-function-name map-terms-of-wff map-terms-in-wff)
(new-function-name map-terms-of-wff-and-compose-result map-atoms-in-wff-and-compose-result)
(new-function-name map-terms-of-atom map-terms-in-atom)
(new-function-name map-terms-of-atom-and-compose-result map-terms-in-atom-and-compose-result)
(new-function-name map-terms-of-term map-terms-in-term)
(new-function-name map-terms-of-term-and-compose-result map-terms-in-term-and-compose-result)
(new-function-name map-terms-of-list-of-terms map-terms-in-list-of-terms)
(new-function-name map-atoms-of-list-of-wffs map-atoms-in-list-of-wffs)
(new-function-name map-terms-of-list-of-terms-and-compose-result map-terms-in-list-of-terms-and-compose-result)
(new-function-name map-atoms-of-list-of-wffs-and-compose-result map-atoms-in-list-of-wffs-and-compose-result)
(new-function-name map-terms-of-list-of-wffs-and-compose-result map-terms-in-list-of-wffs-and-compose-result)
(new-function-name show-options print-options)
(new-function-name show-agenda print-agenda)
(new-function-name show-agendas print-agendas)
(new-function-name show-clocks print-clocks)
(new-function-name show-wffs print-rows)
(new-function-name show-rewrites print-rewrites)
(new-function-name show-symbol-table print-symbol-table)
(new-function-name ancestry row-ancestry)
(new-function-name row-and-ancestors row-ancestry)
(new-function-name delete-nonassertions new-row-context)

(new-option-name use-rewrite-code-for-numbers            use-code-for-numbers)
(new-option-name use-rewrite-code-for-lists              use-code-for-lists)
(new-option-name use-rewrite-code-for-characters         use-code-for-characters)
(new-option-name use-temporal-constraints                use-temporal-reasoning)
(new-option-name use-number-sorts                        use-lisp-types-as-sorts)
(new-option-name rewrite-terms-in-answer                 rewrite-answers)
(new-option-name rewrite-terms-in-constraint             rewrite-constraints)

(new-function-name make-application make-compound)
(new-function-name make-application* make-compound*)
(new-function-name appl-head head)
(new-function-name appl-args args)
(new-function-name functor-name function-name)

(new-function-name function-p function-symbol-p)

(new-function-name make-conjunction  conjoin)
(new-function-name make-conjunction* conjoin*)
(new-function-name make-disjunction  disjoin)
(new-function-name make-disjunction* disjoin*)
(new-function-name make-negation  negate)

(new-function-name checkpoint-constraint-system   checkpoint-theory)
(new-function-name uncheckpoint-constraint-system uncheckpoint-theory)
(new-function-name restore-constraint-system      restore-theory)
(new-function-name constraint-system-closure      theory-closure)
(new-function-name constraint-system-assert       theory-assert)
(new-function-name constraint-system-deny         theory-deny)
(new-function-name constraint-system-truep        theory-truep)
(new-function-name constraint-system-falsep       theory-falsep)
(new-function-name constraint-system-simplify     theory-simplify)
(new-function-name constraint-system-assert2      theory-assert2)
(new-function-name constraint-system-deny2        theory-deny2)

(new-function-name function-connective-p function-logical-symbol-p)

(new-function-name constant-has-author constant-author)
(new-function-name constant-has-source constant-source)
(new-function-name function-has-author function-author)
(new-function-name function-has-source function-source)
(new-function-name row-has-author row-author)
(new-function-name row-has-source row-source)
(new-function-name sort-has-author sort-author)
(new-function-name sort-has-source sort-source)

(new-function-name in-author has-author)
(new-function-name in-documentation has-documentation)
(new-function-name in-source has-source)
(new-function-name in-name has-name)

(defun default-use-support-restriction (&optional (value t))
  (default-assert-supported (not value)))

(defun default-use-support-restriction? ()
  (not (default-assert-supported?)))

(defun use-support-restriction (&optional (value t))
  (assert-supported (not value)))

(defun use-support-restriction? ()
  (not (assert-supported?)))

(defun default-use-ordering-restriction (&optional (value t))
  (warn "The DEFAULT-USE-ORDERING-RESTRICTION function is obsolete and should not be used.")
  (cond
    (value
     (default-use-literal-ordering-with-resolution 'literal-ordering-a)
     (default-use-literal-ordering-with-hyperresolution 'literal-ordering-a)
     (default-use-literal-ordering-with-negative-hyperresolution 'literal-ordering-a)
     (default-use-literal-ordering-with-ur-resolution 'literal-ordering-a)
     (default-use-literal-ordering-with-paramodulation 'literal-ordering-a))
    (t
     (default-use-literal-ordering-with-resolution nil)
     (default-use-literal-ordering-with-hyperresolution nil)
     (default-use-literal-ordering-with-negative-hyperresolution nil)
     (default-use-literal-ordering-with-ur-resolution nil)
     (default-use-literal-ordering-with-paramodulation nil)))
  value)

(defun use-ordering-restriction (&optional (value t))
  (warn "The USE-ORDERING-RESTRICTION function is obsolete and should not be used.")
  (cond
    (value
     (use-literal-ordering-with-resolution 'literal-ordering-a)
     (use-literal-ordering-with-hyperresolution 'literal-ordering-a)
     (use-literal-ordering-with-negative-hyperresolution 'literal-ordering-a)
     (use-literal-ordering-with-ur-resolution 'literal-ordering-a)
     (use-literal-ordering-with-paramodulation 'literal-ordering-a))
    (t
     (use-literal-ordering-with-resolution nil)
     (use-literal-ordering-with-hyperresolution nil)
     (use-literal-ordering-with-negative-hyperresolution nil)
     (use-literal-ordering-with-ur-resolution nil)
     (use-literal-ordering-with-paramodulation nil)))
  value)

(defun allow-keyword-predicate-symbols (&optional (value t))
  (allow-keyword-relation-symbols value))

(defun allow-keyword-predicate-symbols? ()
  (allow-keyword-relation-symbols?))

(defun default-allow-keyword-predicate-symbols (&optional (value t))
  (default-allow-keyword-relation-symbols value))

(defun default-allow-keyword-predicate-symbols? ()
  (default-allow-keyword-relation-symbols?))

(defun cycl-package-name? ()
  (package-name (cycl-package)))

(defun km-package-name? ()
  (package-name (km-package)))

(declare-snark-option allow-subclass-of-sort-symbols t :never-print)

(export '(use-support-restriction
          use-support-restriction?
          default-use-support-restriction
          default-use-support-restriction?
          use-ordering-restriction
          use-ordering-restriction?
          default-use-ordering-restriction
          default-use-ordering-restriction?
          allow-keyword-predicate-symbols
          allow-keyword-predicate-symbols?
          default-allow-keyword-predicate-symbols
          default-allow-keyword-predicate-symbols?
          delete-nonassertions
          cycl-package-name?
          km-package-name?)
        :snark)

(export '(mes::make-table)
        :mes)

(defun initialize-backward-compatibility ()
  (setq *cons-function*                           *cons*)
  (setq *standard-equality-predicate*             *=*)
  (setq *standard-negation-connective*            *not*)
  (setq *standard-conjunction-connective*         *and*)
  (setq *standard-disjunction-connective*         *or*)
  (setq *standard-implication-connective*         *implies*)
  (setq *standard-reverse-implication-connective* *implied-by*)
  (setq *standard-equivalence-connective*         *iff*)
  (setq *standard-exclusive-or-connective*        *xor*)
  (setq *standard-conditional-connective*         *if*)
  (setq *standard-universal-quantifier*           *forall*)
  (setq *standard-existential-quantifier*         *exists*)
  (let-options ((allow-keyword-constant-symbols t)
		(allow-keyword-function-symbols t)
		(allow-keyword-proposition-symbols t)
		(allow-keyword-relation-symbols t))
    (declare-proposition false                    :alias :false)
    (declare-proposition true                     :alias :true)
    (declare-relation (function-name *=*) :any    :alias '(:=))
    (declare-relation '/= :any                    :alias :/=)
    (declare-function 'list :any                  :alias 'listof)
    (declare-logical-symbol (function-name *not*)        :alias :not)
    (declare-logical-symbol (function-name *and*)        :alias :and)
    (declare-logical-symbol (function-name *or*)         :alias :or)
    (declare-logical-symbol (function-name *implies*)    :alias :implies)
    (declare-logical-symbol (function-name *implied-by*) :alias :implied-by)
    (declare-logical-symbol (function-name *iff*)        :alias '(:iff :<=>))
    (declare-logical-symbol (function-name *xor*)        :alias :xor)
    (declare-logical-symbol (function-name *if*)         :alias :if)
    (declare-logical-symbol (function-name *answer-if*)  :alias :answer-if)
    (declare-logical-symbol (function-name *forall*)     :alias '(:forall all))
    (declare-logical-symbol (function-name *exists*)     :alias '(:exists some))
    (declare-logical-symbol '=>                          :alias :=>)
    (declare-logical-symbol '<=                          :alias :<=)
    (declare-logical-symbol 'nand                        :alias :nand)
    (declare-logical-symbol 'nor                         :alias :nor))
  nil)

;;; usages of these function can be replaced by using :allowed-in-answer
;;; specification in declare-constant, declare-function, declare-relation

(defun set-nonprimitive-constants (&rest nonprims)
  (assert-nonprimitive-constants nonprims))

(defun set-nonprimitive-functions (&rest nonprims)
  (assert-nonprimitive-functions nonprims))

;;;: ttp: 04/18/95 new, modeled after set-nonprimitive-constants
(defun assert-nonprimitive-constants (nonprims)
  (dolist (consym nonprims)
    (let ((symbol (input-symbol consym)))
      (if (not (function-symbol-p symbol))
	  (setf (constant-allowed-in-answer symbol) nil)
	  (error "Treating a function ~A as a constant." symbol)))))

;;;: ttp: 04/18/95 new, modeled after set-nonprimitive-functions
(defun assert-nonprimitive-functions (nonprims)
  (dolist (fnsym nonprims)
    (let ((symbol (input-symbol fnsym)))
      (if (function-symbol-p symbol)
	  (setf (function-allowed-in-answer symbol) nil)
	  (error "Treating a constant ~A as a function." symbol)))))

(defun function-sort (symbol)
  ;; this tries to fake the functionality of the old function-sort slot at
  ;; least for the cases when old-style function sort declarations were used
  (mapcar (lambda (fsd)
            (cons (if (function-boolean-valued-p symbol)
                      (declare-sort* 'boolean)
                      (fsd-result-sort fsd))
                  (let ((alist (fsd-argument-sort-alist fsd))
                        (arg-sorts nil))
                    (dotimes (i 10000)
                      (unless (eql 0 i)
                        (let ((v (assoc i alist)))
                          (if v
                              (push (cdr v) arg-sorts)
                              (return (nreverse arg-sorts)))))))))
          (function-sort-declarations symbol)))

(defun free-variables (wff)
  (prog->
   (input-wff wff -> wff1 dp-alist1)
   (input-wff wff -> wff2 dp-alist2)
   (intersection (variables wff1 nil (variables dp-alist1))
		 (variables wff2 nil (variables dp-alist2)))))

(new-function-name assert-quote-arg assertion-wff)
(new-function-name convert-km-assertion-file-to-cycl read-km->cycl-assertion-file)

(defun assert-arg (x)
  (cond
   ((and (consp x) (eq 'assertion (car x)) (consp (cdr x)))
    (kwote (second x)))
   ((and (consp x) (eq 'assert (car x)) (consp (cdr x)))
    (second x))
   (t
    (error "value ~S is not of the expected form (ASSERT expr ...)." x))))

(defun quote-arg (x)
  (cond
   ((and (consp x) (eq 'quote (car x)) (consp (cdr x)) (null (cddr x)))
    (second x))
   (t
    (error "value ~S is not of the expected form (QUOTE expr)." x))))

#||
;;; Thomas Pressburger modified the output code to optionally use
;;; a pretty-printer for printing wffs via these functions.

;;; pretty-printer calls (e.g., pp-bp) may need to be fixed in
;;; my code to improve the appearance of pretty-printed output,
;;; since I usually don't use it - MES

(defparameter *pp-margin* 78)

(defvar *pp?* nil
  "Whether to use the prettyprinter after all.")

(defun toggle-pp ()
  "sometimes it's better off when debugging?"
  (setq *pp?* (not *pp?*)))

(defun pp-string (str)
  (if *pp?* (pp::string-out str) (princ str)))

(defun pp-num (num)
  (if *pp?* (pp::num-out num) (princ num)))

(defun pp-symbol (sym)
  (if *pp?* (pp::symbol-out sym) (princ sym)))

;;;: ttp: 6/24/93 12:36 new
(defun pp-thing (thing)
  (if *pp?* (pp::thing-out thing) (format t "~A" thing)))

(defmacro pp-format (control-string &rest args)
  `(funcall (if *pp?* #'pp::string-out #'identity)
	    (format (if *pp?* nil t) ,control-string ,@args)))

(defmacro pp-format2 (control-string pp-control-string &rest args)
  `(funcall (if *pp?* #'pp::string-out #'identity)
	    (format (if *pp?* nil t) (if *pp?* ,pp-control-string ,control-string) ,@args)))

(defun pp-bp (indentation united?)
  (when *pp?*
    (pp::bp indentation united?)))

(defmacro pp-init-finish (margin &rest forms)
  `(unwind-protect
       (progn
	 (when *pp?*
	   (pp::pp-init ,margin))
	 ,@forms)
     (when *pp?*
       (pp::pp-finish))))

(defmacro pp-setb-endb (&rest forms)
  `(unwind-protect
       (progn
	 (when *pp?*
	   (pp::setb))
	 ,@forms)
     (when *pp?*
       (pp::endb))))

(defun pp-thing-list (lst mapfn &optional (obj? T))
  (unless (null lst)
    (labels
      ((plst
	  ()
	 (pp-thing (funcall mapfn (car lst)))
	 (dolist (x (cdr lst))
	   (pp-string ", ")
	   (pp-bp 0 nil)
	   (pp-thing (funcall mapfn x )))))
      (if obj? (pp-setb-endb (plst)) (plst)))))

;;;: ttp: 4/23/96 optional stream and depth (depth doesn't seem to do anything)
;;;: ttp: 5/9/96 need to bind *standard-output* because pp-finish
;; under pp-init-finish prints leftover items in the buffer
(defun pterm (term &optional (*standard-output* *standard-output*) depth)
  "Useful for printing out the answer term."
  (pp-init-finish *pp-margin* (print-term term nil *standard-output* depth)))

(defun pp-test (margin)
  "Test it on the problem of printing
   `fooblebar(firstarg,secondargument,thirdargument)'
   with a given margin."

  ;; Initialize the prettyprinter with the specified margin.
  (pp-init-finish
   margin

   ;; pp-setb-endb delimits an `object'.  The prettyprinter tries
   ;; to keep the object on one line.
   (pp-setb-endb

    ;; pp-string outputs the given string.  There's also NUM-OUT.
    (pp-string "fooblebar")

    ;; pp-bp indicates a possible place for a new line, if the object in
    ;; which it is embedded does not fit on one line.  If it is
    ;; necessary to `break' the object, a new line is started here, and
    ;; indented 2 past where the indentation where the object began;
    ;; i.e. the indentation where the `f' in fooblebar was printed.  A T
    ;; instead of a NIL means that this would be a `united' breakpoint.  If ANY
    ;; break point (at the same level) needs to be broken, then this
    ;; one will also be broken.  An example of its use would be to place it
    ;; before statements in a Pascal `begin-end' block.  Usually if the
    ;; whole block doesn't fit on one line, each statement is on its
    ;; own line.
    (pp-bp 2 nil)
    (pp-setb-endb
     (pp-string "(")
     (pp-string "firstarg")
     (pp-string ",")
     (pp-bp 1 nil);; The 1 spaces past the left-paren
     (pp-string "secondargument")
     (pp-string ",")
     (pp-bp 1 nil)
     (pp-string "thirdargument")
     (pp-string ")")
     )
    )
   ;; The prettyprinting algorithm relies on buffering, and
   ;; e.g. if everything so far fits on a line, it will be waiting for more
   ;; input before it prints the line.  PP-FINISH flushes the buffers,
   ;; but PP-INIT-FINISH does this anyway.
   ;;(pp-finish).  
   ))
||#

;;; backward-compatibility.lisp EOF
