;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: rewrite.lisp
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

(declaim (special *subsuming* *frozen-variables* *processing-row*))

(defstruct (rewrite
	     (:constructor make-rewrite (row pattern value condition pattern-symbol-count new-value-variables polarity)))
  row
  pattern
  value
  condition
  pattern-symbol-count
  new-value-variables
  (embeddings nil)
  (polarity nil)
  )

(defvar *redex-path* nil)	;(polarity-n function-n ... polarity-1 function-1)

(defvar *rewrite-cache*)
(defvar *rewrite-cache-hits* 0)
(defvar *rewrite-cache-misses* 0)

(defun use-rewrite-cache? ()
  ;; totally disabled now
  nil)

(defun clear-rewrite-cache ()
  (let ((n (use-rewrite-cache?)))
    (setq *rewrite-cache* (if n (make-assoc-cache n) nil)))
  nil)

(defun clear-rewrite-cache-statistics ()
  (setq *rewrite-cache-hits* 0)
  (setq *rewrite-cache-misses* 0)
  nil)

(defun add-to-rewrite-cache (term value simplifiers)
  (assoc-cache-push term (list value simplifiers) *rewrite-cache*))

(defun rewrite-cache-value (x)
  (let ((v (or (assoc x *rewrite-cache*)
	       (assoc x *rewrite-cache* :test #'equal-p))))
    (cond
      (v
       (incf *rewrite-cache-hits*)
       (second v))
      (t
       (incf *rewrite-cache-misses*)
       none))))

(defun print-rewrite-cache ()
  (let ((n (use-rewrite-cache?)))
    (when n
      (let ((l (assoc-cache-entries *rewrite-cache*)))
	(terpri-comment)
	(format t "Rewrite cache contains ~D/~D entries~:[.~;:~]" (length l) n l)
	(dolist (x l)
	  (terpri-comment)
	  (princ "   ")
	  (print-term (first x))
	  (princ "   is   ")
	  (print-term (second x))
	  ;; print simplifiers, when we know what format to use
	  )))))

;;;: ttp: 07/28/94 new
(defvar *trace-rewrites?* nil
  "When T, when a term is rewritten, the before and after form are printed.")

;;;: ttp: 07/28/94 new
(defun trace-rewrite1 (rewrite-row term rewritten-term)
  (when *trace-rewrites?*
    (terpri)
    (terpri-comment)
    (format T "Rewrite ~a applied to:" (row-name-or-number rewrite-row))
    (terpri-comment)
    (print-term term)
    (terpri-comment)
    (format T "resulted in:")
    (terpri-comment)
    (print-term rewritten-term)
    (terpri)
    )
  rewritten-term
  )

(defun rewrite-patterns-and-values (function pattern value pattern-symbol-count embeddings symbol-count)
  ;; calls function with rewrite's pattern and value, and patterns and values for any embeddings,
  ;; provided size of the pattern does not exceed size of the term
  (prog->
    (when (symbol-count-not-greaterp pattern-symbol-count symbol-count)
      (funcall function pattern value)
      (when embeddings
	(- (symbol-count-total symbol-count) (symbol-count-total pattern-symbol-count) -> size-difference)
	(unless (< size-difference 2)
	  (dereference pattern nil)
	  (head pattern -> head)
          (associative-function-argument-sort head -> sort)
	  (make-variable sort -> newvar1)
	  (ecase embeddings
	    (:l
	     (funcall function
		      (make-compound head newvar1 pattern)	;left embedding
		      (make-compound head newvar1 value)))
            (:r
             (funcall function
                      (make-compound head pattern newvar1)	;right embedding
                      (make-compound head value newvar1)))
	    (:l&r
	     (funcall function
		      (make-compound head newvar1 pattern)	;left embedding
		      (make-compound head newvar1 value))
	     (funcall function
		      (make-compound head pattern newvar1)	;right embedding
		      (make-compound head value newvar1))
	     (unless (< size-difference 4)
	       (make-variable sort -> newvar2)
	       (funcall function
			(make-compound head newvar1 pattern newvar2)	;left & right embedding
			(make-compound head newvar1 value newvar2))))))))))

(defvar *rewrites-used*)

(defvar rewrite-strategy :innermost)
;; options:
;;  :innermost  simplifies subterms first
;;  :outermost  tries to simplify outer terms first, subterms in left-to-right order otherwise

(defvar fully-rewritten-compounds)

(defun redex-at-top? ()
  (null *redex-path*))

(defun redex-polarity (&optional (rp *redex-path*))
  (if (null rp)
      :pos
      (first rp)))

(defun set-redex-polarity (polarity)
  (setf (first *redex-path*) polarity))

(defun redex-literal? (&optional (rp *redex-path*))
  (or (null rp)
      (and (eq 'not (function-logical-symbol-p (second rp)))
           (redex-literal? (cddr rp)))))

(defun redex-clause? (&optional (rp *redex-path*))
  (or (null rp)
      (and (redex-clause? (cddr rp))
           (let ((c (function-logical-symbol-p (second rp))))
             (or (not c)
                 (case c
                   (not
                    t)
                   (and
                    (eq :neg (redex-polarity (cddr rp))))
                   (or
                    (eq :pos (redex-polarity (cddr rp))))
                   (implies
                    (eq :pos (redex-polarity (cddr rp))))
                   (implied-by
                    (eq :pos (redex-polarity (cddr rp))))
                   (otherwise
                    nil)))))))

(defun rewriter (term subst)
  (dereference
    term subst
    :if-variable term
    :if-constant (if (or (eq true term) (eq false term))
		     term
		     (ecase rewrite-strategy
		       (:innermost
			 (rewrite-innermost term subst nil))
		       (:outermost
			 (rewrite-outermost term subst nil))))
    :if-compound (let ((*subsuming* t)
                       (*frozen-variables* (variables term subst *frozen-variables*))
		       FULLY-REWRITTEN-COMPOUNDS)
		   (ecase rewrite-strategy
;;		     (:innermost
;;		       (rewrite-innermost term subst nil))
		     (:innermost		;rewrite at top first, then do innermost simplification
		       (let ((term* (rewrite-compound term subst (head term))))
			 (cond
			   ((eq none term*)
			    (rewrite-innermost term subst :top))
			   ((or (eq true term*) (eq false term*))
			    term*)
			   (t
			    (rewrite-innermost term* subst nil)))))
		     (:outermost
		       (rewrite-outermost term subst nil))))))

(defun rewrite-constant (term subst)
  ;; it is assumed that the lhs of any applicable rewrite must be identical to term
  (prog->
    (dolist (rewrites term) ->* rewrite)
    (rewrite-row rewrite -> w)
    (rewrite-condition rewrite -> cond)
    (when (and (implies w (eq t (context-subsumption-p (row-context w) *rewriting-row-context*)))
               (or (eq cond t) (funcall cond (rewrite-pattern rewrite) (rewrite-value rewrite) subst))
               (term-subsort-p (rewrite-value rewrite) term subst))
      (pushnew-unless-nil w *rewrites-used*)
      (return-from rewrite-constant
        (rewrite-value rewrite))))
  none)

(defun rewrite-compound (term subst head)
  (let* ((funs (function-rewrite-code head))
	 (v (if funs (rewrite-compound-by-code term subst funs) none)))
    (cond
      ((neq none v)
       v)
      ((function-rewritable-p head)
       (rewrite-compound-by-rule term subst (symbol-count term subst)))
      (t
       none))))

(defun rewrite-compound-by-code (term subst funs)
  (dolist (fun funs none)
    (let ((result (funcall fun term subst)))
      (when (and (neq none result) (term-subsort-p result term subst))
        (let ((head (head term)))
          (pushnew-unless-nil
           (and (not (function-logical-symbol-p head))
                (function-code-name head))
           *rewrites-used*))
	(return result)))))

(defun rewrite-compound-by-rule (term subst symbol-count)
  (prog->
    ;; ASSUME THAT IF EMBEDDED REWRITE IS NEEDED, ITS UNEMBEDDED FORM WILL BE RETRIEVED
    (when (trace-rewrite?)
      (format t "~2%; REWRITE-COMPOUND-BY-RULE will try to rewrite~%;   ~A." (term-to-lisp term subst)))
    (retrieve-generalization-entries term subst #'tme-rewrites ->* e rewrites)
    (declare (ignore e))
    (dolist rewrites ->* rewrite)
    (rewrite-row rewrite -> w)
    (when (and (implies w (eq t (context-subsumption-p (row-context w) *rewriting-row-context*)))
               (implies (rewrite-polarity rewrite)
                        (eq (rewrite-polarity rewrite) (redex-polarity))))
      (rewrite-condition rewrite -> cond)
      (rewrite-pattern rewrite -> pattern)
      (rewrite-value rewrite -> value)
      (when (trace-rewrite?)
        (format t "~%; Try ~A -> ~A." (term-to-lisp pattern) (term-to-lisp value)))
      (rewrite-pattern-symbol-count rewrite -> pattern-symbol-count)
      (QUOTE NIL -> V)
      (COND
	((AND (SETQ V (AC-INVERSE-RULE-P PATTERN VALUE COND subst))
	      (SETQ V (APPLY-AC-INVERSE-RULE (ARGS TERM) (CAR V) (CADR V) (CADDR V) subst)))
	 (RETURN-FROM REWRITE-COMPOUND-BY-RULE V))
	(T
	 (rewrite-patterns-and-values
	   pattern
	   value
	   pattern-symbol-count
	   (rewrite-embeddings rewrite)
	   symbol-count
	   ->* pattern* value*)
	 (when (trace-rewrite?)
	   (format t "~%; Try ~A LHS." (term-to-lisp pattern*))
;;	   (format t "~%; FROZEN:    ") (print-terms (setf *frz* *frozen-variables*))
;;	   (format t "~%; PATTERN*:  ") (print-term (setf *pat* pattern*))
;;	   (format t "~%; TERM:      ") (print-term (setf *trm* term))
;;	   (format t "~%; SUBST:     ") (print-terms (setf *subst* subst))
;;	   (format t "~%; Unifiable: ") (unless (prin1 (unify-p pattern* term subst)) (break))
	   )
	 (unify pattern* term subst ->* subst)
	 (when (and (or (eq cond t) (funcall cond pattern value subst))	;CHECK ORDER OF UNEMBEDDED REWRITE
                    (term-subsort-p value* pattern* subst))
	   (pushnew-unless-nil w *rewrites-used*)
	   (dolist (var (rewrite-new-value-variables rewrite))
	     (let ((v (make-variable (variable-sort var))))
	       (setq subst (bind-variable-to-term var v subst))
	       (push v *frozen-variables*)))
	   (instantiate value* subst -> term*)
	   (when (trace-rewrite?)
	     (format t "~%; REWRITE-COMPOUND-BY-RULE rewrote it to~%;  ~A." (term-to-lisp term* subst)))
	   (return-from rewrite-compound-by-rule
	     term*))))))
  (when (trace-rewrite?)
    (format t "~%; REWRITE-COMPOUND-BY-RULE failed to rewrite it."))
  none)

(defun rewrite-list (term subst)
  (rewrite-list-by-rule term subst (symbol-count term subst)))

(defun rewrite-list-by-rule (term subst symbol-count)
  (prog->
    (retrieve-generalization-entries term subst #'tme-rewrites ->* e rewrites)
    (declare (ignore e))
    (dolist rewrites ->* rewrite)
    (rewrite-row rewrite -> w)
    (when (implies w (eq t (context-subsumption-p (row-context w) *rewriting-row-context*)))
      (rewrite-condition rewrite -> cond)
      (rewrite-pattern rewrite -> pattern)
      (rewrite-value rewrite -> value)
      (rewrite-pattern-symbol-count rewrite -> pattern-symbol-count)
      (rewrite-patterns-and-values
       pattern
       value
       pattern-symbol-count
       (rewrite-embeddings rewrite)
       symbol-count
       ->* pattern* value*)
      (unify pattern* term subst ->* subst)
      (when (and (or (eq cond t) (funcall cond pattern value subst))	;CHECK ORDER OF UNEMBEDDED REWRITE
                 (term-subsort-p value* pattern* subst))
        (pushnew-unless-nil w *rewrites-used*)
        (dolist (var (rewrite-new-value-variables rewrite))
          (let ((v (make-variable (variable-sort var))))
            (setq subst (bind-variable-to-term var v subst))))
        (instantiate value* subst -> term*)
        (when *trace-rewrites?*
          (trace-rewrite1 w term term*))
        (return-from rewrite-list-by-rule
          term*))))
  none)

(defvar *rewrite-count-warning* t)

(defmacro rewrite-*most (appl-code)
  `(block rewrite-*most
     (let ((term original-term) (count 0) v)
       (loop
	 (when *rewrite-count-warning*
	   (when (and (= (rem count 1000) 0) (/= count 0))
	     (warn "~A has been rewritten ~D times;~%value now is ~A."
		   (print-term original-term subst :string)
		   count
		   (print-term term subst :string))))
	 (incf count)
	 (dereference
	   term subst
	   :if-variable (progn
			  (when (use-rewrite-cache?)
			    (unless (eql original-term term)
			      (add-to-rewrite-cache original-term term NIL)))
			  (return-from rewrite-*most term))
	   :if-constant (cond
			  ((or (eq true term) (eq false term))
			   (when (use-rewrite-cache?)
			     (unless (eql original-term term)
			       (add-to-rewrite-cache original-term term NIL)))
			   (return-from rewrite-*most term))
			  ((and (use-rewrite-cache?)
				(neq none (setq v (rewrite-cache-value term))))
			   (unless (eql original-term term)
			     (add-to-rewrite-cache original-term v NIL))
			   (return-from rewrite-*most v))
			  (t
			   (let ((result (rewrite-constant term subst)))
			     (cond
			       ((neq none result)
				(setq term result))
			       (t
				(when (use-rewrite-cache?)
				  (add-to-rewrite-cache original-term term NIL))
				(return-from rewrite-*most term))))))
	   :if-compound (cond
			  ((MEMBER TERM FULLY-REWRITTEN-COMPOUNDS :TEST #'EQ)
			   (RETURN-FROM REWRITE-*MOST TERM))
			  ((and (use-rewrite-cache?)
				(neq none (setq v (rewrite-cache-value term))))
			   (unless (eq original-term term)
			     (add-to-rewrite-cache original-term v NIL))
			   (return-from rewrite-*most v))
			  (t
			   ,appl-code)))))))

(defun eq-args (term args)
  (dereference
   term nil
   :if-compound-cons (and (eql (carc term) (first args))
	                  (eql (cdrc term) (second args)))
   :if-compound-appl (eq (argsa term) args)))

(defun rewrite-innermost (original-term subst head-if-associative)
  ;; requires that original-term be fully dereferenced IF REWRITE CACHE IS USED
  ;; (otherwise, input-outputs of dereferencing put into rewrite cache)
  (rewrite-*most
    (let ((head (head term))
	  (args (args term))
	  args*)
      (cond
	((or (null args)
	     (eq args (setq args* (let ((*redex-path* (list* nil head *redex-path*)))
				    (rewrite-list-innermost
				     args subst
				     (if (function-associative head) head nil)
				     (function-polarity-map head))))))
	 )
	(t
	 (setq term (FANCY-make-compound* head args*))))
      (dereference term subst)
      (cond
	((not (and (compound-p term)		;FANCY-make-compound changed it?
		   (eq (head term) head)
		   (eq-args term args*)))
	 (when (eq :top head-if-associative)
	   (setq head-if-associative nil)))
	((and (eq :top head-if-associative)
	      (progn (setq head-if-associative nil) t)
	      (compound-p term)
	      (eq (head term) head)
	      (eq-args term args))
	 (return-from rewrite-*most term))
	((and head-if-associative (eq head head-if-associative))
	 (return-from rewrite-*most term))
	(t
	 (let ((result (rewrite-compound term subst head)))
	   (cond
	     ((neq none result)
	      (setq term result))
	     (t
	      (when (use-rewrite-cache?)
		(add-to-rewrite-cache original-term term NIL))
	      (PUSHNEW TERM FULLY-REWRITTEN-COMPOUNDS :TEST #'EQ)
	      (return-from rewrite-*most term)))))))))

(defun rewrite-outermost (original-term subst head-if-associative)
  ;; requires that original-term be fully dereferenced IF REWRITE CACHE IS USED
  ;; (otherwise, input-outputs of dereferencing put into rewrite cache)
  (rewrite-*most
    (let ((head (head term)))
      (cond
	((and head-if-associative (eq head head-if-associative))
	 (let ((args (args term)) args*)
	   (cond
	     ((or (null args)
		  (eq args (setq args* (let ((*redex-path* (list* nil head *redex-path*)))
					 (rewrite-list-outermost
					  args subst
					  (if (function-associative head) head nil)
					  (function-polarity-map head))))))
	      (return-from rewrite-*most term))
	     (t
	      (setq term (FANCY-make-compound* head args*))))))
	(t
	 (let ((result (rewrite-compound term subst head)))
	   (cond
	     ((neq none result)
	      (setq term result))
	     (t
	      (let ((args (args term)) args*)
		(cond
		  ((or (null args)
		       (eq args (setq args* (rewrite-list-outermost
					      args subst
					      (if (function-associative head) head nil)
					      (function-polarity-map head)))))
		   (when (use-rewrite-cache?)
		     (add-to-rewrite-cache original-term term NIL))
		   (return-from rewrite-*most term))
		  (t
		   (setq term (FANCY-make-compound* head args*)))))))))))))

(defun rewrite-list-innermost (terms subst head-if-associative polarity-map &optional rewrite-alist)
  ;; rewrite nonempty list of terms, using innermost simplification first
  (let* ((x (first terms))
	 (newly-simplified nil)
	 (x* (or (cdr (assoc x rewrite-alist :test (lambda (x y) (equal-p x y subst))))
		 (progn
		   (setq newly-simplified t)
                   (set-redex-polarity (map-polarity (first polarity-map) (redex-polarity (cddr *redex-path*))))
		   (rewrite-innermost x subst head-if-associative))))
	 (y (rest terms)))
    (lcons x*
	   (rewrite-list-innermost y subst head-if-associative (rest polarity-map)
				   (if newly-simplified
				       (acons x x* rewrite-alist)
				       rewrite-alist))
	   terms)))

(defun rewrite-list-outermost (terms subst head-if-associative polarity-map)
  ;; rewrite nonempty list of terms, using outermost simplification first
  (let* ((x (first terms))
	 (x* (progn
               (set-redex-polarity (map-polarity (first polarity-map) (redex-polarity (cddr *redex-path*))))
               (rewrite-outermost x subst head-if-associative))))
    (cond
      ((neql x* x)
       (cons x* (rest terms)))
      (t
       (let ((y (rest terms)))
	 (cond
	   ((null y)
	    terms)
	   (t
	    (let ((y* (rewrite-list-outermost y subst head-if-associative (rest polarity-map))))
	      (if (eq y* y) terms (cons x* y*))))))))))

(defun ac-inverse-rule-p (pattern value cond subst)
  (and
    (eq cond t)
    (ground-p value subst)
    (dereference
      pattern subst
      :if-compound (let ((f (head pattern)))
		     (and
		       (function-associative f)
		       (function-commutative f)
		       (let ((args (args pattern)))
			 (and
			   (= (length args) 2)
			   (let ((arg1 (first args)) (arg2 (second args)))
			     (match-term
			       arg1 arg2 subst
			       :if-variable*compound (let ((g (head arg2)))
						       (and
							 (eql (function-arity g) 1)
							 (equal-p arg1 (arg1 arg2) subst)
							 (list f g value)))
			       :if-compound*variable (let ((g (head arg1)))
						       (and
							 (eql (function-arity g) 1)
							 (equal-p arg2 (arg1 arg1) subst)
							 (list f g value))))))))))))

(defun apply-ac-inverse-rule (args f g e subst)
  ;; f(x,g(x)) -> e
  (apply-ac-inverse-rule* (count-arguments f args subst) f g e subst))

(defun apply-ac-inverse-rule* (terms-and-counts f g e subst)
  (prog->
    (dolist terms-and-counts ->* tc)
    (when (> (tc-count tc) 0)
      (tc-term tc -> term)
      (when (dereference term subst :if-compound (eq g (head term)))
	(recount-arguments f
			   (list* (make-tc term -1)
				  (make-tc (arg1 term) -1)
				  (make-tc e 1)
				  terms-and-counts)
			   subst
			   -> new-terms-and-counts)
	(when (loop for tc in new-terms-and-counts
		    never (< (tc-count tc) 0))
	  (return-from apply-ac-inverse-rule*
	    (or
	      (apply-ac-inverse-rule* new-terms-and-counts f g e subst)
	      (let ((args nil))
		(prog->
		  (dolist new-terms-and-counts ->* tc)
		  (setq args (consn (tc-term tc) args (tc-count tc))))
		(make-a1-compound* f nil args))))))))
  nil)

;;; rewrite.lisp EOF
