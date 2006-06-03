(in-package "LISP")

(#+sbcl sb-ext:without-package-locks #-sbcl progn

(defun eval (original-exp)
  "Evaluates its single arg in a null lexical environment, returns the
  result or results."
  (declare (optimize (safety 1)))
  (let ((exp (macroexpand original-exp)))
    (typecase exp
      (symbol
       (ecase (info variable kind exp)
	 (:constant
	  (values (info variable constant-value exp)))
	 ((:special :global)
	  (symbol-value exp))
	 ((:alien :macro)
	  (eval:internal-eval original-exp))))
      (list
       (let ((name (first exp))
	     (args (1- (length exp))))
	 (case name
	   (function
	    (unless (= args 1)
	      (error 'simple-program-error
		     :format-control "Wrong number of args to FUNCTION:~% ~S."
		     :format-arguments (list exp)))
	    (let ((name (second exp)))
	      (cond ((consp name)
		     (if (valid-function-name-p name)
			 (fdefinition name)
		       (eval:make-interpreted-function name)))
		    ((macro-function name)
		     (error 'simple-type-error
			    :datum name
			    :expected-type '(not (satisfies macro-function))
			    :format-control "~S is a macro."
			    :format-arguments (list name)))
		    ((special-operator-p name)
		     (error 'simple-type-error
			    :datum name
			    :expected-type '(not
					     (satisfies special-operator-p))
			    :format-control "~S is a special operator."
			    :format-arguments (list name)))
		    (t
		     (fdefinition name)))))
	   (quote
	    (unless (= args 1)
	      (error 'simple-program-error
		     :format-control "Wrong number of args to QUOTE:~% ~S."
		     :format-arguments (list exp)))
	    (second exp))
	   (if (unless (or (= args 2) (= args 3))
	      (error 'simple-program-error
		     :format-control "Wrong number of args to IF:~% ~S."
		     :format-arguments (list exp)))
	       (if (eval (second  exp))
		   (eval (third exp))
		 (eval (fourth exp))))
	   (setq
	    (unless (evenp args)
	      (error 'simple-program-error
		     :format-control "Odd number of args to SETQ:~% ~S."
		     :format-arguments (list exp)))
	    (unless (zerop args)
	      (do ((name (cdr exp) (cddr name)))
		  ((null name)
		   (do ((args (cdr exp) (cddr args)))
		       ((null (cddr args))
			;; We duplicate the call to SET so that the correct
			;; value gets returned.
			(set (first args) (eval (second args))))
		     (set (first args) (eval (second args)))))
		(let ((symbol (first name)))
		  (case (info variable kind symbol)
		    (:special)
		    (:global
		     (case *top-level-auto-declare*
		       (:warn
			(warn "Declaring ~S special." symbol))
		       ((t))
		       ((nil)
			(return (eval:internal-eval original-exp))))
		     (proclaim `(special ,symbol)))
		    (t
		     (return (eval:internal-eval original-exp))))))))
	   ((progn)
	    (when (> args 0)
	      (dolist (x (butlast (rest exp)) (eval (car (last exp))))
		(eval x))))
	   ((eval-when)
	    (if (and (> args 0)
		     (or (member 'eval (second exp))
			 (member :execute (second exp))))
		(when (> args 1)
		  (dolist (x (butlast (cddr exp)) (eval (car (last exp))))
		    (eval x)))
		(eval:internal-eval original-exp)))
	   (t
	    (if (and (symbolp name)
		     (eq (info function kind name) :function))
		(collect ((args))
		  (dolist (arg (rest exp))
		    (args (eval arg)))
		  (apply (symbol-function name) (args)))
		(eval:internal-eval original-exp))))))
      (t
       exp))))
)

;; oops, test code got checked in...
;; see cmucl/18e/src/code/fdefinition.lisp for real definition
;; (defun valid-function-name-p (name) (symbolp name))

