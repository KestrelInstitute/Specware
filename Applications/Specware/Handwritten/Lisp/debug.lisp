;;; Utilities for help in debugging MetaSlang programs in Lisp
(in-package "CL-USER")

;; When the following boolean is true, then all exceptions (not just Fail)
;; take the user into the Lisp debugger.
(defvar SpecCalc::specwareWizard? nil)

#+allegro
(defun quiet-do-command (&rest args)
  (let ((top-level:*auto-zoom* nil)
	(top-level:*print-level* 0))
    (apply #'top-level:do-command args)))

#+allegro
(defun if-break-move-to-caller ()
  (let ((fm (quiet-do-command "curr")))
    (if (member (car fm) '(break))
	(progn (quiet-do-command "dn" 1)
	       (if-break-move-to-caller))
      fm)))

#+allegro
(setq debug::*hidden-functions*
  (union debug::*hidden-functions*
	 '(excl::fwrap-hook excl::trace-fwrapper
	   excl::internal-invoke-debugger
	   EXCL::%INVOKES)))

#+allegro
(setq DEBUG::*HIDDEN-PACKAGE-INTERNALS*
  (remove :EXCL DEBUG::*HIDDEN-PACKAGE-INTERNALS*))

(defvar *dont-break-next-call* nil)
(defvar *currently-broken-fns* nil)

(defmacro f-break (&rest fns)
  `(break-functions ',fns))

#+allegro
(top-level:alias ("f-break" 2) (&rest fns) (break-functions fns))

(defmacro f-unbreak (&rest fns)
  `(unbreak-functions ',fns))

#+allegro
(top-level:alias ("f-unbreak" 2) (&rest fns) (unbreak-functions fns))

(defun break-functions (fns)
  (unless (null fns)
    (loop for fn in fns
	  do (break-fn fn)
	     (pushnew fn *currently-broken-fns*)))
  *currently-broken-fns*)

;;; redefines a refine utility
(defun break-fn (fn-name)
  (eval `(common-lisp:trace (,fn-name	;:condition (not *dont-break-next-call*)
			     :break-before
			     (if *dont-break-next-call*
				 (setq *dont-break-next-call* nil)
			       t)))))


(defun unbreak-functions (fns)
  (if (null fns)
      (setq fns *currently-broken-fns*))
  (loop for fn in fns
      do (eval `(untrace ,fn))
	 (setf *currently-broken-fns*
	   (remove fn *currently-broken-fns* :test #'equal))))


;;; Facility for breaking the function returned by a function
(defvar *currently-curried-broken-fns* nil)
(defvar *form*)
(defvar *curry-trace-depth* 1)

(defmacro c-break (&rest fns)
  `(break-curried-functions ',fns))

(defmacro c-unbreak (&rest fns)
  `(unbreak-curried-functions ',fns))

(defun break-curried-functions (fns)
  (unless (null fns)
    (loop for fn in fns
	  do (break-curried-fn fn)
	     (pushnew fn *currently-curried-broken-fns*)))
  *currently-curried-broken-fns*)

(defun unbreak-curried-functions (fns)
  (if (null fns)
      (setq fns *currently-curried-broken-fns*))
  (loop for fn in fns
      do (unadvise-1 fn :around 'c-break)
	 (setf *currently-curried-broken-fns*
	   (remove fn *currently-curried-broken-fns*))))

(defun break-curried-fn (fn)
  (advise-1 fn :around 'c-break nil
	    `((let ((curry-fn :do-it))
		#'(lambda (&rest args)
		    (setq cl:* (setq *form* `(apply ',curry-fn ',args)))
		    (let ((*print-level* *trace-print-level*)
			  (*print-length* *trace-print-length*)
			  (*curry-trace-depth* (+ 1 *curry-trace-depth*)))
		      (break "~a: ~a~a~a" (- *curry-trace-depth* 1) ',fn
			     #+allegro excl:arglist
			     #+(or mcl Lispworks) ()
			     args))
		    (let ((val (let ((*curry-trace-depth* (+ 1 *curry-trace-depth*)))
				 (apply curry-fn args))))
			;;(excl::trace-indent (or excl::trace-level 0))
			;;(format t ": Returned ~a" val)
		      val))))))

(defvar *currently-curried-traced-fns* nil)

(defmacro c-trace (&rest fns)
  `(trace-curried-functions ',fns))

(defmacro c-untrace (&rest fns)
  `(untrace-curried-functions ',fns))

(defun trace-curried-functions (fns)
  (unless (null fns)
    (loop for fn in fns
	  do (trace-curried-fn fn)
	     (pushnew fn *currently-curried-traced-fns*)))
  *currently-curried-traced-fns*)

(defun untrace-curried-functions (fns)
  (if (null fns)
      (setq fns *currently-curried-traced-fns*))
  (loop for fn in fns
      do (unadvise-1 fn :around 'c-trace)
	 (setf *currently-curried-traced-fns*
	   (remove fn *currently-curried-traced-fns*))))

(defun trace-curried-fn (fn)
  (advise-1 fn :around 'c-trace nil
	    `((let ((curry-fn :do-it))
		#'(lambda (&rest args)
		    (let ((*print-level* *trace-print-level*)
			  (*print-length* *trace-print-length*))
		      (format t "Call ~a: ~a~a~a~%" *curry-trace-depth* ',fn
			      #+allegro excl:arglist 
			      #+(or mcl Lispworks) ()
			      args))
		    (let ((val (let ((*curry-trace-depth* (+ 1 *curry-trace-depth*)))
				 (apply curry-fn args)))
			  (*print-level* *trace-print-level*)
			  (*print-length* *trace-print-length*))
		      (format *TRACE-OUTPUT* "Returned ~a: ~a~%" *curry-trace-depth* val)
		      val))))))

#||
(defun curry-add (x) #'(lambda (y) (+ x y)))
(defun test-curry (x y) (funcall (curry-add x) y))
||#


#+allegro
(defun be- (n)
;;;: sjw: 7/5/96 16:11  Allow for (car fm) to be (EXCL::ENCAPSULATED RESOLVED-SETFORMERS)
;;; as in Allegro CL 4.3
  (let* ((fm (quiet-do-command "dn" n))
	 (fm (if (eq (car fm) 'EXCL::TRACE-HOOK)
		 (cons (fourth fm) (fifth fm))
	       fm))
	 (fn (if (consp (car fm))
		 (second (car fm))
	       (car fm)))
	 (EXCL::*INHIBIT-TRACE* nil)
	 (*dont-break-next-call* (and (member fn *currently-broken-fns*)
				      (gethash (fdefinition fn)
					       excl::*fwrap-hash-table*))))
    (apply fn (cdr fm))))

#+allegro
(defun bev ()
  (if-break-move-to-caller)
  (be- 0))

#+allegro
(top-level:alias "bev" () (bev))

#+allegro
(defun br- (&optional (val nil))
  (if-break-move-to-caller)
  (top-level:do-command "return" `',val))

#+allegro
(defun bg! ()
  (if-break-move-to-caller)
  (let ((EXCL::*INHIBIT-TRACE* t))
    (top-level:do-command "restart")))

#+allegro
(defun be! ()
  (let* ((fm (if-break-move-to-caller))
	 (fn (if (consp (car fm))
		 (second (car fm))
	       (car fm)))
	 (EXCL::*INHIBIT-TRACE* t))
    (apply fn (cdr fm))))


#+allegro
(defun ppc()
  (let ((fm (quiet-do-command "curr")))
    (terpri t)
    (pprint fm)))
