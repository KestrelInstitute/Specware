(in-package :cl-user)
(defpackage :SpecCalc)

;; Toplevel Lisp aliases for Specware

(defvar *last-unit-Id-_loaded* nil)
(defvar *last-swl-args* nil)
(defvar *last-swj-args* nil)

(defun sw0 (x)
   (Specware::runSpecwareUID x)
   (values))
#+allegro(top-level:alias ("sw0" :case-sensitive) (x) (sw0 (string x)))

(defun set-base (x)
   (Specware::setBase_fromLisp x)
   (values))
#+allegro
(top-level:alias ("set-base" :case-sensitive) (x) (set-base x))

(defun show-base-unit-id ()
   (Specware::showBase_fromLisp-0)
   (values))
#+allegro
(top-level:alias ("show-base-unit-id" :case-sensitive) () (show-base-unit-id))

(defun sw-re-init ()
   (Specware::reinitializeSpecware-0)
   (values))
(defun sw-init ()
   (sw-re-init))
#+allegro(top-level:alias "sw-init" () (sw-re-init))

(defun list-loaded-units ()
   (Specware::listLoadedUnits-0))
#+allegro(top-level:alias ("list" :case-sensitive) () (list-loaded-units))

(defun sw (x)
   (Specware::evaluateUID_fromLisp x)
   ;; (values) ; breaks bootstrap!  why suppress result?
   )

#+allegro
(top-level:alias ("sw" :case-sensitive) (&optional x)
  (if x
    (sw (setq *last-unit-Id-_loaded* (string x)))
    (if *last-unit-Id-_loaded*
      (sw *last-unit-Id-_loaded*)
      (format t "No previous unit evaluated~%"))))

(defun show (x)
   (Specware::evaluatePrint_fromLisp x)
   (values))
#+allegro
(top-level:alias ("show" :case-sensitive) (&optional x)
  (if x
    (show (setq *last-unit-Id-_loaded* (string x)))
    (if *last-unit-Id-_loaded*
      (show *last-unit-Id-_loaded*)
      (format t "No previous unit evaluated~%"))))

;; Not sure if an optional UnitId make sense for swl
(defun swl (x &optional y)
   (Specware::evaluateLispCompile_fromLisp-2 x (if y (cons :|Some| y)
						 '(:|None|)))
   (values))
#+allegro
(top-level:alias ("swl" :case-sensitive) (&optional &rest args)
   (let ((r-args (if (not (null args))
		     args
		   *last-swl-args*)))
   (if r-args
       (progn (setq *last-swl-args* args)
	      (funcall 'swl (string (first r-args))
		       (if (not (null (second r-args)))
			   (string (second r-args)) nil)))
     (format t "No previous unit evaluated~%"))))

(defun swll (x &optional y)
   (let ((lisp-file-name (or y (concatenate 'string
				 specware::temporaryDirectory "cl-current-file"))))
     (if (Specware::evaluateLispCompileLocal_fromLisp-2
	    x (cons :|Some| lisp-file-name))
	 (let (*redefinition-warnings*)
	   (specware::compile-and-load-lisp-file lisp-file-name))
       "Specware Processing Failed!")))
#+allegro
(top-level:alias ("swll" :case-sensitive) (&optional &rest args)
   (let ((r-args (if (not (null args))
		     args
		   *last-swl-args*)))
   (if r-args
       (progn (setq *last-swl-args* args)
	      (funcall 'swll (string (first r-args))
		       (if (not (null (second r-args)))
			   (string (second r-args)) nil)))
     (format t "No previous unit evaluated~%"))))


(defpackage "SWE")

(defvar *current-swe-spec* nil ) ; "/Library/Base"

(defvar swe::tmp)

#+allegro
(top-level:alias ("in-spec" :case-sensitive :string) (x) 
  (setq *current-swe-spec* x)
  (format t "~&Subsequent :swe commands will now import ~A~%" x))

(defun swe (x)
  (let* ((tmp-uid "swe_tmp")
	 (tmp-sw  (format nil "~A.sw" tmp-uid))
	 (tmp-cl  (concatenate 'string specware::temporaryDirectory "swe_tmp")))
    ;; clear any old values or function definitions:
    (makunbound  'swe::tmp)
    (fmakunbound 'swe::tmp)
    (with-open-file (s tmp-sw :direction :output :if-exists :supersede)
      (if (null *current-swe-spec*)
	  (format s "spec~%  def swe.tmp = ~A~%endspec~%" x)
	(format s "spec~%  import ~A~%  def swe.tmp = ~A~%endspec~%" 
		*current-swe-spec*
		x)))
    ;; Process unit id:
    (if (Specware::evaluateLispCompileLocal_fromLisp-2 tmp-uid (cons :|Some| tmp-cl))
	(let (*redefinition-warnings*)
	  ;; Load resulting lisp code:
	  (load (make-pathname :type "lisp" :defaults tmp-cl))
	  ;; Print result:
	  (let ((*package* (find-package "SW-USER")))
	    (cond ((boundp 'swe::tmp)
		   (format t "~%Value is ~S~2%" swe::tmp))
		  ((fboundp 'swe::tmp)
		   (let* ((code (excl::func_code #'swe::tmp))
			  (auxfn (find-aux-fn code)))
		     (format t "~%Function is ")
		     (pprint code)
		     (format t "~%")
		     (when (fboundp auxfn)
		       (format t "~%where ~A is " auxfn)
		       (let ((fn (symbol-function auxfn)))
			 (let ((code (excl::func_code fn)))
			   (if (consp code)
			       (pprint code)
			     (format t "the compiled function ~A" fn))))
		       (format t "~&~%"))))
		  (t
		   (warn "No value for expression?")))))
      "Specware Processing Failed!")))
#+allegro
(top-level:alias ("swe" :case-sensitive :string) (x) (swe x))

(defun find-aux-fn (code)
  ;; step down through interpreted definitions to get past built-in stuff
  ;; down to the highest level user function
  ;; For example, if code is
  ;;   (LAMBDA (X1) (BLOCK SWE::TMP #'(LAMBDA (X2) #'(LAMBDA (X3) (SWE::TMP-1-1-1 X1 X2 X3)))))
  ;; this will find the symbol SWE::TMP-1-1-1
  (let ((fn (car code)))
    (cond ((equal fn 'function)
	   (find-aux-fn (cadr code)))
	  ((equal fn 'block)
	   (find-aux-fn (caddr code)))
	  ((equal fn 'lambda)
	   (find-aux-fn (caddr code)))
	  (t
	   fn))))

;; Not sure if an optional UnitId make sense for swj
(defun swj (x &optional y)
   (Specware::evaluateJavaGen_fromLisp-2 x (if y (cons :|Some| y)
					     '(:|None|)))
   (values))
#+allegro
(top-level:alias ("swj" :case-sensitive) (&optional &rest args)
   (let ((r-args (if (not (null args))
		     args
		   *last-swj-args*)))
   (if r-args
       (progn (setq *last-swj-args* args)
	      (funcall 'swj (string (first r-args))
		       (if (not (null (second r-args)))
			   (string (second r-args)) nil)))
     (format t "No previous unit evaluated~%"))))

;; Not sure whether ... no I'm not repeating this comment :)
(defun swc (x &optional y)
   (Specware::evaluateCGen_fromLisp-2 x (if y (cons :|Some| y)
					  '(:|None|))))
#+allegro
(top-level:alias ("swc" :case-sensitive) (&optional &rest args)
   (let ((r-args (if (not (null args))
		     args
		   *last-swc-args*)))
   (if r-args
       (progn (setq *last-swc-args* args)
	      (funcall 'swc (string (first r-args))
		       (if (not (null (second r-args)))
			   (string (second r-args)) nil)))
     (format t "No previous unit evaluated~%"))))

#+allegro
(top-level:alias ("wiz" :case-sensitive) (&optional (b nil b?))
   (if b? (princ (setq SpecCalc::specwareWizard? b))
          (princ SpecCalc::specwareWizard?)))

;; When the following boolean is true, then the System.debug function will
;; take the user into the Lisp debugger.
(defvar System-spec::specwareDebug? nil)
(defun swdbg (&optional (b nil b?))
  (if b? (princ (setq System-spec::specwareDebug?
		      (and b (not (equal b "nil")))))
    (princ System-spec::specwareDebug?))
  (values))

#+allegro
(top-level:alias ("swdbg" :case-sensitive) (&optional (b nil b?))
   (if b? (princ (setq System-spec::specwareDebug? b))
          (princ System-spec::specwareDebug?)))

(defun swpath  (&optional str)
  (if (or (null str) (equal str ""))
      (princ (specware::getenv "SWPATH"))
    (let ((str (string str)))
      (speccalc::checkSpecPathsExistence str)
      (princ (specware::setenv "SWPATH" (string str)))))
  (values))

#+allegro
(top-level:alias ("swpath" :case-sensitive :string) (&optional str)
  (if (or (null str) (equal str ""))
      (princ (sys:getenv "SWPATH"))
    (let ((str (string str)))
      (speccalc::checkSpecPathsExistence str)
      (princ (setf (sys:getenv "SWPATH") (string str))))))

#+(or cmu openmcl)
(defun cd (&optional dir)
  (specware::change-directory (or dir (specware::getenv "HOME"))))

#+(or cmu openmcl)
(defun exit ()
  (quit))

(defun strip-extraneous (str)
  (let ((len (length str)))
    (if (> len 0)
	(if (member (elt str 0) '(#\" #\space))
	    (strip-extraneous (subseq str 1 len))
	  (if (member (elt str (- len 1)) '(#\" #\space))
	      (strip-extraneous (subseq str 0 (- len 1)))
	    str))
      str)))

#+cmu
(defun cl::commandp (form)
  (keywordp form))

#+(or cmu mcl)
(defun cl::invoke-command-interactive (command)
  (let ((fn (intern (symbol-name command)))
	(ch (read-char-no-hang)))
    (if ch
	(progn (unread-char ch)
	       (if (fboundp fn)
		   (funcall fn (strip-extraneous (read-line)))
		 (progn (read-line)
			(warn "Unknown command ~s" command))))
      (if (fboundp fn)
	  (funcall fn)
	(warn "Unknown command ~s" command)))))

#+mcl
(let ((ccl::*warn-if-redefine-kernel* nil))
(defun ccl::check-toplevel-command (form)
  (let* ((cmd (if (consp form) (car form) form))
         (args (if (consp form) (cdr form))))
    (if (keywordp cmd)
      (dolist (g ccl::*active-toplevel-commands*
		 (cl::invoke-command-interactive cmd))
	(when
	    (let* ((pair (assoc cmd (cdr g))))
	      (if pair 
		(progn (apply (cadr pair) args)
		       t)))
	  (return t))))))
)

