(in-package :cl-user)
(defpackage :SpecCalc)
(defpackage :MSInterpreter)
(defpackage :JGen)
;; Toplevel Lisp aliases for Specware

(defparameter *sw-help-strings*
  '((":dir" . "List files in current directory")
    (#+allegro ":list" #-allegro ":list-units". "List loaded units")
    (":ls" . "List files in current directory")
    (":set-base" . "Set base library unit id")
    (":show" . "Show unit")
    (":show-base-unit-id" . "Show base library unit id")
    (":sw" . "Process unit")
    (":sw-help" . "Help for specware commands")
    (":sw-init" . "Clear Spec cache")
;;; Comment out undocumented commands
;;;    (":swc" . "Generate C code for unit")
    (":swe" . "Evaluate specware term")
    (":swe-spec" . "Set spec context for :swe command")
;;;    (":swj" . "Generate Java code for unit")
;;;    (":swj-config" . "Show configuration parameters for Java generation")
;;;    (":swj-config-dir" . "Set base directory to be used by :swj")
;;;    (":swj-config-make-public" . "Set public names to be used by :swj")
;;;    (":swj-config-pkg" . "Set package name to be used by :swj")
;;;    (":swj-config-reset" . "Restore default configuration parameters for Java generation")
    (":swl" . "Generate Lisp code for unit")
    (":swll" . "Generate Lisp code for local definition of unit, and compile and load")
    (":swpath" . "Query (no arg) or set SWPATH"))
  )

(defun sw-help (&optional command)
  (if command
      (let ((pr (assoc command *sw-help-strings* :test 'equal)))
	(when pr
	  (format t "~a~%" (cdr pr))))
    (loop for (com . helpstr) in *sw-help-strings*
      do (format t "~14a  ~a~%" com helpstr )))
  (values))

#+allegro
(top-level:alias ("sw-help" :string) (&optional com) (sw-help com))
    

(defun subst-home (dir)
  (if (and (stringp dir) (>= (length dir) 2) (equal (subseq dir 0 2) "~/"))
      (concatenate 'string (specware::getenv "HOME") (subseq dir 1))
    dir))

(defvar *last-unit-Id-_loaded* nil)

(defun sw0 (x)
  (Specware::runSpecwareUID (subst-home x))
  (values))
#+allegro(top-level:alias ("sw0" :case-sensitive) (x) (sw0 (string x)))

(defun set-base (x)
  (Specware::setBase_fromLisp (subst-home x))
  (values))
#+allegro
(top-level:alias ("set-base" :case-sensitive) (x) (set-base (string x)))

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
  (Specware::listLoadedUnits-0)
  (values))
(defun list-units ()
  (Specware::listLoadedUnits-0)
  (values))
#+allegro(top-level:alias ("list" :case-sensitive) () (list-loaded-units))

(defun sw (&optional x)
  (setq x (subst-home x))
  (if x
      (Specware::evaluateUID_fromLisp (setq *last-unit-Id-_loaded* x))
    (if *last-unit-Id-_loaded*
	(Specware::evaluateUID_fromLisp *last-unit-Id-_loaded*)
      (format t "No previous unit evaluated~%")))
  ;; (values) ; breaks bootstrap!  why suppress result?
  )

#+allegro
(top-level:alias ("sw" :case-sensitive :string) (&optional x)
  (sw x))

(defun show (&optional x)
  (setq x (subst-home x))
  (if x
      (Specware::evaluatePrint_fromLisp (setq *last-unit-Id-_loaded* (string x)))
    (if *last-unit-Id-_loaded*
	(Specware::evaluatePrint_fromLisp *last-unit-Id-_loaded*)
      (format t "No previous unit evaluated~%")))
  (values))
#+allegro
(top-level:alias ("show" :case-sensitive :string) (&optional x)
  (show x))

;; Not sure if an optional UnitId make sense for swl
(defun swl-internal (x &optional y)
  (Specware::evaluateLispCompile_fromLisp-2 (subst-home x)
					    (if y (cons :|Some| (subst-home y))
					      '(:|None|))))

;;; For non-allegro front-end to handle arguments separated by spaces
(defun toplevel-parse-args (arg-string)
  (let ((result ())
	pos)
    (loop while (setq pos (position #\  arg-string))
      do (let ((next-arg (subseq arg-string 0 pos)))
	   (when (not (equal next-arg ""))
	     (push next-arg result))
	   (setq arg-string (subseq arg-string (1+ pos)))))
    (nreverse (if (equal arg-string "")
		  result
		(cons arg-string result)))))


(defvar *last-swl-args* nil)

(defun swl (&optional args)
  (let ((r-args (if (not (null args))
		    (toplevel-parse-args args)
		  *last-swl-args*)))
    (if r-args
	(progn (setq *last-swl-args* r-args)
	       (swl-internal (string (first r-args))
			     (if (not (null (second r-args)))
				 (string (second r-args)) nil)))
      (format t "No previous unit evaluated~%"))))

#+allegro
(top-level:alias ("swl" :case-sensitive) (&optional &rest args)
  (let ((r-args (if (not (null args))
		    args
		  *last-swl-args*)))
    (if r-args
	(progn (setq *last-swl-args* args)
	       (funcall 'swl-internal (string (first r-args))
			(if (not (null (second r-args)))
			    (string (second r-args)) nil)))
      (format t "No previous unit evaluated~%"))))

(defun swll-internal (x &optional y)
  (let ((lisp-file-name (subst-home (or y (concatenate 'string
					    specware::temporaryDirectory
					    "cl-current-file")))))
    (if (Specware::evaluateLispCompileLocal_fromLisp-2
	 x (cons :|Some| lisp-file-name))
	(let (#+allegro *redefinition-warnings*)
	  (specware::compile-and-load-lisp-file lisp-file-name))
      "Specware Processing Failed!")))

(defun swll (&optional args)
  (let ((r-args (if (not (null args))
		    (toplevel-parse-args args)
		  *last-swl-args*)))
    (if r-args
	(progn (setq *last-swl-args* r-args)
	       (swll-internal (string (first r-args))
			      (if (not (null (second r-args)))
				  (string (second r-args)) nil)))
      (format t "No previous unit evaluated~%"))))

#+allegro
(top-level:alias ("swll" :case-sensitive) (&optional &rest args)
  (let ((r-args (if (not (null args))
		    args
		  *last-swl-args*)))
    (if r-args
	(progn (setq *last-swl-args* args)
	       (funcall 'swll-internal (string (first r-args))
			(if (not (null (second r-args)))
			    (string (second r-args)) nil)))
      (format t "No previous unit evaluated~%"))))


(defpackage "SWE") ; for access to results

(defvar *swe-use-interpreter?* t)   ; nil means used compiled lisp code
(defvar *current-swe-spec*     nil) ; nil means no import
(defvar *current-swe-spec-dir* nil)
(defvar swe::tmp)

(defun swe-spec (&optional x)
  (when (null x)
    (setq x (car *last-swl-args*)))
  (unless (eq (elt x 0) #\/)
    (format t "~&coercing ~A to /~A~%" x x)
    (setq x (format nil "/~A" x)))
  (setq x (subst-home x))
  (cond ((sw (string x))
	 (setq *current-swe-spec* x)
	 (setq *current-swe-spec-dir* (specware::current-directory))
	 (format t "~&Subsequent :swe commands will now import ~A.~%" x)
	 (unless *swe-use-interpreter?*
	   (format t "~&The following will produce, compile and load code for this spec:~%")
	   (format t "~&:swll ~A~%" x)))
	(t
	 (format t "~&:swe-spec had no effect.~%" x)
	 (if *current-swe-spec*
	     (format t "~&Subsequent :swe commands will still import ~A.~%" *current-swe-spec*)
	   (format t "~&Subsequent :swe commands will still import just the base spec.~%"))))
  (values))

#+allegro
(top-level:alias ("swe-spec" :case-sensitive :string) (x) 
  (swe-spec x))

(defvar *swe-print-as-slang?* nil)
(defvar *swe-return-value?* nil)

(defvar *tmp-counter* 0)

(defun ymd-hms ()
  (multiple-value-bind (second minute hour day month year)
      (DECODE-UNIVERSAL-TIME (get-universal-time))
    (format nil "~2,'0D~2,'0D~2,'0D_~2,'0D~2,'0D~2,'0D" 
	    (mod year 100) month day
	    hour minute second)))

;;; This seems to be the commonlisp ensure-directories-exist
;;;(defun ensure-directory (pathname)
;;;  (let* ((full-dir-list (pathname-directory pathname))
;;;	 (mode (car full-dir-list))
;;;	 (dir-list (list mode)))
;;;    (dolist (subdir (cdr full-dir-list))
;;;      (setq dir-list (append dir-list (list subdir)))
;;;      (let ((dir-name (make-pathname :directory dir-list)))
;;;	(ensure-directories-exist dir-name)))
;;;    (probe-file (make-pathname :directory full-dir-list))))

(defun swe (x)
  (let* ((tmp-dir (format nil "~Aswe/" specware::temporaryDirectory))
	 (tmp-name (format nil "swe_tmp_~D_~D"
			   (incf *tmp-counter*) 
			   (ymd-hms)))
	 (tmp-uid (format nil "/~A"     tmp-name))
	 (tmp-sw  (format nil "~A~A.sw" tmp-dir tmp-name))
	 (tmp-cl  (format nil "~A~A"    tmp-dir tmp-name))
	 (old-swpath (specware::getEnv "SWPATH"))
	 (new-swpath (format nil #-mswindows "~Aswe/:~A:~A" #+mswindows "~A/swe/;~A;~A"
			     Specware::temporaryDirectory *current-swe-spec-dir* old-swpath))
	 value)
    ;; clear any old values or function definitions:
    (makunbound  'swe::tmp)
    (fmakunbound 'swe::tmp)
    (ensure-directories-exist tmp-dir)
    (with-open-file (s tmp-sw :direction :output :if-exists :supersede)
      (format s "spec~%")
      (when *swe-use-interpreter?*
	(format s "  import ~A~%" "/Library/InterpreterBase"))
      (when (not (null *current-swe-spec*))
	(format s "  import ~A~%" *current-swe-spec*))
      (format s "  def swe.tmp = ~A~%endspec~%" x))
    ;; Process unit id:
    (if (unwind-protect
	    (progn
	      (specware::setenv "SWPATH" new-swpath)
	      (if *swe-use-interpreter?*
		  (setq value (Specware::evalDefInSpec-2 tmp-uid `(:|Qualified| . ("swe" . "tmp"))))
		(Specware::evaluateLispCompileLocal_fromLisp-2 tmp-uid (cons :|Some| tmp-cl))))
	  (specware::setenv "SWPATH" old-swpath))
	(if *swe-use-interpreter?*
	    (if (eq (car value) :|None|)
		(warn "No value for expression?")
	      (if *swe-return-value?* (cdr value)
		(MSInterpreter::printValue (cdr value))))
	  (let (#+allegro *redefinition-warnings*)
	    ;; Load resulting lisp code:
	    (load (make-pathname :type "lisp" :defaults tmp-cl))
	    (if *swe-return-value?* swe::tmp
	      ;; Print result:
	      (let ((*package* (find-package "SW-USER")))
		(cond ((boundp 'swe::tmp)
		       (if *swe-print-as-slang?*
			   (format t "~%Value is ~%~/specware::pprint-dt/~%"
				   swe::tmp)
			 (format t "~%Value is ~S~2%" swe::tmp)))
		      ((fboundp 'swe::tmp)
		       (let* ((code #+allegro (excl::func_code #'swe::tmp)
				    #-allegro (symbol-function 'swe::tmp))
			      (auxfn (find-aux-fn code)))
			 (format t "~%Function is ")
			 (pprint code)
			 (format t "~%")
			 (when (fboundp auxfn)
			   (format t "~%where ~A is " auxfn)
			   (let ((fn (symbol-function auxfn)))
			     (let ((code #+allegro (excl::func_code fn)
					 #+cmu     (eval:interpreted-function-lambda-expression fn)
					 #-(or allegro cmu) fn))
			       (if (consp code)
				   (pprint code)
				 (format t "the compiled function ~A" fn))))
			   (format t "~&~%"))))
		      (t
		       (warn "No value for expression?")))
		(values)))))
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


;;; --------------------------------------------------------------------------------
;;;
;;; Java Gen
;;;
;;; --------------------------------------------------------------------------------

(defun swj (x &optional y)
  (Specware::evaluateJavaGen_fromLisp-2 (subst-home x) 
					(if y 
					    (cons :|Some| y)
					  '(:|None|)))
  (values))

(defvar *last-swj-args* nil)

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

(defun swj-config-pkg (&optional pkg)
  #+(or allegro lispworks)
  (defparameter #+allegro excl::*redefinition-warnings*
    #+Lispworks lispworks::*redefinition-action*
    nil)
  (if (not (null pkg))
      (defparameter JGEN::packageName (string pkg))
    ())
  (format t "~A~%" JGEN::packageName))

(defun swj-config-dir (&optional dir)
  (setq dir (subst-home dir))
  #+(or allegro lispworks)
  (defparameter #+allegro excl::*redefinition-warnings*
    #+Lispworks lispworks::*redefinition-action*
    nil)
  (if (not (null dir))
      (defparameter JGEN::baseDir (string dir))
    ())
  (format t "~A~%" JGEN::baseDir))

(defun swj-config-make-public (&optional ops)
  #+(or allegro lispworks)
  (defparameter #+allegro excl::*redefinition-warnings*
    #+Lispworks lispworks::*redefinition-action*
    nil)
  (if (not (null ops))
      (defparameter JGEN::publicOps ops)
    ())
  (format t "~A~%" JGEN::publicOps))

(defun swj-config-reset ()
  #+(or allegro lispworks)
  (defparameter #+allegro excl::*redefinition-warnings*
    #+Lispworks lispworks::*redefinition-action*
    nil)
  (defparameter JGEN::packageName (string "specware.generated"))
  (defparameter JGEN::baseDir (string "."))
  (defparameter JGEN::publicOps nil))

#+allegro
(top-level:alias ("swj-config-pkg" :case-sensitive) (&optional pkg-name) (swj-config-pkg pkg-name))
#+allegro
(top-level:alias ("swj-config-dir" :case-sensitive :string) (&optional dir-name) (swj-config-dir dir-name))
#+allegro
(top-level:alias ("swj-config-make-public" :case-sensitive) (&optional &rest ops)
  (swj-config-make-public ops))
#+allegro
(top-level:alias ("swj-config-reset") () (swj-config-reset))

#+allegro
(top-level:alias
  ("swj-config") ()
  (let* ((pkgname (format nil "~A" JGEN::packageName))
	 (bdir (format nil "~A" JGEN::baseDir))
	 (ops (format nil "~A" JGEN::publicOps))
	 ;; (pops (if (string= ops "") ; is this test backwards?
	 ;; 	   (concatenate 'string "\"" ops "\"")
	 ;; 	   "none"))
	 )
    (progn
      (format t ";;; package name   [change with :swj-config-pkg]:         \"~A\"~%" pkgname)
      (format t ";;; base directory [change with :swj-config-dir]:         \"~A\"~%" bdir)
      (format t ";;; public ops     [change with :swj-config-make-public]: ~A~%" ops)
      (if (not (string= pkgname "default"))
	  (let* ((ppath (map 'string #'(lambda(c) (if (eq c #\.) #\/ c)) pkgname))
		 (dir (concatenate 'string bdir "/" ppath "/")))
	    (format t ";;; Java file(s) will be written into directory \"~A\"~%" dir))
	()))))

;;; --------------------------------------------------------------------------------

(defvar *last-swc-args* nil)

(defun swc-internal (x &optional y)
   (Specware::evaluateCGen_fromLisp-2 (subst-home x) (if y (cons :|Some| (subst-home y))
						       '(:|None|)))
   (values))

(defun swc (&optional args)
  (let ((r-args (if (not (null args))
		    (toplevel-parse-args args)
		  *last-swc-args*)))
    (if r-args
	(progn (setq *last-swc-args* r-args)
	       (swc-internal (string (first r-args))
			     (if (not (null (second r-args)))
				 (string (second r-args)) nil)))
      (format t "No previous unit evaluated~%"))))

#+allegro
(top-level:alias ("swc" :case-sensitive) (&optional &rest args)
  (let ((r-args (if (not (null args))
		    args
		  *last-swc-args*)))
    (if r-args
	(progn (setq *last-swc-args* args)
	       (funcall 'swc-internal (string (first r-args))
			(if (not (null (second r-args)))
			    (string (second r-args)) nil)))
      (format t "No previous unit evaluated~%"))))

(defun swpf-internal (x &optional y &key (obligations t))
  (Specware::evaluateProofGen_fromLisp-3 (subst-home (string x))
					 (if y (cons :|Some| (string (subst-home y)))
					   '(:|None|))
					 obligations))

(defvar *last-swpf-args* nil)

(defun swpf (&optional args)
  (let ((r-args (if (not (null args))
		    (toplevel-parse-args args)
		  *last-swpf-args*)))
    (if r-args
	(progn (setq *last-swpf-args* r-args)
	       (swpf-internal (string (first r-args))
			     (if (not (null (second r-args)))
				 (string (second r-args)) nil)))
      (format t "No previous unit evaluated~%"))))

(defun ucase (x)
  (if (keywordp x)
      (intern (read-from-string (string x)) 'keyword)
    (read-from-string (string x))))

#+allegro
(top-level:alias ("swpu" :case-sensitive) (&optional &rest args)
  (let ((r-args (if (not (null args))
		    (if (keywordp (cadr args))
			(cons (car args)
			      (cons nil (cdr args)))
		      args)
		  *last-swpf-args*)))
    (if r-args
	(progn (setq *last-swpf-args* args)
	       (apply 'swpf-internal
		      (cons (car r-args) (cons (cadr r-args)
			    (mapcar #'(lambda (x) (ucase x))
			      (cddr r-args))))))
      (format t "No previous unit evaluated~%"))))

;		      (string (first r-args))
;			(if (not (null (second r-args)))
;			    (string (second r-args)) nil)))
;      (format t "No previous unit evaluated~%"))))


;(defun swpfl-internal (x &optional y)
;  (let ((lisp-file-name (subst-home (or y (concatenate 'string
;					    specware::temporaryDirectory
;					    "cl-current-file")))))
;    (if (Specware::evaluateLispCompileLocal_fromLisp-2
;	 x (cons :|Some| lisp-file-name))
;	(let (#+allegro *redefinition-warnings*)
;	  (specware::compile-and-load-lisp-file lisp-file-name))
;      "Specware Processing Failed!")))

;(defun swpfl (&optional args)
;  (let ((r-args (if (not (null args))
;		    (toplevel-parse-args args)
;		  *last-swl-args*)))
;    (if r-args
;	(progn (setq *last-swl-args* r-args)
;	       (swpfl-internal (string (first r-args))
;			      (if (not (null (second r-args)))
;				  (string (second r-args)) nil)))
;      (format t "No previous unit evaluated~%"))))

;#+allegro
;(top-level:alias ("swpfl" :case-sensitive) (&optional &rest args)
;  (let ((r-args (if (not (null args))
;		    args
;		  *last-swl-args*)))
;    (if r-args
;	(progn (setq *last-swl-args* args)
;	       (funcall 'swpfl-internal (string (first r-args))
;			(if (not (null (second r-args)))
;			    (string (second r-args)) nil)))
;      (format t "No previous unit evaluated~%"))))

#+allegro
(top-level:alias ("wiz" :case-sensitive) (&optional (b nil b?))
  (if b? (princ (setq SpecCalc::specwareWizard? b))
    (princ SpecCalc::specwareWizard?)))

;; When the following boolean is true, then the System.debug function will
;; take the user into the Lisp debugger.
;; already declared in ~/Work/Generic/Specware4/Library/Base/Handwritten/Lisp/System.lisp :
;; (defvar System-spec::specwareDebug? nil)
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
  (setq str (subst-home (strip-extraneous str)))
  (if (or (null str) (equal str ""))
      (princ (specware::getenv "SWPATH"))
    (let ((str (string str)))
      (speccalc::checkSpecPathsExistence str)
      (princ (specware::setenv "SWPATH" (string str)))))
  (values))

#+allegro
(top-level:alias ("swpath" :case-sensitive :string) (&optional str)
  (setq str (subst-home str))
  (if (or (null str) (equal str ""))
      (princ (sys:getenv "SWPATH"))
    (let ((str (if (eq (aref str 0) #\")
		   (read-from-string str)
		 str)))
      (speccalc::checkSpecPathsExistence str)
      (princ (setf (sys:getenv "SWPATH") (string str))))))

(defun under-ilisp? ()
  (and (find-package "ILISP")
       (find-symbol "ILISP-COMPILE" "ILISP")))

#-allegro
(defun cd (&optional (dir ""))
  (if (equal dir "")
      (setq dir (specware::getenv "HOME"))
    (setq dir (subst-home dir)))
  #+cmu (unix:unix-chdir (if (equal dir "") (specware::getenv "HOME") dir))
  #-cmu (specware::change-directory dir)
  (let* ((dirpath (specware::current-directory))
	 (newdir (namestring dirpath)))
    #+cmu (setq common-lisp::*default-pathname-defaults* dirpath)
    (when (under-ilisp?)
      (emacs::eval-in-emacs (format nil "(setq default-directory ~s
                                               lisp-prev-l/c-dir/file (cons default-directory nil))"
				    (specware::ensure-final-slash newdir))))
    (princ newdir)
    (values)))

#-allegro
(defun ld (file)
  (load (subst-home file)))

#-allegro
(defun pwd ()
  (princ (namestring (specware::current-directory)))
  (values))

#-allegro
(defun exit ()
  (quit))

#-allegro
(defun cl (file)
  (specware::compile-and-load-lisp-file (subst-home file)))

#-allegro
(defun cf (file)
  (compile-file (subst-home file)))

#-allegro
(defun help (&optional command)
  (sw-help command))

(defun strip-extraneous (str)
  (let ((len (length str)))
    (if (> len 0)
	(if (member (elt str 0) '(#\" #\space))
	    (strip-extraneous (subseq str 1 len))
	  (if (member (elt str (- len 1)) '(#\" #\space))
	      (strip-extraneous (subseq str 0 (- len 1)))
	    str))
      str)))

#+(or sbcl cmu)
(defun cl::commandp (form)
  (keywordp form))

#+(or cmu mcl sbcl)
(defun cl::invoke-command-interactive (command)
  (let ((fn (intern (symbol-name command) (find-package "CL-USER")))
	(ch (read-char-no-hang)))
    ;; Warning: the READ used to get the command will typically eat
    ;; the terminating whitespace char.
    ;; In batch mode, this may be the newline char, so ch here
    ;; gets the first character on the following line.
    ;; (In interactive mode, ch will be NIL in such cases.)
    ;; To avoid this problem, scripts should put spaces after :pwd, etc.
    (when ch
      (unread-char ch))
    (if (or (null ch)          ; interactive, end of command
	    (eq ch #\Newline)) ; batch, first char after whitespace is newline      
	(if (fboundp fn)
	    (funcall fn)
	  (progn (warn "Unknown command ~s" command)
		 (values)))
      (if (fboundp fn)
	  (funcall fn (read-line))
	(progn (read-line)
	       (warn "Unknown command ~s" command)
	       (values))))))

#+mcl
(let ((ccl::*warn-if-redefine-kernel* nil))
  (defun ccl::check-toplevel-command (form)
    (let* ((cmd (if (consp form) (car form) form))
	   (args (if (consp form) (cdr form))))
      (if (keywordp cmd)
	  (dolist (g ccl::*active-toplevel-commands*
		     (let ((vals (multiple-value-list (cl::invoke-command-interactive cmd))))
		       (dolist (val vals)
			 (format t "~A~%" val))
		       t))
	    (when (let* ((pair (assoc cmd (cdr g))))
		    (if pair 
			(progn (apply (cadr pair) args)
			       t)))
	      (return t))))))
  )

#-allegro
(defun ls (&optional (str ""))
  #+cmu  (ext:run-program "ls" (if (equal str "") '("-FC") (list "-FC" str)) :output t)
  #+mcl  (ccl:run-program "ls" (if (equal str "") '("-FC") (list "-FC" str)) :output t)
  #+sbcl (sb-ext:run-program "/bin/ls" (if (equal str "") '("-FC") (list "-FC" str)) :output t)
  #-(or cmu mcl sbcl) (format t "Not yet implemented")
  (values))

#-allegro
(defun dir (&optional (str ""))
  (ls str))

#-allegro
(defun pa (&optional pkgname)
  (if (null pkgname)
      (princ (package-name *package*))
    (let ((pkg (find-package pkgname)))
      (if pkg
	  (setq *package* pkg)
	(princ "Not a package"))))
  (values))

#-allegro
(defun untr () (untrace))

#-allegro
(defun tr (&optional (nms-string ""))
  (eval `(trace ,@(map 'list #'read-from-string (toplevel-parse-args nms-string)))))

#+allegro
(top-level:alias ("ls" :string) (&optional (str ""))
  #+UNIX      (shell (format nil "ls ~A"  str))
  #+MSWINDOWS (shell (format nil "dir ~A" str))
  #-(OR UNIX MSWINDOWS) (format t "~&Neither the UNIX nor MSWINDOWS feature is present, so I don't know what to do!~%")
  )

#+allegro
(top-level:alias ("dir" :string) (&optional (str ""))
  #+UNIX      (shell (format nil "ls ~A"  str))
  #+MSWINDOWS (shell (format nil "dir ~A" str))
  #-(OR UNIX MSWINDOWS) (format t "~&Neither the UNIX nor MSWINDOWS feature is present, so I don't know what to do!~%")
  )

