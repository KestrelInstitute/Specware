(in-package :cl-user)
(defpackage :SpecCalc)
(defpackage :MSInterpreter)
(defpackage :JGen)
(defpackage :IO-SPEC)
(defpackage :SYSTEM-SPEC)
(defpackage :EMACS)
(defpackage :SWShell)
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
    (":swc" . "Generate C code for unit") 
    (":swe" . "Evaluate specware term")
    (":swe-spec" . "Set spec context for :swe command")
    (":swj" . "Generate Java code for unit")
    (":swj-config" . "Show configuration parameters for Java generation")
    (":swj-config-dir" . "Set base directory to be used by :swj")
    (":swj-config-make-public" . "Set public names to be used by :swj")
    (":swj-config-pkg" . "Set package name to be used by :swj")
    (":swj-config-reset" . "Restore default configuration parameters for Java generation")
    (":swl" . "Generate Lisp code for unit")
    (":swll" . "Generate Lisp code for local definition of unit, and compile and load")
    (":swpath" . "Query (no arg) or set SWPATH"))
  )

(defun sw-help (&optional command)
  (if command
      (let ((pr (assoc command *sw-help-strings* :test 'equal)))
	(if pr (print-command-doc (car pr) (cdr pr))
	  (format t "No documentation for command.")))
    (loop for (com . helpstr) in *sw-help-strings*
      do (print-command-doc com helpstr)))
  (values))

(defun print-command-doc (com helpstr)
  (when (eq (elt helpstr 0) #\[)
    (let ((close (position #\] helpstr :from-end t)))
      (when close
	(setq com (concatenate 'string com " " (subseq helpstr 0 (1+ close))))
	(setq helpstr (subseq helpstr (+ 2 close))))))
  (if (> (length com) 17)
      (format t "~a~%~18T~a~%" com helpstr)
    (format t "~17a ~a~%" com helpstr)))

#+allegro
(top-level:alias ("sw-help" :string) (&optional com) (sw-help com))
    
;;; Normalization utilities
(defun subst-home (path)
  (when (stringp path)
    (when (and (>= (length path) 2) (equal (subseq path 0 2) "~/"))
      (setq path (concatenate 'string (specware::getenv "HOME") (subseq path 1))))
    (setq path (string-subst path " ~/" (concatenate 'string " " (specware::getenv "HOME") "/"))))
    path)

(defun strip-extraneous (str)
  (let ((len (length str)))
    (if (> len 0)
	(if (member (elt str 0) '(#\" #\space))
	    (strip-extraneous (subseq str 1 len))
	  (if (member (elt str (- len 1)) '(#\" #\space))
	      (strip-extraneous (subseq str 0 (- len 1)))
	    str))
      str)))

;;; Code for handling specalc terms as well as just unitid strings
(defun unitIdString? (str)
  (loop for i from 0 to (- (length str) 1)
        always (let ((ch (elt str i)))
		 (or (alphanumericp ch)
		     (member ch '(#\/ #\: #\# #\_ #\- #\~))))))

(defvar *saved-swpath* nil)
(defvar *temp-file-in-use?* nil)
(defvar *current-temp-file* nil)
(defvar *tmp-counter* 0)
(defvar SpecCalc::noElaboratingMessageFiles)
(defvar SpecCalc::aliasPaths)
(defun sw-temp-file? (fil)
  (equal fil *current-temp-file*))

(defun norm-unitid-str (str)
  (setq *current-temp-file* nil)
  (setq SpecCalc::aliasPaths nil)
  (if (null str) str
    (progn (setq str (strip-extraneous str))
	   (setq str (subst-home str))
	   (let ((len (length str)))
	     (when (and (> len 3)
			(string= (subseq str (- len 3)) ".sw"))
	       (setq str (subseq str 0 (- len 3)))))
	   (setq *temp-file-in-use?* nil)
	   (unless (unitIdString? str)
	     ;; spec calc term. Need to put it in a temporary file
	     (let* ((tmp-dir (format nil "~Asw/" specware::temporaryDirectory))
		    (tmp-name (format nil "sw_tmp_~D_~D"
				      (incf *tmp-counter*) 
				      (ymd-hms)))
		    (tmp-uid (format nil "/~A"     tmp-name))
		    (tmp-full-uid (format nil "~A~A"  tmp-dir tmp-name))
		    (tmp-sw  (format nil "~A~A.sw" tmp-dir tmp-name))
		    (old-swpath (or *saved-swpath* (specware::getEnv "SWPATH")))
		    (new-swpath (format nil #-mswindows "~Asw/:~A" #+mswindows "~A/sw/;~A"
					Specware::temporaryDirectory old-swpath)))
	       (ensure-directories-exist tmp-dir)
	       (with-open-file (s tmp-sw :direction :output :if-exists :supersede)
		 (format s "~A" str))
	       (setq *saved-swpath* old-swpath)
	       (specware::setenv "SWPATH" new-swpath)
	       (setq *temp-file-in-use?* t)
	       (setq *current-temp-file* tmp-sw)
	       (setq SpecCalc::aliasPaths (list (cons (cdr (pathname-directory (parse-namestring tmp-dir)))
						      (cdr (pathname-directory (specware::current-directory))))))
	       (setq SpecCalc::noElaboratingMessageFiles (cons tmp-full-uid nil))
	       (setq str tmp-uid)))
	   str)))

(defvar *running-test-harness?* nil)
(defvar SWShell::*in-specware-shell?*)
(defvar swshell::*emacs-eval-form-after-prompt*)

(defun show-error-position (emacs-error-info position-delta)
  (when emacs-error-info
    (let ((error-file (first emacs-error-info))
	  (linepos (second emacs-error-info))
	  (charpos (third emacs-error-info)))
      (unless *running-test-harness?*
	(if (sw-temp-file? error-file)
	    (let ((emacs-command (format nil "(show-error-on-new-input ~a)" (+ charpos position-delta))))
	      (if SWShell::*in-specware-shell?*
		  (setq swshell::*emacs-eval-form-after-prompt* emacs-command)
		(emacs::eval-in-emacs emacs-command)))
	  (emacs::eval-in-emacs (format nil "(goto-file-position ~s ~a ~a)"
					error-file linepos charpos)))))))

(defvar *last-unit-Id-_loaded* nil)

(defun sw0 (x)
  (Specware::runSpecwareUID (norm-unitid-str x))
  (values))

#+allegro(top-level:alias ("sw0" :case-sensitive) (x) (sw0 (string x)))

(defun set-base (x)
  (Specware::setBase_fromLisp (norm-unitid-str x))
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
  (setq x (norm-unitid-str x))
  (flet ((sw-int (x)
	   (let ((val (if x
			  (Specware::evaluateUID_fromLisp (setq *last-unit-Id-_loaded* x))
			(if *last-unit-Id-_loaded*
			    (Specware::evaluateUID_fromLisp *last-unit-Id-_loaded*)
			  (format t "No previous unit evaluated~%")))))
	     (show-error-position emacs::*goto-file-position-stored* 1)
	     val)))
    (if *running-test-harness?*
	(sw-int x)
      (let ((emacs::*goto-file-position-store?* t)
	    (emacs::*goto-file-position-stored* nil))
	(sw-int x)))))

#+allegro
(top-level:alias ("sw" :case-sensitive :string) (&optional x)
  (sw x))

(defun show (&optional x)
  (setq x (norm-unitid-str x))
  (flet ((show-int (x)
	   (if x
	       (Specware::evaluatePrint_fromLisp (setq *last-unit-Id-_loaded* (string x)))
	     (if *last-unit-Id-_loaded*
		 (Specware::evaluatePrint_fromLisp *last-unit-Id-_loaded*)
	       (format t "No previous unit evaluated~%")))
	   (show-error-position emacs::*goto-file-position-stored* 1)
	   (values)))
    (if *running-test-harness?*
	(show-int x)
      (let ((emacs::*goto-file-position-store?* t)
	    (emacs::*goto-file-position-stored* nil))
	(show-int x)))))

#+allegro
(top-level:alias ("show" :case-sensitive :string) (&optional x)
  (show x))

(defun showx (&optional x)
  (setq x (norm-unitid-str x))
  (flet ((show-int (x)
	   (let ((SpecCalc::printSpecExpanded? t))
	     (if x
		 (Specware::evaluatePrint_fromLisp (setq *last-unit-Id-_loaded* (string x)))
	       (if *last-unit-Id-_loaded*
		   (Specware::evaluatePrint_fromLisp *last-unit-Id-_loaded*)
		 (format t "No previous unit evaluated~%"))))
	   (show-error-position emacs::*goto-file-position-stored* 1)
	   (values)))
    (if *running-test-harness?*
	(show-int x)
      (let ((emacs::*goto-file-position-store?* t)
	    (emacs::*goto-file-position-stored* nil))
	(show-int x)))))

#+allegro
(top-level:alias ("showx" :case-sensitive :string) (&optional x)
  (showx x))

;; Not sure if an optional UnitId make sense for swl
(defun swl-internal (x &optional y)
  ;; scripts depend upon this returning true iff successful
  (setq x (norm-unitid-str x))
  (flet ((swl1 (x y)
	   (let ((val (Specware::evaluateLispCompile_fromLisp-2 x
								(if y (cons :|Some| (subst-home y))
								  '(:|None|)))))
	     (show-error-position emacs::*goto-file-position-stored* 1)
	     val)))
    (if *running-test-harness?*
	(swl1 x y)
      (let ((emacs::*goto-file-position-store?* t)
	    (emacs::*goto-file-position-stored* nil))
	(swl1 x y)))))

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

;;; This is heuristic. It could be made more accurate by improving filestring? to check for chars that
;;; can't appear in file names but might appear in the final token of a spec term
(defun extract-final-file-name (arg-string)
  (let ((pos (position #\  arg-string :from-end t)))
    (if (null pos)
	(list arg-string nil)
      (let ((lastitem (subseq arg-string (1+ pos))))
	(if (filestring? lastitem)
	    (list (subseq arg-string 0 pos) lastitem)
	  (list arg-string nil))))))

(defun filestring? (str)
  (or (find #\/ str)
      (not (or (member str '("end-spec" "endspec") :test 'string=)
	       (find #\} str)))))

(defvar *last-swl-args* nil)

(defun swl (&optional args)
  ;; scripts depend upon this returning true iff successful
  (let ((r-args (if (not (null args))
		    (extract-final-file-name args)
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
  ;; scripts depend upon this returning true iff successful
  (let ((lisp-file-name (subst-home (or y (concatenate 'string
					    specware::temporaryDirectory
					    "cl-current-file"))))
	(x (norm-unitid-str x)))
    (flet ((swll1 (x lisp-file-name)
	     (let ((val (if (Specware::evaluateLispCompileLocal_fromLisp-2
			     x (cons :|Some| lisp-file-name))
			    (let (#+allegro *redefinition-warnings*)
			      ;; scripts depend upon the following returning true iff successful
			      (specware::compile-and-load-lisp-file lisp-file-name))
			  "Specware Processing Failed!")))
	       (show-error-position emacs::*goto-file-position-stored* 1)
	       val)))
      (if *running-test-harness?*
	  (swll1 x lisp-file-name)
	(let ((emacs::*goto-file-position-store?* t)
	      (emacs::*goto-file-position-stored* nil))
	  (swll1 x lisp-file-name))))))

(defun swll (&optional args)
  ;; scripts depend upon this returning true iff successful
  (let ((r-args (if (not (null args))
		    (extract-final-file-name args)
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
    (setq x (and (consp *last-swl-args*) (car *last-swl-args*))))
  (if (null x) (format t "~&No previous spec")
    (progn
      (setq x (norm-unitid-str x))
      (unless (eq (elt x 0) #\/)
	(format t "~&coercing ~A to /~A~%" x x)
	(setq x (format nil "/~A" x)))
      (setq x (norm-unitid-str x))
      (cond ((sw (string x))
	     (setq *current-swe-spec* x)
	     (setq *current-swe-spec-dir* (specware::current-directory))
	     (format t "~&Subsequent evaluation commands will now import ~A.~%" x)
	     (unless *swe-use-interpreter?*
	       (format t "~&The following will produce, compile and load code for this spec:~%")
	       (format t "~&:swll ~A~%" x)))
	    (t
	     (format t "~&:swe-spec had no effect.~%" x)
	     (if *current-swe-spec*
		 (format t "~&Subsequent :swe commands will still import ~A.~%" *current-swe-spec*)
	       (format t "~&Subsequent :swe commands will still import just the base spec.~%"))))))
  (values))

#+allegro
(top-level:alias ("swe-spec" :case-sensitive :string) (x) 
  (swe-spec x))

(defvar *swe-print-as-slang?* nil)
(defvar *swe-return-value?* nil)
(defvar *expr-begin-offset* 2)		; Difference between beginning of expr in input and in file

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
	 (*current-temp-file* tmp-sw)
	 (tmp-cl  (format nil "~A~A"    tmp-dir tmp-name))
	 (SpecCalc::noElaboratingMessageFiles (list tmp-cl))
	 (old-swpath (specware::getEnv "SWPATH"))
	 (new-swpath (format nil #-mswindows "~Aswe/:~A:~A" #+mswindows "~A/swe/;~A;~A"
			     Specware::temporaryDirectory *current-swe-spec-dir* old-swpath))
	 (emacs::*goto-file-position-store?* t)
	 (emacs::*goto-file-position-stored* nil)
	 (parser-type-check-output)
	 (input-line-num 2)
	 parsed-ok?
	 value)
    (declare (special SpecCalc::printElaborateSpecMessage?))
    ;; clear any old values or function definitions:
    (makunbound  'swe::tmp)
    (fmakunbound 'swe::tmp)
    (ensure-directories-exist tmp-dir)
    (with-open-file (s tmp-sw :direction :output :if-exists :supersede)
      (format s "spec~%")
      (when *swe-use-interpreter?*
	(format s "  import ~A~%" "/Library/InterpreterBase")
	(incf input-line-num))
      (when (not (null *current-swe-spec*))
	(format s "  import ~A~%" *current-swe-spec*)
	(incf input-line-num))
      (format s "  def swe.tmp = ~A~%endspec~%" x))
    ;; Process unit id:
    (unwind-protect
	    (progn
	      (specware::setenv "SWPATH" new-swpath)
	      (setq parser-type-check-output
		(with-output-to-string (*standard-output*)
		  (let ((*error-output* *standard-output*)
			(SpecCalc::numberOfTypeErrorsToPrint 2))
		    (setq parsed-ok? (Specware::evaluateUID_fromLisp tmp-uid)))))
	      (when parsed-ok?
		(if *swe-use-interpreter?*
		    (setq value (Specware::evalDefInSpec-2 tmp-uid `(:|Qualified| . ("swe" . "tmp"))))
		  (Specware::evaluateLispCompileLocal_fromLisp-2 tmp-uid (cons :|Some| tmp-cl)))))
	  (specware::setenv "SWPATH" old-swpath))
    (if emacs::*goto-file-position-stored* ; Parse or type-check error
	(progn (princ (trim-error-output parser-type-check-output))
	       (show-error-position emacs::*goto-file-position-stored* -15))
      (progn
	(princ parser-type-check-output)
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
		(values)))))))))

#+allegro
(top-level:alias ("swe" :case-sensitive :string) (x) (swe x))

;;; Remove file error comment. Could also massage line numbers.
(defun trim-error-output (errstr)
  (setq errstr (fix-position-references errstr "3."))
  (let ((first-linefeed (position #\linefeed errstr))
	(syntax-err-pos (search "Syntax error" errstr))
	pos)
    (setq errstr
	  (if (and first-linefeed (string= (subseq errstr 0 10)  "Errors in "))
	      (subseq errstr (+ first-linefeed 1))
	    (if syntax-err-pos
		(subseq errstr 0 syntax-err-pos)
	      errstr)))
    (when (setq pos (search " At line" errstr))
      (setq errstr (concatenate 'string (subseq errstr 0 pos) (subseq errstr (+ pos 16)))))
    (when (setq pos (search "op tmp" errstr))
      (setq errstr (concatenate 'string (subseq errstr 0 pos) "top-level expression"
				(subseq errstr (+ pos 6)))))
    errstr))

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

(defun fix-position-references (str prefix)
  (let ((pos 0))
    (loop while (setq pos (search prefix str :start2 pos))
      do (let ((endprefixpos (+ pos (length prefix)))
	       endnumpos)
	   (loop for i from endprefixpos
	     while (digit-char-p (elt str i))
	     do (setq endnumpos i))
	   (when endnumpos
	     (let ((rawlinepos (read-from-string str nil nil :start endprefixpos :end (1+ endnumpos))))
	       (when (fixnump rawlinepos)
		 (setq str (concatenate 'string
					(subseq str 0 pos)
					(format nil "~a" (+ rawlinepos *expr-begin-offset*))
					(subseq str (1+ endnumpos)))))))
	   (incf pos)		; ensure progress
	   ))
    str))

(defun string-subst (str source target)
  (let (pos)
    (loop while (setq pos (search source str))
	  do (setq str (concatenate 'string
			 (subseq str 0 pos)
			 target
			 (subseq str (+ pos (length source))))))
    str))


;;; --------------------------------------------------------------------------------
;;;
;;; Java Gen
;;;
;;; --------------------------------------------------------------------------------

(defun swj (x &optional y)
  (let ((emacs::*goto-file-position-store?* t)
	(emacs::*goto-file-position-stored* nil))
    (Specware::evaluateJavaGen_fromLisp-2 (norm-unitid-str x) 
					  (if y 
					      (cons :|Some| y)
					    '(:|None|)))
    (show-error-position emacs::*goto-file-position-stored* 1)
    (values)))

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

(defun swj-config ()
  (let* ((pkgname (format nil "~A" JGEN::packageName))
	 (bdir (format nil "~A" JGEN::baseDir))
	 (ops (format nil "~A" JGEN::publicOps))
	 ;; (pops (if (string= ops "") ; is this test backwards?
	 ;; 	   (concatenate 'string "\"" ops "\"")
	 ;; 	   "none"))
	 )
    (progn
      (format t ";;; package name   [change with swj-config-pkg]:         \"~A\"~%" pkgname)
      (format t ";;; base directory [change with swj-config-dir]:         \"~A\"~%" bdir)
      (format t ";;; public ops     [change with swj-config-make-public]: ~A~%" ops)
      (if (not (string= pkgname "default"))
	  (let* ((ppath (map 'string #'(lambda(c) (if (eq c #\.) #\/ c)) pkgname))
		 (dir (concatenate 'string bdir "/" ppath "/")))
	    (format t ";;; Java file(s) will be written into directory \"~A\"~%" dir))
	()))))

#+allegro
(top-level:alias
  ("swj-config") () (swj-config))

;;; --------------------------------------------------------------------------------

(defvar *last-swc-args* nil)

(defun swc-internal (x &optional y)
;;  (format t "swc-internal: x=~A, y=~A~%" x y)
   (let ((emacs::*goto-file-position-store?* t)
	 (emacs::*goto-file-position-stored* nil))
     (Specware::evaluateCGen_fromLisp-2 (norm-unitid-str x)
					(if y (cons :|Some| (subst-home y))
					  '(:|None|)))
     (show-error-position emacs::*goto-file-position-stored* 1)
     (values)))

(defun swc (&optional args)
  (let ((r-args (if (not (null args))
		    (extract-final-file-name args)
		  *last-swc-args*)))
    (if r-args
	(progn
	  (setq *last-swc-args* r-args)
	  (let* (
		 (unitid (string (first r-args)))
		 (arg2 (if (null (second r-args)) nil (string (second r-args))))
		 (cfilename (if arg2 arg2 (if (unitIdString? unitid)
					      (getCFileNameFromUnitid unitid)
					    "temp")))
		 )
	    (progn
	      (funcall 'swc-internal unitid cfilename)
	      )
	    ))
      (format t "No previous unit evaluated~%"))))

#+allegro
(top-level:alias ("swc" :case-sensitive :string) (&optional args)
  (swc args))
;;  (let ((r-args (if (not (null args))
;;		    args
;;		  *last-swc-args*)))
;;    (if r-args
;;	(progn (setq *last-swc-args* args)
;;	       (funcall 'swc-internal (string (first r-args))
;;			(if (not (null (second r-args)))
;;			    (string (second r-args)) nil)))
;;     (format t "No previous unit evaluated~%"))))

(defvar *last-make-args* nil)
(defvar *make-verbose* t)

(defun make (&rest args)
  (let* ((make-args (if (not (null args)) 
			(cons (norm-unitid-str (first args)) (rest args))
		      *last-make-args*))
	 (make-command (if (specware::getenv "SPECWARE4_MAKE") (specware::getenv "SPECWARE4_MAKE") "make"))
	 (user-make-file-suffix ".mk")
	 (sw-make-file "$(SPECWARE4)/Languages/MetaSlang/CodeGen/C/Clib/Makerules")
	 (make-file "swcmake.mk"))
    (setq *last-make-args* make-args)
    (if  make-args
	(let* ((unitid (first make-args))
	       (cbase (getCFileNameFromUnitid unitid))
	       (user-make-file (concatenate 'string cbase user-make-file-suffix))
	       (hw-src-1 (concatenate 'string cbase "_main.c"))
	       (hw-src-2 (concatenate 'string cbase "_test.c"))
	       (hw-src (if (IO-SPEC::fileExistsAndReadable hw-src-1) hw-src-1
			 (if (IO-SPEC::fileExistsAndReadable hw-src-2) hw-src-2 nil)))
	       )
	  (when *make-verbose* 
	    (progn
	      (format t ";; using make command:                     ~S~%" make-command)
	      (format t ";; looking for user-defined make rules in: ~S~%" user-make-file)
	      (format t ";; using system make rules in:             ~S~%" sw-make-file)
	      (format t ";; generating local make rules in:         ~S~%" make-file)
	      (when hw-src
		(format t ";; linking with handwritten source:        ~S~%" hw-src))
	      (format t ";; invoking :swc ~A ~A~%" unitid cbase))
	    )
	  (funcall 'swc-internal (string unitid) (string cbase))
	  (when *make-verbose* (format t ";; generating makefile ~S~%" make-file))
	  (with-open-file (mf make-file :direction :output :if-exists :new-version)
	    (progn
	      (format mf "# ----------------------------------------------~%")
	      (format mf "# THIS MAKEFILE IS GENERATED, PLEASE DO NOT EDIT~%")
	      (format mf "# ----------------------------------------------~%")
	      (format mf "~%~%")
	      (format mf "# the toplevel target extracted from the :make command line:~%")
	      (format mf "all : ~A~%" cbase)
	      (format mf "~%")
	      (format mf "# include the predefined make rules and variable:~%")
	      (format mf "include ~A~%" sw-make-file)
	      (when (IO-SPEC::fileExistsAndReadable user-make-file)
		(progn
		  (format mf "~%")
		  (format mf "# include the existing user make file:~%")
		  (format mf "include ~A~%" user-make-file))
		)
	      (when hw-src
		(format mf "~%")
		(format mf "# handwritten source code; derived from unit-id by appending either \"_main.c\" or \"_test.c\":~%")
		(format mf "HWSRC = ~A~%" hw-src)
		)
	      (format mf "~%")
	      (format mf "# dependencies and rule for main target:~%")
	      (format mf "~A: ~A.o $(HWSRC) $(USERFILES) $(GCLIB)~%" cbase cbase)
	      (format mf "	$(CC) -o ~A $(LDFLAGS) $(CPPFLAGS) $(CFLAGS) ~A.o $(HWSRC) $(USERFILES) $(LOADLIBES) $(LDLIBS)~%"
		      cbase cbase)
	      ))
	  (when *make-verbose* 
	    (format t ";; invoking make command:  ~A -f ~A~%" make-command make-file))
	  (run-cmd make-command "-f" (format nil "~A" make-file)))
      ;; else: no make-args
      (progn
	(format t "No previous unit evaluated")
	(if (IO-SPEC::fileExistsAndReadable make-file)
	    (progn
	      (format t "; using existing make-file ~s...~%" make-file)
	      (run-cmd make-command "-f" (format nil "~A" make-command make-file))
	      )
	  (format t " and no previous make-file found; please supply a unit-id as argument.~%")
	  )))))
 

#+allegro
(top-level:alias ("make" :case-sensitive :string) (&optional args)
  (make args))

;; returns the name of the cfile from the given unitid
;; by substituting #' with underscores
(defun getCFileNameFromUnitid (unitId)
  (cl:substitute #\_  #\# (string unitid))
  )

#-(or allegro cmu mcl sbcl) 
(defun run-cmd (cmd &rest args)
  (warn "ignoring non-[ALLEGRO/CMU/MCL/SBCL] RUN-CMD : ~A~{ ~A~}" cmd args))


#+(or cmu mcl sbcl) 
(defun run-cmd (cmd &rest args)
  (let ((process
	 ;; cmu defaults for keywords args to run-program:
	 ;;   (env *environment-list*)
	 ;;   (wait t) 
	 ;;   pty 
	 ;;   input            if-input-does-not-exist 
	 ;;   output           (if-output-exists :error) 
	 ;;   (error :output)  (if-error-exists :error) 
	 ;;   status-hook
	 #+cmu  (ext:run-program    cmd args :output *standard-output* :error :output :wait t)
	 #+mcl  (ccl:run-program    cmd args :output *standard-output* :error :output :wait t)
	 #+sbcl (sb-ext:run-program cmd args :output *standard-output* :error :output :wait t)))
    (let ((rc (process-exit-code process)))
      (unless (equal rc 0)
	(warn "Return code from run-shell-command was non-zero: ~S" rc))))
  (values))

#+allegro
(defun run-cmd (cmd &rest args)
  (let ((cmd (format nil "~A~{ ~A~}" cmd args)))
    (let ((rc
	   #+UNIX      (run-shell-command cmd 
					  :output       *standard-output* 
					  :error-output :output 
					  :wait t) 
	   #+MSWINDOWS (run-shell-command cmd 
					  ;; :output       *standard-output* ; mysterious problems under windows
					  ;; :error-output :output           ; mysterious problems under windows
					  :wait t)
	   #-(OR UNIX MSWINDOWS) (progn (warn "ignoring non-[UNIX/MSWINDOWS] ALLEGRO RUN-CMD : ~A" cmd) 1)))
      (unless (equal rc 0)
	(warn "Return code from run-shell-command was non-zero: ~S" rc))))
  (values))
  
;; --------------------------------------------------------------------------------

(defun swpf-internal (x &optional y &key (obligations t))
  (let ((emacs::*goto-file-position-store?* t)
	(emacs::*goto-file-position-stored* nil))
    (let ((val (Specware::evaluateProofGen_fromLisp-3 (norm-unitid-str (string x))
						      (if y (cons :|Some| (string (subst-home y)))
							'(:|None|))
						      obligations)))
      (show-error-position emacs::*goto-file-position-stored* 1)
      val)))

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

(defun wiz (&optional (b nil b?))
  (if b? (princ (setq SpecCalc::specwareWizard? (and b (if (member b '("nil" "NIL" "off") :test 'string=)
							   nil t))))
    (princ SpecCalc::specwareWizard?))
  (values))

#+allegro
(top-level:alias ("wiz" :case-sensitive) (&optional (b nil b?))
  (if b? (princ (setq SpecCalc::specwareWizard? b))
    (princ SpecCalc::specwareWizard?)))

;; When the following boolean is true, then the System.debug function will
;; take the user into the Lisp debugger.
;; already declared in ~/Work/Generic/Specware4/Library/Base/Handwritten/Lisp/System.lisp :
;; (defvar System-spec::specwareDebug? nil)
(defun swdbg (&optional (b nil b?))
  (if b? 
      (princ (setq System-spec::specwareDebug?
	       (and b (if (member b '("nil" "NIL" "off") :test 'string=)
			  nil t))))
    (princ System-spec::specwareDebug?))
  (values))

#+allegro
(top-level:alias ("swdbg" :case-sensitive) (&optional (b nil b?))
  (if b? (princ (setq System-spec::specwareDebug? b))
    (princ System-spec::specwareDebug?)))

(defun swprb (&optional (b nil b?))
  (if b? 
      (princ (setq System-spec::proverUseBase?
	       (and b (if (member b '("nil" "NIL" "off") :test 'string=)
			  nil t))))
    (princ System-spec::proverUseBase?))
  (values))

#+allegro
(top-level:alias ("swprb" :case-sensitive) (&optional (b nil b?))
  (if b? (princ (setq System-spec::proverUseBase? b))
    (princ System-spec::proverUseBase?)))

(defun swpath  (&optional str)
  (setq str (subst-home (strip-extraneous str)))
  (if (or (null str) (equal str ""))
      (princ (specware::getenv "SWPATH"))
    (let ((str (string str)))
      (speccalc::checkSpecPathsExistence str)
      (princ (specware::setenv "SWPATH" (string str)))
      (setq *saved-swpath* nil))) 
  (values))

#+allegro
(top-level:alias ("swpath" :case-sensitive :string) (&optional str)
  (setq str (subst-home str))
  (if (or (null str) (equal str ""))
      (princ (specware::getenv "SWPATH"))
    (let ((str (if (eq (aref str 0) #\")
		   (read-from-string str)
		 str)))
      (speccalc::checkSpecPathsExistence str)
      (princ (specware::setenv "SWPATH" (string str)))))
  (values))

(defun under-ilisp? ()
  (and (find-package "ILISP")
       (find-symbol "ILISP-COMPILE" "ILISP")))

(defun cd (&optional (dir ""))
  (if (equal dir "")
      (setq dir (specware::getenv "HOME"))
    (setq dir (subst-home dir)))
  (loop while (and (> (length dir) 1) (equal (subseq dir 0 2) ".."))
    do (setq dir (subseq dir (if (and (> (length dir) 2) (eq (elt dir 2) #\/))
			      3 2)))
       (let* ((curr (specware::current-directory))
	      (olddirpath (pathname-directory curr))
	      (pathlen (length olddirpath)))
	 (if (< pathlen 2)
	     (warn "Already at top of directory tree")
	   (specware::change-directory (make-pathname :directory (subseq olddirpath 0 (- pathlen 1))
						      :defaults curr)))))
  (unless (equal dir "")
     #+cmu (unix:unix-chdir dir)
     #-cmu (specware::change-directory dir))
  (let* ((dirpath (specware::current-directory))
	 (newdir (namestring dirpath)))
    (emacs::eval-in-emacs (format nil "(set-default-directory ~s)"
				  (specware::ensure-final-slash newdir)))
    #+cmu (setq common-lisp::*default-pathname-defaults* dirpath)
    (when (under-ilisp?)
      (emacs::eval-in-emacs (format nil "(setq lisp-prev-l/c-dir/file
                                               (cons default-directory nil))"
				    (specware::ensure-final-slash newdir))))
    (princ newdir)
    (values)))

(defun ld (file)
  (load (subst-home file)))

(defun pwd ()
  (princ (namestring (specware::current-directory)))
  (values))

#-allegro
(defun exit ()
  (quit))

#+allegro
(top-level:alias ("quit" ) () (exit))

(defun cl (file)
  (specware::compile-and-load-lisp-file (subst-home file)))

(defun cf (file)
  (compile-file (subst-home file)))

(defun help (&optional command)
  (sw-help command))

#+(or sbcl cmu)
(defun cl::commandp (form)
  (keywordp form))

(defun invoke-command-interactive (command)
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

#+(or cmu mcl sbcl)
(defun cl::invoke-command-interactive (command)
  (invoke-command-interactive command))

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

(defun ls (&optional (str ""))
  (let* ((contents (directory (specware::dir-to-path str)))
	 (sw-files (loop for p in contents
		     when (string= (pathname-type p) "sw")
		     collect p)))
    (list-files sw-files)
    (values)))

(defun dir (&optional (str ""))
  (ls str))

(defun dirr (&optional (str ""))
  (list-directory-rec (specware::dir-to-path str))
  (values))

(defun list-directory-rec (dir)
  (let* ((contents (directory dir))
	 (sw-files (loop for p in contents
		     when (string= (pathname-type p) "sw")
		     collect p)))
    (when (not (null sw-files))
      (format t "~a:~%" (pathname-directory-string dir))
      (list-files sw-files))
    (loop for p in contents
      unless (equal (pathname-name p) "CVS")
      do ;; Work around allegro bug in directory
          #+allegro (setq p (make-pathname :directory (namestring p)))
	  (when (specware::directory? p)
	   (list-directory-rec p))))
  )

(defparameter *dir-width* 80)

(defun list-files (files)
  (when files
    (let* ((names (loop for fil in files collect (pathname-name fil)))
	   (num-files (length names))
	   (max-width (+ 3 (loop for name in names maximize (length name))))
	   (across (floor *dir-width* max-width))
	   (rows (ceiling num-files across))
	   (grouped-names (loop for i from 0 to (- rows 1)
			    collect
			    (loop for j from i to (min (- num-files 1) (* across rows)) by rows
			          collect (elt names j)))))
      (loop for row in grouped-names
	do (loop for fil in row
	     do (format t " ~va" max-width (concatenate 'string fil ".sw")))
	   (format t "~%")))))

(defun pathname-directory-string (p)
  (let* ((dirnames (pathname-directory p))
	 (abbrev-dirnames (speccalc::abbreviatedPath (cdr dirnames)))
	 (main-dir-str (apply #'concatenate 'string
			      (loop for d in (if (string= (car abbrev-dirnames) "~")
						 (cdr abbrev-dirnames)
					       abbrev-dirnames)
				nconcing (list "/" d)))))
    (if (eq (car dirnames) :absolute)
	(if (string= (car abbrev-dirnames) "~")
	    (format nil "~~~a" main-dir-str)
	  main-dir-str)
      (format nil ".~a" main-dir-str))))

(defun pa (&optional pkgname)
  (if (null pkgname)
      (princ (package-name *package*))
    (let ((pkg (find-package pkgname)))
      (if pkg
	  (setq *package* pkg)
	(princ "Not a package"))))
  (values))

(defun untr () (untrace))

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

