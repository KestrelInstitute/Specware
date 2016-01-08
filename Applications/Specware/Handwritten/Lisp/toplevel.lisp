(in-package :cl-user)
(defpackage :SpecCalc)
(defpackage :String-Spec)
(defpackage :MSInterpreter)
(defpackage :JGen)
(defpackage :IO-Spec)
(defpackage :System-Spec)
(defpackage :Emacs)
(defpackage :TypeChecker)
(defpackage :SWShell)
(defpackage :swank)
(defpackage :AnnSpecPrinter)
(defpackage :ShowDeps)
(defpackage :ShowImports)
(defpackage :ShowData)
(defpackage :ACL2)
(defpackage :CheckSpec)

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
    (":swpath" . "Query (no arg) or set SWPATH")
    ;; following is useful when running without XEmacs to provide access to shell
;;    (":bash" . "With no args, run the bash shell.\nFor bash fn arg1 .. argn, run fn on args in bash shell [no spaces allowed in any arg]")
    ))

(defun sw-help (&optional argstr)
  ;; argstr should always be a string now, but test for null anyways
  (if (or  (null argstr) (equal argstr ""))  
      (loop for (com . helpstr) in *sw-help-strings* do
           (print-command-doc com helpstr))
      (let ((pr (assoc argstr *sw-help-strings* :test 'equal)))
        (if pr 
            (print-command-doc (car pr) (cdr pr))
            (format t "No documentation for command: ~A." argstr))))
  (values))

(defun print-command-doc (com helpstr)
  (when (eq (elt helpstr 0) #\[)
    (let* ((counter 1)
           (n (dotimes (i (length helpstr))
                (case (elt helpstr (+ i 1))
                  (#\[ (incf counter))
                  (#\] (decf counter)))
                (when (zerop counter)
                  (return (+ i 1))))))
      (unless (null n)
        (setq com (concatenate 'string com " " (subseq helpstr 0 (1+ n))))
        (setq helpstr (subseq helpstr (+ n 2))))))
  (format t (if (> (length com) 23) "~a~%~24T~a~%" "~&~23a ~a~%") com helpstr))

#+allegro
(top-level:alias ("sw-help" :string) (&optional com) (sw-help com))

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
;;; deprecated, but still in use -- see CommandParser.sw
(defun unitIdString? (str)
  (loop for i from 0 to (- (length str) 1)
        always (let ((ch (elt str i)))
		 (or (alphanumericp ch)
		     (member ch '(#\/ #\: #\# #\_ #\- #\~ #\.))))))

(defvar *saved-swpath* nil)
(defvar *temp-file-in-use?* nil)
(defvar *current-temp-file* nil)
(defvar *tmp-counter* 0)
(defvar SpecCalc::noElaboratingMessageFiles)
(defvar SpecCalc::aliasPaths)
(defun sw-temp-file? (fil)
  (equal fil *current-temp-file*))

(defun user-name ()
  (or (Specware::getenv "USER") (Specware::getenv "USERNAME")))

(defun add-to-swpath (dir)
  (let ((swpath (Specware::getenv "SWPATH")))
    (unless *saved-swpath*
      (setq *saved-swpath* swpath))
    (Specware::setenv "SWPATH"
		      (if swpath
			  (format nil (if System-Spec::msWindowsSystem?
                                          "~A;~A" "~A:~A")
				  dir swpath)
			dir))))

(defun maybe-restore-swpath ()
  (when *saved-swpath*
    (Specware::setenv "SWPATH" *saved-swpath*)
    (setq *saved-swpath* nil)))

(defun norm-unitid-str (str)
  (setq *current-temp-file* nil)
  (setq SpecCalc::aliasPaths nil)
  (if (or (null str) (equal str "")) 
      nil ; would prefer "", but then need to revise all the callers 
      (progn 
        (setq str (strip-extraneous str))
        (let ((len (length str)))
          (when (and (> len 3)
                     (string= (subseq str (- len 3)) ".sw"))
            (setq str (subseq str 0 (- len 3)))))
        (setq *temp-file-in-use?* nil)
        (if (unitIdString? str)
            (setq str (subst-home str))
            ;; spec calc term. Need to put it in a temporary file
            (let* ((tmp-dir (format nil "~Asw/" Specware::temporaryDirectory))
                   (tmp-name (format nil "sw_tmp_~D_~D"
                                     (incf *tmp-counter*) 
                                     (ymd-hms)))
;;;		    (tmp-full-name (format nil "~A~A" tmp-dir tmp-name))
;;;		    (tmp-device-uid-pr (split-device tmp-full-name))
;;;		    (tmp-uid (cdr tmp-device-uid-pr))
;;;		    (tmp-device (car tmp-device-uid-pr))
                   (tmp-uid (format nil "/~a" tmp-name))
                   (tmp-full-uid (format nil "~A~A"  tmp-dir tmp-name))
                   (tmp-sw (format nil "~A~A.sw" tmp-dir tmp-name)))
              (ensure-directories-exist tmp-dir)
              (with-open-file (s tmp-sw :direction :output :if-exists :supersede)
                (format s "~A" str))
              (add-to-swpath tmp-dir)
              (setq *temp-file-in-use?* t)
              (setq *current-temp-file* tmp-sw)
              (setq SpecCalc::aliasPaths
                    (list (cons (pathname-to-path (parse-namestring tmp-dir))
                                (pathname-to-path (Specware::ensure-final-slash (Specware::current-directory))))))
              (setq SpecCalc::noElaboratingMessageFiles (cons tmp-full-uid nil))
              (setq str tmp-uid)))
        str)))

(defun split-device (unit-name)
  (if (and (> (length unit-name) 2) (eq (aref unit-name 1) #\:))
      (cons (subseq unit-name 0 3)
	    (subseq unit-name 2))
    (cons (subseq unit-name 0 1) unit-name)))

(defun pathname-to-path (pathname)
  (let ((dev (pathname-device pathname))
	(dir (cdr (pathname-directory pathname))))
    (if (and (stringp dev) (not (equal dev "")))
	(cons (concatenate 'string dev ":") dir)
      dir)))

(defvar *running-test-harness?* nil)
(defvar SWShell::*in-specware-shell?*)
(defvar SWShell::*emacs-eval-form-after-prompt*)

(defun show-error-position (emacs-error-info position-delta)
  (when emacs-error-info
    (let ((error-file (first emacs-error-info))
	  (linepos (second emacs-error-info))
	  (charpos (third emacs-error-info)))
      (unless *running-test-harness?*
	(if (sw-temp-file? error-file)
	    (let ((emacs-command (format nil "(show-error-on-new-input ~a t)" (+ charpos position-delta))))
	      (if SWShell::*in-specware-shell?*
		  (setq SWShell::*emacs-eval-form-after-prompt* emacs-command)
		(Emacs::eval-in-emacs emacs-command)))
	  (Emacs::eval-in-emacs (format nil "(goto-file-position ~s ~a ~a)"
					error-file linepos charpos)))))))

(defvar *last-unit-Id-_loaded* nil)

(defun sw0 (x)
  (Specware::runSpecwareUID (norm-unitid-str x))
  (maybe-restore-swpath)
  (values))

#+allegro(top-level:alias ("sw0" :case-sensitive) (x) (sw0 (string x)))

(defun set-base (x)
  (Specware::setBase_fromLisp (norm-unitid-str x))
  (maybe-restore-swpath)
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

;;; The following is incomplete, but only used for internal utilities
(defun unit-to-file-name (unitid)
  (let ((hash-pos (position '#\# unitid)))
    (when hash-pos
      (setq unitid (subseq unitid 0 hash-pos)))
    (concatenate 'string unitid ".sw")))

(defvar *force-reprocess-of-unit* nil)

;This is the function invoked by the 'proc' command in the Specware shell.
(defun sw (&optional x)
  (setq x (norm-unitid-str x))
  (flet ((sw-int (x)
	   (let ((val (if x
			  (Specware::evaluateUID_fromLisp-1-1 (setq *last-unit-Id-_loaded* x) *force-reprocess-of-unit*)
			(if *last-unit-Id-_loaded*
			    (Specware::evaluateUID_fromLisp-1-1 *last-unit-Id-_loaded* *force-reprocess-of-unit*)
			  (format t "ERROR: No previous unit evaluated~%")))))
	     (show-error-position Emacs::*goto-file-position-stored* 1)
	     (maybe-restore-swpath)
	     val)))
    (if *running-test-harness?*
	(sw-int x)
      (let ((Emacs::*goto-file-position-store?* t)
	    (Emacs::*goto-file-position-stored* nil))
	(sw-int x)))))

#+allegro
(top-level:alias ("sw" :case-sensitive :string) (&optional x)
  (sw x))

(defun parse-qid (qid-str)
  (let ((syms (String-Spec::splitStringAt-2 (String-Spec::removeWhiteSpace qid-str) ".")))
    (if (null (cdr syms))
        (MetaSlang::mkQualifiedId-2 Script::wildQualifier (first syms))
        (MetaSlang::mkQualifiedId-2 (if (string= (first syms) "") MetaSlang::UnQualified
                                        (first syms))
                                    (second syms)))))

(defun split-arg-string (argstr)
  (if (null argstr) argstr
    (let ((strquote_pos (position  '#\" argstr)))
      (if (null strquote_pos)
          (String-Spec::splitStringAt-2 argstr " ")
        (let ((end_strquote_pos (position  '#\" argstr :start (+ strquote_pos 1))))
          (if (null end_strquote_pos)
              (progn (warn "Unmatched string quote")
                     '(nil))
            (concatenate 'list
                         (String-Spec::splitStringAt-2 (subseq argstr 0 strquote_pos) " ")
                         (list (subseq argstr strquote_pos (+ end_strquote_pos 1)))
                         (split-arg-string (subseq argstr (+ end_strquote_pos 1))))))))))

(defun show (&optional argstr)
  (let* ((args (String-Spec::removeEmpty (split-arg-string argstr)))
         (arg1_len (length (car args)))
         (args (if (null args) (list nil)
                   (if (and (eql (length args) 1)
                            (position #\. (car args))
                            (> arg1_len 1)
                            (not (and (> arg1_len 3)
                                      (string= (subseq (car args) (- arg1_len 3)) ".sw"))))
                       (cons nil args)
                       args)))
         (num-args (length args)))
    (let* ((uid (if (or (null (car args)) (string= (car args) "."))
                    *last-unit-Id-_loaded*
                    (norm-unitid-str (car args))))
           (qids (map 'list #'parse-qid (cdr args))))
      (setq *last-unit-Id-_loaded* uid)
      (flet ((show-int (uid)
               (Specware::evaluatePrint_fromLisp-2 uid qids)
               (show-error-position Emacs::*goto-file-position-stored* 1)
               (maybe-restore-swpath)
               (values)))
        (if *running-test-harness?*
            (show-int uid)
            (let ((Emacs::*goto-file-position-store?* t)
                  (Emacs::*goto-file-position-stored* nil))
              (show-int uid)))))))

#+allegro
(top-level:alias ("show" :case-sensitive :string) (&optional x)
  (show x))

(defun showx (&optional x)
  (setq x (norm-unitid-str x))
  (flet ((show-int (x)
	   (let ((SpecCalc::printSpecExpanded? t)
                 (AnnSpecPrinter::printPragmas? nil))
	     (declare (special SpecCalc::printSpecExpanded? AnnSpecPrinter::printPragmas?))
	     (if x
		 (Specware::evaluatePrint_fromLisp-2 (setq *last-unit-Id-_loaded* (string x))
						     (use-x-symbol?))
	       (if *last-unit-Id-_loaded*
		   (Specware::evaluatePrint_fromLisp-2 *last-unit-Id-_loaded*
						       (use-x-symbol?))
		 (format t "No previous unit evaluated~%"))))
	   (show-error-position Emacs::*goto-file-position-stored* 1)
	   (maybe-restore-swpath)
	   (values)))
    (if *running-test-harness?*
	(show-int x)
      (let ((Emacs::*goto-file-position-store?* t)
	    (Emacs::*goto-file-position-stored* nil))
	(show-int x)))))

#+allegro
(top-level:alias ("showx" :case-sensitive :string) (&optional x)
  (showx x))

(defvar *slicing-lisp?* nil)

;; Not sure if an optional UnitId make sense for swl
(defun swl-internal (x &optional y)
  ;; scripts depend upon this returning true iff successful
  (setq x (norm-unitid-str x))
  (flet ((swl1 (x y)
	   (let ((val (Specware::evaluateLispCompile_fromLisp-3 x
								(if y (cons :|Some| (subst-home y))
								  '(:|None|))
                                                                *slicing-lisp?*)))
	     (show-error-position Emacs::*goto-file-position-stored* 1)
	     (maybe-restore-swpath)
	     val)))
    (if *running-test-harness?*
	(swl1 x y)
      (let ((Emacs::*goto-file-position-store?* t)
	    (Emacs::*goto-file-position-stored* nil))
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

;This is the function invoked by the Specware shell command 'gen-lisp'.
(defun swl (&optional args)
  ;; scripts depend upon this returning true iff successful
  (let ((r-args (if (not (null args))
		    (extract-final-file-name args)
		  (if (equal (car *last-swl-args*) *last-unit-Id-_loaded*)
		      *last-swl-args*
		      (list *last-unit-Id-_loaded*)))))
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

(defun swll-internal (x y load?)
  ;; scripts depend upon this returning true iff successful
  (let ((lisp-file-name (subst-home (or y (concatenate 'string
					    Specware::temporaryDirectory
					    (user-name)
					    "-swe/"
					    "lgen_lisp_tmp"))))
	(x (norm-unitid-str x)))
    (flet ((swll1 (x lisp-file-name)
	     (let ((val (if (Specware::evaluateLispCompileLocal_fromLisp-2
			     x (cons :|Some| lisp-file-name))
			    (let (#+allegro *redefinition-warnings*)
			      ;; scripts depend upon the following returning true iff successful
			      (if load?
				  (Specware::compile-and-load-lisp-file lisp-file-name)
				(compile-file lisp-file-name)))
			  "Specware Processing Failed!")))
	       (show-error-position Emacs::*goto-file-position-stored* 1)
	       (maybe-restore-swpath)
	       val)))
      (if *running-test-harness?*
	  (swll1 x lisp-file-name)
	(let ((Emacs::*goto-file-position-store?* t)
	      (Emacs::*goto-file-position-stored* nil))
	  (swll1 x lisp-file-name))))))

;This is the function invoked by the Specware shell command 'lgen-lisp'.
(defun swll (&optional args)
  ;; scripts depend upon this returning true iff successful
  (let ((r-args (if (not (null args))
		    (extract-final-file-name args)
		  *last-swl-args*)))
    (if r-args
	(progn (setq *last-swl-args* r-args)
	       (swll-internal (string (first r-args))
			      (if (not (null (second r-args)))
				  (string (second r-args)) nil)
			      t))
      (format t "No previous unit evaluated~%"))))

#+allegro
(top-level:alias ("swll" :case-sensitive) (&optional &rest args)
  (let ((r-args (if (not (null args))
		    args
		  *last-swl-args*)))
    (if r-args
	(progn (setq *last-swl-args* r-args)
	       (swll-internal (string (first r-args))
			      (if (not (null (second r-args)))
				  (string (second r-args)) nil)
			      t))
      (format t "No previous unit evaluated~%"))))


(defun swll-no-load (&optional args)
  ;; scripts depend upon this returning true iff successful
  (let ((r-args (if (not (null args))
		    (extract-final-file-name args)
		  *last-swl-args*)))
    (if r-args
	(progn (setq *last-swl-args* r-args)
	       (swll-internal (string (first r-args))
			      (if (not (null (second r-args)))
				  (string (second r-args)) nil)
			      nil))
      (format t "No previous unit evaluated~%"))))

(defun unitIdChar (ch)
  (or (member ch '(#\/ #\_ #\#))
      (let ((num (char-code ch)))
	(or (and (>= num (char-code #\0))
		 (<= num (char-code #\9)))
	    (and (>= num (char-code #\a))
		 (<= num (char-code #\z)))
	    (and (>= num (char-code #\A))
		 (<= num (char-code #\Z)))))))

(defun split-filename-for-path (filename)
  ;; Splits absolute filename into head suitable for swpath entry and
  ;; tail suitable for a uid. Note that uids cannot contain ~ or spaces
  ;; Assumes sw::normalize-filename has been called
  (let (head pos) 
    (if (eq (elt filename 1) #\:)
	(progn (setq head (subseq filename 0 3))
	       (setq filename (subseq filename 3)))
      (progn (setq head (subseq filename 0 1))
	     (setq filename (subseq filename 1))))
    (loop while (and (position-if-not 'unitIdChar filename)
                     (setq pos (position #\/ filename)))
      do (setq head (concatenate 'string head (subseq filename 0 (1+ pos))))
         (setq filename (subseq filename (1+ pos))))
    (cons head (concatenate 'string "/" filename))))

(defun name-relative-to-swpath (filename)
  (let ((swpath (get-swpath)))
    (loop for dir in (Specware::split-components swpath (if System-Spec::msWindowsSystem?
                                                            '(#\;) '(#\:)))
       do (let ((dir (norm-unitid-str dir)))
	    (if (string-equal dir (subseq  filename 0 (min (length dir) (length filename))))
		(let ((rel-filename (subseq filename (length dir))))
		  (unless (position-if-not 'unitIdChar rel-filename)
		    (return (if (eq (elt rel-filename 0) #\/)
				rel-filename
			      (concatenate 'string "/" rel-filename)))))))
       finally (return (split-filename-for-path filename)))))

(defpackage :SWE) ; for access to results

(defvar *swe-use-interpreter?* t)   ; nil means used compiled lisp code
(defvar *current-swe-spec*     nil) ; nil means no import
(defvar *current-swe-spec-dir* "")
(defvar swe::tmp)

(defun swe-spec (&optional x)
  (when (null x)
    (setq x (and (consp *last-swl-args*) (car *last-swl-args*))))
  (if (null x) (format t "~&No previous spec")
    (progn
      (setq x (norm-unitid-str x))
      (let ((x0 x)
            (swpath-relative? (eq (elt x 0) #\/)))
        (setq *current-swe-spec-dir* "")
	(unless swpath-relative?
	  (setq x (name-relative-to-swpath (format nil "~A~A" (Specware::current-directory) x)))
          (when (consp x)
            (setq *current-swe-spec-dir* (car x)
                  x (cdr x)))
          ;(format t "~&coercing ~A~A~%" (or *current-swe-spec-dir* "") x)
          )
	;;      (setq x (norm-unitid-str x))
	(let ((saved-swpath (and *saved-swpath*
				 (Specware::getenv "SWPATH"))))
	  (cond ((sw (string x0))	; restores *saved-swpath* if necessary
		 (setq *current-swe-spec* x)
		 (format t "~&Subsequent evaluation commands will now import ~A~A.~%"
			 *current-swe-spec-dir*
			 (if (equal *current-swe-spec-dir* "") x (subseq x 1)))
		 (unless *swe-use-interpreter?*
		   (format t "~&The following will produce, compile and load code for this spec:~%")
		   (format t "~&:swll ~A~%" x)))
		(t
		 (format t "~&:swe-spec had no effect.~%" x)
		 (if *current-swe-spec*
		     (format t "~&Subsequent :swe commands will still import ~A.~%" *current-swe-spec*)
		   (format t "~&Subsequent :swe commands will still import just the base spec.~%"))))))))
  (values))

#+allegro
(top-level:alias ("swe-spec" :case-sensitive :string) (x) 
  (swe-spec x))

(defvar *swe-print-as-slang?* nil)
(defvar *swe-return-value?* nil)
(defvar *expr-begin-offset* 2)		; Difference between beginning of expr in input and in file

(defun ymd-hms ()
  (multiple-value-bind (second minute hour day month year)
      (decode-universal-time (get-universal-time))
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
  (let* ((tmp-dir (format nil "~A~A_swe/" Specware::temporaryDirectory (user-name)))
	 (tmp-name (format nil "swe_tmp_~D_~D"
			   (incf *tmp-counter*) 
			   (ymd-hms)))
	 (tmp-uid (format nil "/~A"     tmp-name))
	 (tmp-sw  (format nil "~A~A.sw" tmp-dir tmp-name))
	 (*current-temp-file* tmp-sw)
	 (tmp-cl  (format nil "~A~A"    tmp-dir tmp-name))
	 (SpecCalc::noElaboratingMessageFiles (list tmp-cl))
	 (TypeChecker::complainAboutImplicitPolymorphicOps? nil)
	 (old-swpath (or (Specware::getenv "SWPATH") ""))
	 (new-swpath (format nil
			     (if System-Spec::msWindowsSystem? "~A;~A;~A" "~A:~A:~A")
			     tmp-dir *current-swe-spec-dir* old-swpath))
	 (Emacs::*goto-file-position-store?* t)
	 (Emacs::*goto-file-position-stored* nil)
	 (parser-type-check-output)
	 (input-line-num 2)
	 parsed-ok?
	 value)
    (declare (special SpecCalc::noElaboratingMessageFiles TypeChecker::complainAboutImplcitPolymorphicOps?))
    ;; clear any old values or function definitions:
    (makunbound  'swe::tmp)
    (fmakunbound 'swe::tmp)
    (ensure-directories-exist tmp-dir)
    (with-open-file (s tmp-sw :direction :output :if-exists :supersede)
      (format s "spec~%")
      (when nil   ; *swe-use-interpreter?*  handled explicitly in Interpreter
	(format s "  import ~A~%" "/Library/InterpreterBase")
	(incf input-line-num))
      (when (not (null *current-swe-spec*))
	(format s "  import ~A~%" *current-swe-spec*)
	(incf input-line-num))
      (format s "  def swe.tmp = ~A~%endspec~%" x))
    ;; Process unit id:
    (unwind-protect
	(progn
	  (Specware::setenv "SWPATH" new-swpath)
	  (setq parser-type-check-output
	    (with-output-to-string (*standard-output*)
	      (let ((*error-output* *standard-output*)
		    (SpecCalc::numberOfTypeErrorsToPrint 2))
		(setq parsed-ok? (Specware::evaluateUID_fromLisp-1-1 tmp-uid nil)))))
	  (when parsed-ok?
	    (if *swe-use-interpreter?*
		(setq value (Specware::evalDefInSpec-2 tmp-uid `(:|Qualified| . ("swe" . "tmp"))))
	       (with-output-to-string (*standard-output*)
                 (Specware::evaluateLispCompileLocal_fromLisp-2 tmp-uid (cons :|Some| tmp-cl))))))
      (Specware::setenv "SWPATH" old-swpath))
    (if Emacs::*goto-file-position-stored* ; Parse or type-check error
	(progn (princ (trim-error-output parser-type-check-output))
	       (show-error-position Emacs::*goto-file-position-stored* -16))
      (progn
	(princ parser-type-check-output)
	(if *swe-use-interpreter?*
	    (if (eq (car value) :|None|)
		(warn "No value for expression?")
	      (if *swe-return-value?* (cdr value)
		(MSInterpreter::printMSIValue-2 (cdr value)
                                                (use-x-symbol?))))
	  (let (#+allegro *redefinition-warnings*)
	    ;; Load resulting lisp code:
	    (load (make-pathname :type "lisp" :defaults tmp-cl))
	    (if *swe-return-value?* swe::tmp
	      ;; Print result:
	      (let ((*package* (find-package :SW-User)))
		(cond ((boundp 'swe::tmp)
		       (if *swe-print-as-slang?*
			   (format t "~%Value is ~%~/Specware::pprint-dt/~%"
				   swe::tmp)
			 (format t "~%Value is ~S~2%" swe::tmp)))
		      ((fboundp 'swe::tmp)
		       (let* ((code #+allegro (excl::func_code #'swe::tmp)
				    #-allegro (symbol-function 'swe::tmp))
			      (auxfn (find-aux-fn code)))
			 (format t "~%Function is ")
			 (pprint code)
			 (format t "~%")
			 (when (and (symbolp auxfn) (fboundp auxfn))
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

(defvar Specware::*dont-use-x-symbol?* t)

(defun use-x-symbol? ()
  (and (not Specware::*dont-use-x-symbol?*)
       (fboundp 'Emacs::eval-with-emacs)
       (funcall 'Emacs::eval-with-emacs "(sw-use-x-symbol?)")))

(defvar interpreterBaseName "/Library/InterpreterBase")
(defvar MSInterpreter::interpreterBaseSpec)

;; Specware::initializeInterpreterBaseAux is funcalled from 
;; Specware::initializeInterpreterBase-0 in Preface.lisp, which in turn is called from
;; intializeSpecware in Specware.sw
;; This indirection avoids compiler warnings about Specware::initializeInterpreterBase-0
;; being undefined when Specware4.lisp is compiled.
(defun Specware::initializeInterpreterBaseAux () 
  (unwind-protect
      (progn
	;; clear base names so adding defs for base ops won't complain
	(SpecCalc::clearBaseNames_fromLisp nil)
	(setq MSInterpreter::interpreterBaseSpec (sc-val interpreterBaseName)))
    ;; restore base names
    (SpecCalc::setBaseNames_fromLisp nil)))

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
    (when (setq pos (search "ERROR: Could not match type constraint for" errstr))
      (setq errstr (subseq errstr pos)))
    (when (setq pos (search " At line" errstr))
      (setq errstr (concatenate 'string (subseq errstr 0 pos) (subseq errstr (+ pos 16)))))
    (when (setq pos (search " found in " errstr))
      (setq errstr (subseq errstr 0 pos)))
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
  (if (listp code)
      (let ((fn (car code)))
        (cond ((equal fn 'function)
               (find-aux-fn (cadr code)))
              ((equal fn 'block)
               (find-aux-fn (caddr code)))
              ((equal fn 'lambda)
               (find-aux-fn (caddr code)))
              (t
               fn)))
    code))

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
	       (when (integerp rawlinepos)
		 (setq str (concatenate 'string
					(subseq str 0 pos)
					(format nil "~a" (+ rawlinepos *expr-begin-offset*))
					(subseq str (1+ endnumpos)))))))
	   (incf pos)		; ensure progress
	   ))
    str))

;;; --------------------------------------------------------------------------------
;;;
;;; Java Gen
;;;
;;; --------------------------------------------------------------------------------

(defun swj-internal (x &optional y)
  (let ((Emacs::*goto-file-position-store?* t)
	(Emacs::*goto-file-position-stored* nil))
    (Specware::evaluateJavaGen_fromLisp-2 (norm-unitid-str x) 
					  (if y 
					      (cons :|Some| y)
					    '(:|None|)))
    (show-error-position Emacs::*goto-file-position-stored* 1)
    (maybe-restore-swpath)
    (values)))

(defvar *last-swj-args* nil)

(defun swj (&optional args)
  (let ((r-args (if (not (null args))
		    (extract-final-file-name args)
		  *last-swj-args*)))
    (if r-args
	(progn (setq *last-swj-args* r-args)
	       (swj-internal (string (first r-args))
			     (if (not (null (second r-args)))
				 (string (second r-args)) nil)))
      (format t "No previous unit evaluated~%"))))

#+allegro
(top-level:alias ("swj" :case-sensitive) (&optional &rest args)
  (swj args))

(defun swj-config-pkg (&optional pkg)
  #+(or allegro lispworks)
  (defparameter #+allegro excl::*redefinition-warnings*
    #+Lispworks lispworks::*redefinition-action*
    nil)
  (if (not (null pkg))
      (defparameter JGen::packageName (string pkg))
    ())
  (format t "~A~%" JGen::packageName))

(defun swj-config-dir (&optional dir)
  (setq dir (subst-home dir))
  #+(or allegro lispworks)
  (defparameter #+allegro excl::*redefinition-warnings*
    #+Lispworks lispworks::*redefinition-action*
    nil)
  (if (not (null dir))
      (defparameter JGen::baseDir (string dir))
    ())
  (format t "~A~%" JGen::baseDir))

(defun swj-config-make-public (&optional ops)
  #+(or allegro lispworks)
  (defparameter #+allegro excl::*redefinition-warnings*
    #+Lispworks lispworks::*redefinition-action*
    nil)
  (if (not (null ops))
      (defparameter JGen::publicOps ops)
    ())
  (format t "~A~%" JGen::publicOps))

(defun swj-config-reset ()
  #+(or allegro lispworks)
  (defparameter #+allegro excl::*redefinition-warnings*
    #+Lispworks lispworks::*redefinition-action*
    nil)
  (defparameter JGen::packageName (string "specware.generated"))
  (defparameter JGen::baseDir (string "."))
  (defparameter JGen::publicOps nil))

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
  (let* ((pkgname (format nil "~A" JGen::packageName))
	 (bdir (format nil "~A" JGen::baseDir))
	 (ops (format nil "~A" JGen::publicOps))
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
   (let ((Emacs::*goto-file-position-store?* t)
	 (Emacs::*goto-file-position-stored* nil))
     (Specware::evaluateCGen_fromLisp-2 (norm-unitid-str x)
					(if y (cons :|Some| (subst-home y))
					  '(:|None|)))
     (show-error-position Emacs::*goto-file-position-stored* 1)
     (maybe-restore-swpath)
     (values)))

;This is the function invoked by the Specware shell command 'gen-c'.
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
      (format t "No previous unit processed for C generation.~%"))))

;produces a value of an Option type, either None if val is nil, or Some val
(defun wrap-option (val)
  (if val
      (cons :|Some| val)
      '(:|None|)))
  
; This is the function invoked by the Specware shell command 'gen-c-thin'.
; This function is the Lisp 'wrapper' of the Metaslang code that does the real work.
(defun gen-c-thin (&optional argstring)
  ;; This calls the Lisp translation of op evaluateGenCThin (from Languages/SpecCalculus/Semantics/Specware.sw).
  ;; The "-2" in the Lisp function name is added during the translation to Lisp.
  ;; My approach is to have the Metaslang code do all of the argument parsing.
  (let ((val (Specware::evaluateGenCThin-2 (wrap-option argstring)
                                           (wrap-option *last-unit-Id-_loaded*))))
    ;;evaluateGenCThin returns an optional string to store in *last-unit-Id-_loaded*
    (if (equal val '(:|None|))
        nil ;does this return value matter?
        ;; strip the :|Some| to get the string
        (setq *last-unit-Id-_loaded* (cdr val)))))

; This is the function invoked by the Specware shell command 'showdeps'.
; This function is the Lisp 'wrapper' of the Metaslang code that does the real work.
(defun showdeps (&optional argstring)
  ;; This calls the Lisp translation of op evaluateShowDeps (from Languages/SpecCalculus/AbstractSyntax/ShowDeps.sw).
  ;; The "-2" in the Lisp function name is added during the translation to Lisp.
  ;; My approach is to have the Metaslang code do all of the argument parsing.
  (let ((val (ShowDeps::evaluateShowDeps-3 (wrap-option argstring)
                                           (wrap-option *last-unit-Id-_loaded*)
                                           (home-dir))))
    ;;evaluateShowDeps returns an optional string to store in *last-unit-Id-_loaded*
    (if (equal val '(:|None|))
        nil ;does this return value matter?
        ;; strip the :|Some| to get the string
        (setq *last-unit-Id-_loaded* (cdr val)))))

;;; This is the function invoked by the Specware shell command 'showimports'.
;;; This function is the Lisp 'wrapper' of the Metaslang code that does the real work.
(defun showimports (&optional argstring)
  ;; This calls the Lisp translation of op evaluateShowImports (from
  ;; Languages/SpecCalculus/AbstractSyntax/ShowImports.sw).  The "-3" in
  ;; the Lisp function name is added during the translation to Lisp.
  ;; My approach is to have the Metaslang code do all of the argument
  ;; parsing.
  (let ((val (ShowImports::evaluateShowImports-3 (wrap-option argstring)
                                           (wrap-option *last-unit-Id-_loaded*)
                                           (home-dir))))
    ;;evaluateShowImports returns an optional string to store in *last-unit-Id-_loaded*
    (if (equal val '(:|None|))
        nil ;does this return value matter?
        ;; strip the :|Some| to get the string
        (setq *last-unit-Id-_loaded* (cdr val)))))

;;; This is the function invoked by the Specware shell command 'gen-acl2'/
;;; This function is the Lisp 'wrapper' of the Metaslang code that does the real work.
(defun gen-acl2 (&optional argstring)
  (let ((val (ACL2::evaluateGenACL2-3 (wrap-option argstring)
                                            (wrap-option *last-unit-Id-_loaded*)
                                            (home-dir))))
    (if (equal val '(:|None|))
        nil
        (setq *last-unit-Id-_loaded* (cdr val)))))


;;; This is the function invoked by the Specware shell command 'showdata'.
;;; This function is the Lisp 'wrapper' of the Metaslang code that does the real work.
(defun showdata (&optional argstring)
  ;; This calls the Lisp translation of op evaluateShowData (from
  ;; Languages/SpecCalculus/AbstractSyntax/ShowData.sw).  The "-3" in
  ;; the Lisp function name is added during the translation to Lisp.
  ;; My approach is to have the Metaslang code do all of the argument
  ;; parsing.
  (let ((val (ShowData::evaluateShowData-3 (wrap-option argstring)
                                           (wrap-option *last-unit-Id-_loaded*)
                                           (home-dir))))
    ;;evaluateShowData returns an optional string to store in *last-unit-Id-_loaded*
    (if (equal val '(:|None|))
        nil ;does this return value matter?
        ;; strip the :|Some| to get the string
        (setq *last-unit-Id-_loaded* (cdr val)))))

;;; This is the function invoked by the Specware shell command 'showdatav'.
;;; This function is the Lisp 'wrapper' of the Metaslang code that does the real work.
(defun showdatav (&optional argstring)
  ;; This calls the Lisp translation of op evaluateShowDataV (from
  ;; Languages/SpecCalculus/AbstractSyntax/ShowData.sw).  The "-3" in
  ;; the Lisp function name is added during the translation to Lisp.
  ;; My approach is to have the Metaslang code do all of the argument
  ;; parsing.
  (let ((val (ShowData::evaluateShowDataV-3 (wrap-option argstring)
                                           (wrap-option *last-unit-Id-_loaded*)
                                           (home-dir))))
    ;;evaluateShowDataV returns an optional string to store in *last-unit-Id-_loaded*
    (if (equal val '(:|None|))
        nil ;does this return value matter?
        ;; strip the :|Some| to get the string
        (setq *last-unit-Id-_loaded* (cdr val)))))

;;; This is the function invoked by the Specware shell command 'checkspec'.
;;; This function is the Lisp 'wrapper' of the Metaslang code that does the real work.
(defun checkspec (&optional argstring)
  ;; This calls the Lisp translation of op evaluateCheckSpec (from
  ;; Languages/SpecCalculus/AbstractSyntax/ASW_Printer_SExp.sw).  The "-3" in
  ;; the Lisp function name is added during the translation to Lisp.
  ;; My approach is to have the Metaslang code do all of the argument
  ;; parsing.
  (let ((val (CheckSpec::evaluateCheckSpec-3 (wrap-option argstring)
                                           (wrap-option *last-unit-Id-_loaded*)
                                           (home-dir))))
    ;;evaluateCheckSpec returns an optional string to store in *last-unit-Id-_loaded*
    (if (equal val '(:|None|))
        nil ;does this return value matter?
        ;; strip the :|Some| to get the string
        (setq *last-unit-Id-_loaded* (cdr val)))))


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
  ;;(format t "args=~A ~A~%" args (length args))
  (let* ((make-args (if (and (first args) (not (null args)))
			(cons (norm-unitid-str (first args)) (rest args))
		      *last-make-args*))
	 (make-command (if (Specware::getenv "SPECWARE4_MAKE") (Specware::getenv "SPECWARE4_MAKE") "make"))
	 (user-make-file-suffix ".mk")
	 (sw-make-file "$(SPECWARE4)/Library/Clib/Makerules")
	 (make-file "swcmake.mk"))
    (setq *last-make-args* make-args)
    (if make-args
	(let* ((unitid (first make-args))
	       (cbase (getCFileNameFromUnitid unitid))
	       (user-make-file (concatenate 'string cbase user-make-file-suffix))
	       (hw-src-1 (concatenate 'string cbase "_main.c"))
	       (hw-src-2 (concatenate 'string cbase "_test.c"))
	       (hw-src (if (IO-Spec::fileExistsAndReadable hw-src-1) hw-src-1
			 (if (IO-Spec::fileExistsAndReadable hw-src-2) hw-src-2 nil)))
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
	  (with-open-file (mf make-file :direction :output :if-exists :supersede)
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
	      (when (IO-Spec::fileExistsAndReadable user-make-file)
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
	  (maybe-restore-swpath)
	  (run-cmd make-command (list "-f" (format nil "~A" make-file))))
      ;; else: no make-args
      (progn
	(format t "No previous unit evaluated")
	(if (IO-Spec::fileExistsAndReadable make-file)
	    (progn
	      (format t "; using existing make-file ~s...~%" make-file)
	      (run-cmd make-command (list "-f" (format nil "~A" make-file)))
	      )
	  (format t " and no previous make-file found; please supply a unit-id as argument.~%")
	  )))))
 

#+allegro
(top-level:alias ("make" :case-sensitive :string) (&optional args)
  (make args))

;; returns the name of the cfile from the given unitid
;; by substituting #' with underscores
(defun getCFileNameFromUnitid (unitId)
  (cl:substitute #\_  #\# (string unitId))
  )

;; --------------------------------------------------------------------------------

(defvar *last-swpc-args* nil)

(defun swpc (&optional args)
  (let ((r-args (if (not (null args))
		    (extract-final-file-name args)
		  *last-swpc-args*)))
    (if r-args
	(progn (setq *last-swpc-args* r-args)
	       (swpc-internal (string (first r-args))
			      (if (not (null (second r-args)))
				  (string (second r-args)) nil)))
      (format t "No previous unit evaluated~%"))))

(defun swpc-internal (x &optional y)
  (let ((Emacs::*goto-file-position-store?* t)
	(Emacs::*goto-file-position-stored* nil))
    (let ((val (Specware::evaluateProofCheck_fromLisp-2
		(norm-unitid-str (string x))
		(if y (cons :|Some| (string (subst-home y)))
		  '(:|None|)))))
      (show-error-position Emacs::*goto-file-position-stored* 1)
      (maybe-restore-swpath)
      val)))

;; --------------------------------------------------------------------------------

(defun swpf-internal (x &optional y &key (obligations t))
  (let ((Emacs::*goto-file-position-store?* t)
	(Emacs::*goto-file-position-stored* nil))
    (let ((val (Specware::evaluateProofGen_fromLisp-3
		(norm-unitid-str (string x))
		(if y (cons :|Some| (string (subst-home y)))
		  '(:|None|))
		obligations)))
      (show-error-position Emacs::*goto-file-position-stored* 1)
      (maybe-restore-swpath)
      val)))

(defun lswpf-internal (x &optional y &key (obligations t))
  (let ((Emacs::*goto-file-position-store?* t)
	(Emacs::*goto-file-position-stored* nil))
    (let ((val (Specware::evaluateProofGenLocal_fromLisp-3
		(norm-unitid-str (string x))
		(if y (cons :|Some| (string (subst-home y)))
		  '(:|None|))
		obligations)))
      (show-error-position Emacs::*goto-file-position-stored* 1)
      (maybe-restore-swpath)
      val)))

(defvar *last-swpf-args* nil)

(defun swpf (&optional args)
  (let ((r-args (if (not (null args))
		    (extract-final-file-name args)
		  *last-swpf-args*)))
    (if r-args
	(progn (setq *last-swpf-args* r-args)
	       (swpf-internal (string (first r-args))
			      (if (not (null (second r-args)))
				  (string (second r-args)) nil)))
      (format t "No previous unit evaluated~%"))))

(defun lswpf (&optional args)
  (let ((r-args (if (not (null args))
		    (extract-final-file-name args)
		  *last-swpf-args*)))
    (if r-args
	(progn (setq *last-swpf-args* r-args)
	       (lswpf-internal (string (first r-args))
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
;					    Specware::temporaryDirectory
;					    "cl-current-file")))))
;    (if (Specware::evaluateLispCompileLocal_fromLisp-2
;	 x (cons :|Some| lisp-file-name))
;	(let (#+allegro *redefinition-warnings*)
;	  (Specware::compile-and-load-lisp-file lisp-file-name))
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

(defpackage :System-Spec)

;; When the following boolean is true, then the System.debug function will
;; take the user into the Lisp debugger.
;; already declared in ~/Work/Generic/Specware4/Library/Legacy/Utilities/Handwritten/Lisp/System.lisp :
;; (defvar System-spec::specwareDebug? nil)
(defun swdbg (&optional (b nil b?))
  (if b? 
      (princ (setq System-Spec::specwareDebug?
	       (and b (if (member b '("nil" "NIL" "off") :test 'string=)
			  nil t))))
    (princ System-Spec::specwareDebug?))
  (values))

#+allegro
(top-level:alias ("swdbg" :case-sensitive) (&optional (b nil b?))
  (if b? (princ (setq System-Spec::specwareDebug? b))
    (princ System-Spec::specwareDebug?)))

(defun swprb (&optional (b nil b?))
  (if b? 
      (princ (setq System-Spec::proverUseBase?
	       (and b (if (member b '("nil" "NIL" "off") :test 'string=)
			  nil t))))
    (princ System-Spec::proverUseBase?))
  (values))

#+allegro
(top-level:alias ("swprb" :case-sensitive) (&optional (b nil b?))
  (if b? (princ (setq System-Spec::proverUseBase? b))
    (princ System-Spec::proverUseBase?)))

(defun swpath  (&optional str)
  (setq str (strip-extraneous str))
  (let ((newpath (if (or (null str) (equal str ""))
		     (or (Specware::getenv "SWPATH") "")
		   (let ((str (normalize-path (string str) nil)))
		     (if (SpecCalc::checkSpecPathsExistence str)
			 (progn (Specware::setenv "SWPATH" (string str))
				(setq *saved-swpath* nil)
				(string str))
		       (progn (format t "Keeping old path:~%")
			      (Specware::getenv "SWPATH")))))))
    (princ (normalize-path newpath t))
    (values)))

(defun normalize-path (path add-specware4-dir?)
  (let* ((path-dirs (mapcar #'(lambda (nm)
				(Specware::ensure-final-slash (subst-home nm)))
			    (Specware::split-components path
                                                        (if System-Spec::msWindowsSystem?
                                                            '(#\;) '(#\:)))))
	 (specware4-dir (substitute #\/ #\\ (Specware::ensure-final-slash (Specware::getenv "SPECWARE4"))))
	 (path-dirs-c-sw (if (and add-specware4-dir?
				  (not (member specware4-dir path-dirs :test 'string-equal)))
			     (nconc path-dirs (list specware4-dir))
			   path-dirs)))
    (format nil
	    (if System-Spec::msWindowsSystem? "~{~a~^;~}" "~{~a~^:~}")
	    path-dirs-c-sw)))

(defun get-swpath ()
  (normalize-path (or (Specware::getenv "SWPATH") "") t))

#+allegro
(top-level:alias ("swpath" :case-sensitive :string) (&optional str)
  (setq str (subst-home str))
  (if (or (null str) (equal str ""))
      (princ (Specware::getenv "SWPATH"))
    (let ((str (if (eq (aref str 0) #\")
		   (read-from-string str)
		 str)))
      (SpecCalc::checkSpecPathsExistence str)
      (princ (Specware::setenv "SWPATH" (string str)))))
  (values))

(defun ld (file)
  (if (null file)
      (format t "Error: ld requires an argument")
    (load (subst-home file))))

(defun pwd ()
  (princ (namestring (Specware::current-directory)))
  (values))

(defun Specware::exit ()
  #+allegro (exit)
  #+sbcl    (sb-ext:exit)
  #-(or allegro sbcl) (quit))

#+allegro
(top-level:alias ("quit" ) () (exit))

(defun cl (file)
  (if (null file)
      (format t "Error: cl requires an argument")
    (Specware::compile-and-load-lisp-file (subst-home file))))

(defun cf (file)
  (if (null file)
      (format t "Error: cf requires an argument")
    (compile-file (subst-home file))))

(defun help (&optional command)
  (sw-help command))

#|
#+(or sbcl cmu)
(Specware::without-package-locks
 (defun cl::commandp (form)
  (keywordp form)))
|#

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
    (if (or (null ch)			; interactive, end of command
	    (eq ch #\Newline))		; batch, first char after whitespace is newline      
	(if (fboundp fn)
	    (funcall fn)
	  (progn (warn "Unknown command ~s" command)
		 (values)))
      (if (fboundp fn)
	  (funcall fn (read-line))
	(progn (read-line)
	       (warn "Unknown command ~s" command)
	       (values))))))
#|
#+(or cmu mcl sbcl)
(Specware::without-package-locks
 (defun cl::invoke-command-interactive (command)
   (invoke-command-interactive command)))
|#

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

(defun pathname-directory-abbrev-string (p)
  (let* ((dirnames (pathname-directory p))
	 (abbrev-dirnames (SpecCalc::abbreviatedPath (cdr dirnames)))
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
    (let ((pkg (or (find-package pkgname)
		   (find-package (string-upcase pkgname)))))
      (if pkg
	  (setq *package* pkg)
	(princ "Not a package"))))
  (values))

(defun untr () (untrace))

(defun tr (&optional (nms-string ""))
  (when (eq nms-string nil) (setq nms-string ""))
  (eval `(trace ,@(map 'list #'read-from-string (toplevel-parse-args nms-string)))))

#+allegro
(top-level:alias ("ls" :string) (&optional (str ""))
  #+unix      (shell (format nil "ls ~A"  str))
  #+mswindows (shell (format nil "dir ~A" str))
  #-(or unix mswindows) (format t "~&Neither the UNIX nor MSWINDOWS feature is present, so I don't know what to do!~%")
  )

#+allegro
(top-level:alias ("dir" :string) (&optional (str ""))
  #+unix      (shell (format nil "ls ~A"  str))
  #+mswindows (shell (format nil "dir ~A" str))
  #-(or unix mswindows) (format t "~&Neither the UNIX nor MSWINDOWS feature is present, so I don't know what to do!~%")
  )

;; Function for getting Value from UID string, for use in testing
(defun sc-val (str)
  (let ((id-str (norm-unitid-str str)))
  (cddr (Specware::evaluateUnitId id-str))))

;; following is useful when running without XEmacs to provide access to shell
;; #+allegro
;; (top-level:alias ("bash" :string) (&optional (str "")) (bash str))

;;; NEEDS WORK...
(defun bash (&optional (str ""))
  (block return-from-bash
    (if (and (stringp str) (> (length str) 0))
	(let* ((fn_and_args 
		;; TODO: not quite right -- shouldn't break on spaces within strings, etc.
		(String-Spec::splitStringAt-2 str " ")) 
	       (fn   (car fn_and_args))
	       (args (cdr fn_and_args)))
	  (handler-bind ((error 
			  #'(lambda (x)
			      (declare (ignore x))
			      (handler-bind ((error 
					      #'(lambda (x)
						  (format t "~%~A~%" x)
						  (format t "~%~A doesn't seem to be accessible.~%" fn)
						  (print str)
						  (format t "~&Trying again with call to to bash using arg ~S" str)
						  (return-from return-from-bash nil))))
				(return-from return-from-bash
				  (progn
				    (format t "~&In bash shell:~%")
				    (Specware::setenv "PS1" "") ; no need for prompt given one command
				    #-ALLEGRO-V7.0 (finish-output)
				    (Specware::run_cmd-2 "bash" (list "-c" str))))))))
	    (Specware::run_cmd-2 fn args)))
      (handler-bind ((error 
		      #'(lambda (x)
			  (declare (ignore x))
			  (format t "~%The bash shell doesn't seem to be available.~%")
			  #+(or mswindows win32) (format t "~&(It is installed as part of the Cygwin installation.)~%")
			  (return-from bash nil))))
	;; ACCORD feature is set by $ACCORD/Scripts/Lisp/BuildPreamble.lisp at build time
	(format t 
		(if (member :ACCORD cl::*features*)
		     "~&Interactive bash shell:~%Type exit to return to Accord Shell.~2%"
		  "~&Interactive bash shell:~%Type exit to return to Specware Shell.~2%"))
	;; (Specware::setenv "PS1" "\\s-\\v\\$ ") ; to get something like "bash-2.05b$ "
	#+cmu (format t "~&Note: The shell prompt may be unsynchronized, appearing *after* input.~2%")
	#-ALLEGRO-V7.0 (finish-output)
	(unwind-protect
	    (Specware::run_cmd-2 "bash" (list "-i"))
	  (format t (if (member :ACCORD cl::*features*)
			"~2&Back in Accord Shell.~2%"
		      "~2&Back in Specware Shell.~2%"))
	  )))))

