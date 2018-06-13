(defpackage :Specware-Test (:use :cl))
(in-package :Specware-Test)

(defparameter *global-test-counter* 0)


#|
Top-level functions
(Specware-Test::run-test-directories "dir1" "dir2" ...)
runs Specware-Test::process-test-file on files dir1/Tests.lisp,
dir2/Tests.lisp, ...

(Specware-Test::run-test-directories-rec "dir1" "dir2" ...)
runs Specware-Test::run-test-directories on "dir1", "dir2", ... and all
their subdirectories.

Note this can be invoked with
M-x sw:run-test-harness
which will run Specware-Test::run-test-directories-rec on the directory
of the current buffer. (with an argument this runs just
Specware-Test::run-test-directories).

(Specware-Test::process-test-file "file")
expects a file that contains test forms like

(test-directories ".")
which tells the test harness to copy all the files in the current directory to a
temporary directory where the tests will be run, and

(test ("Colimit with no sharing"
       :sw "colimit"
       :output ";;; Processing spec A in $TESTDIR/colimit.sw
;;; Processing spec E in $TESTDIR/colimit.sw
")
      ("Syntax Error"
       :sw "a"
       :output "Warning: At line   1: 4  Syntactic error with \"{\"
Syntax error: No term or decls in file $TESTDIR/psl1.sw
Syntax error for filename: $TESTDIR/psl1.sw"))

where colimit.sw and a.sw are files in the same directory as the test file.

Each list in the above test form is a test. The first element is a name for
the test used in reporting results. Currently the only tests are running :sw
on a unit and seeing if the terminal output matches the string after :output.
Other options will be implemented later. The $TESTDIR refers to the temporary
directory where the test is being run.

Currently the tests are run in the current specware image. Later there will
be the option to run each (test ...) form in a fresh image.
|#

(defvar *use-separate-process?* nil)
(defvar *verbose?* t)
(defvar *quiet-about-dirs?* nil)
(defvar *quiet-copy?* t)
(defvar *write-log-file* nil)
(defvar *test-harness-stream* t)
(defvar *test-directory*)
(defvar *test-temporary-directory*)
(defvar *test-temporary-directory-name*)
#+darwin (defvar *test-temporary-directory-name-non-private*)
(defvar *test-driver-file-name* "Tests")

;;; These two are same except in windows where first has \'s instead of /'s
(defvar *test-temporary-directory-name0* "SpecwareTest")
(defvar *test-temporary-directory-name* "SpecwareTest")

(defmacro run-test-directories-rec  (&body dirs)
  `(run-test-directories-rec-fn '(,@dirs)))

(defmacro run-test-directories  (&body dirs)
  `(run-test-directories-fn '(,@dirs)))

(defun parse-device-directory (str)
  (let ((found-index (position #\: str)))
    (if found-index
	(values (subseq str 0 found-index)
		(subseq str (1+ found-index)))
      (values nil str))))

(defun normalize-directory (dir)
  #-allegro dir
  #+allegro
  ;; Work around allegro bug in directory
  (let ((name (namestring dir)))
    (multiple-value-bind (dev dir)
	(parse-device-directory name)
      (make-pathname :directory dir
		     :device dev))))

(defun sorted-directory (dirpath)
  (sort (Specware::sw-directory dirpath)
	#'(lambda (a b)
	    (string<= (namestring a) (namestring b)))))

(defun run-test-directories-rec-fn (dirs)
  ;; First run the tests for the directories themselves
  (run-test-directories-fn dirs)
  ;; Then recursively test the sub-directories
  (loop for dir in dirs
    do (let* ((dirpath (if (stringp dir)
			   (Specware::sw-parse-namestring (cl-user::subst-home (Specware::ensure-final-slash dir)))
			 dir)))
	 ;; sort the directory items to make runs more predictable
	 (loop for dir-item in (sorted-directory dirpath)
	   unless (equal (pathname-name dir-item) "CVS")
	   do (setq dir-item (normalize-directory dir-item))
	   (when (Specware::directory? dir-item)
	     (run-test-directories-rec-fn (list dir-item)))))))

(defun run-test-directories-fn (dirs)
  (setq Specware::Specware4 (Specware::getenv "SPECWARE4"))
  (loop for dir in dirs
     do (let* ((dirpath (if (stringp dir)
			    (Specware::sw-parse-namestring (cl-user::subst-home (Specware::ensure-final-slash dir)))
			  dir))
	       (filepath (merge-pathnames (make-pathname :name *test-driver-file-name* :type "lisp")
					  dirpath)))
	  (when (probe-file filepath)
	    (process-test-file filepath)))))

(defun get-temporary-directory ()
  (get-temporary-directory-i 0))

(defun get-temporary-directory-i (i)
  (multiple-value-bind (sec min hour day month year ign1 ign2 ign3)
      (get-decoded-time)
    (declare (ignore sec ign1 ign2 ign3))
    ;; The ~2,,,'0@a format directives ensure that the field takes up two spaces with a
    ;; leading 0 if necessary
    (let ((dir (merge-pathnames (parse-namestring
				 (format nil "~a/~a~2,,,'0@a~2,,,'0@a~2,,,'0@a~2,,,'0@a~a/"
					 *test-temporary-directory-name*
					 year month day hour min i))
				Specware::temporaryDirectory)))
      (if (probe-file dir)
	  (get-temporary-directory-i (+ i 1))
	dir))))

(defun process-test-file (file)
  (let* ((*package* (find-package #+case-sensitive "Specware-Test"
                                  #-case-sensitive "SPECWARE-TEST"))
	 (path (if (stringp file)
		   (parse-namestring file)
		 file))
	 (*test-directory* (directory-namestring path))
	 (*test-temporary-directory* (get-temporary-directory))
         (*test-temporary-directory-name0* (directory-namestring *test-temporary-directory*))
	 (*test-temporary-directory-name* (replace-string *test-temporary-directory-name0* "\\" "/"))
	 #+darwin (*test-temporary-directory-name-non-private* *test-temporary-directory-name*)
	 (*test-temporary-directory-name*
	  #+darwin (format nil "/private~a" *test-temporary-directory-name*)
	  #-darwin *test-temporary-directory-name*)
	 (old-directory (Specware::current-directory)))
    (unless *quiet-about-dirs?*
      (format t "~%;;;; Running test suite in directory ~a~%" *test-directory*))
    (ensure-directories-exist *test-temporary-directory*)
    (Specware::change-directory *test-temporary-directory*)
    (tagbody
     (unwind-protect
	 (handler-case
	     (with-open-file (str path :direction :input)
	       (loop (let ((form (read str nil ':eof)))
		       (if (eq form ':eof)
			   (return)
			 (eval form)))))
	   ;; the most common problem is likely to be a missing close paren,
	   ;; so report eof specifically
	   (end-of-file ()
			; (setq problem? t)
			(warn "Unexpected EOF with ~A" path))
	   (error (condition)
		  ; (setq problem? t)
		  (warn "Unexpected problem with ~A: ~S" path condition)))
       (progn
	 ;; always try to recover and proceed to the next test
	 (Specware::change-directory old-directory)
	 ;; force-ouput so we can monitor interim results of long-running test suites:
	 (force-output)
	 ;; the go here aborts any attempt to throw out to higher levels...
	 (go survive)))
     survive)))

(defmacro test-files (&body files)
  `(test-files-fn '(,@files)))

(defun test-files-fn (files)
  (loop for file in files
     do (let* ((filepath (parse-namestring file))
	       (source (merge-pathnames filepath *test-directory*))
	       (target (merge-pathnames filepath *test-temporary-directory*)))
	  (ensure-directories-exist target)
	  (if *quiet-copy?*
	      (with-output-to-string (*standard-output*)
		(Specware::copy-file source target))
	    (Specware::copy-file source target)))))

(defmacro test-directories (&body dirs)
  `(test-directories-fn '(,@dirs)))

(defun test-directories-fn (dirs)
  #-ALLEGRO-V7.0 (finish-output t)
  (loop for dir in dirs do
    (let* ((dirpath (make-pathname :directory (if (equal dir ".") nil dir)))
	   (source (merge-pathnames dirpath *test-directory*))
	   (target (merge-pathnames dirpath *test-temporary-directory*)))
      #-ALLEGRO-V7.0 (finish-output t)
      ;;(ensure-directories-exist target)
      (if *quiet-copy?*
	  (with-output-to-string (*standard-output*)
	    (Specware::copy-directory source target t))
	(Specware::copy-directory source target t)))))

(defmacro test (&body test-forms)
  ; (setq *global-test-counter* 0)
  `(progn ,@(loop for fm in test-forms collect `(test-1 ,@fm))))

(defun test-0 (&rest args)
  (if *use-separate-process?*
      ()
    (apply 'test-1 args)))

(defvar cl-user::*swe-return-value?*)
(defvar cl-user::*current-swe-spec*)
(defvar cl-user::*current-swe-spec-dir*)

(defun swe-test (swe-str swe-spec)
  (let* ((cl-user::*swe-return-value?* t)
	 (full-swe-spec (if (and swe-spec
				 (not (eql (aref swe-spec 0) #\/))
				 (> (length swe-spec) 1)
				 (not (eql (aref swe-spec 1) #\:)))
			    (in-current-dir swe-spec)
			  swe-spec))
	 (pos (position #\/ full-swe-spec :from-end t))
	 (cl-user::*current-swe-spec*
	  (if pos (subseq full-swe-spec pos) full-swe-spec))
	 (cl-user::*current-swe-spec-dir* (and pos (subseq full-swe-spec 0 pos))))
    (cl-user::swe swe-str)))

(defun in-current-dir (file)
  (concatenate 'string
    (apply #'concatenate 'string
	   (loop for d in (cdr (pathname-directory *test-temporary-directory*))
	       nconcing (list "/" d)))
    "/"
    file))

(defun test-1 (name &key sw swe swe-spec swl swll lisp show showx path (swprb nil swprb?)
			 output
                         use-goal-file
			 (output-predicate 'diff-output)
			 (value "--NotAValue--")
			 (value-predicate 'equal)
			 file-goto-error
			 error files)
  (let ((msg (format nil "~4D Testing : ~A" (incf *global-test-counter*) name)))
    ;;
    ;; Note:  The xemacs variable fi:lisp-evalserver-number-reads needs to be bound
    ;;        to a value larger than the total number of calls that will be made
    ;;        here to eval-in-emacs (which equals the number of tests to be run).
    ;;        Otherwise, subsequent -eval forms in the script "time out" and fail
    ;;        to execute, so the final exit-lisp and kill-emacs forms don't
    ;;        execute, so the script hangs forever.
    ;;
    ;;        The default value for fi:lisp-evalserver-number-reads is just 200,
    ;;        so current test scripts (e.g. Test_Specware4_ACL) set it to 100000.
    ;;
    ;;        Incrementing fi:lisp-evalserver-number-reads here would be a better
    ;;        solution except that it doesn't seem to work.
    ;;
    (Emacs::eval-in-emacs (format nil "(message ~S)" msg)))
  (let (val error-type (error-messages ())
	(Emacs::*goto-file-position-store?* t)
	(Emacs::*goto-file-position-stored* nil)
	(cl-user::*running-test-harness?* t)
	(Specware::*dont-use-x-symbol?* t))
    (let* ((normalized-input (cond ((not (null sw     )) (normalize-input sw       ))
                                   ((not (null swll   )) (normalize-input swll     ))
                                   ((not (null swe    )) (normalize-input swe      ))
                                   ((not (null swl    )) (normalize-input swl      ))
                                   ((not (null show   )) (normalize-input show     ))
                                   ((not (null showx  )) (normalize-input showx    ))
                                   ((not (null lisp   )) (eval (normalize-input lisp)))
                                   ((not (null path   )) (normalize-input path     ))
                                   ((not (null swprb? )) swprb                     )))
           (test-output (with-output-to-string (*standard-output*)
			 (let ((*error-output* *standard-output*)) ; so we also collect warnings and error messages
			   (multiple-value-setq (val error-type)
			     (ignore-errors
			      (cond ((not (null sw     )) (cl-user::sw            normalized-input))
				    ((not (null swll   )) (cl-user::swll          normalized-input))
				    ((not (null swe    )) (swe-test               normalized-input swe-spec))
				    ((not (null swl    )) (cl-user::swl           normalized-input))
				    ((not (null show   )) (cl-user::show          normalized-input))
				    ((not (null showx  )) (cl-user::showx         normalized-input))
				    ((not (null lisp   )) (eval (read-from-string normalized-input)))
				    ((not (null path   )) (cl-user::swpath        normalized-input))
				    ((not (null swprb? )) (cl-user::swprb         normalized-input))
				    )))))))
      (setq test-output (normalize-output test-output))
      (setq output (if (and use-goal-file (not output))
                       (let ((goal-file (format nil "~a/~a.goal" *test-directory* (replace-string normalized-input "#" "_"))))
                         (if (probe-file goal-file)
                             (IO-Spec::readStringFromFile goal-file)
                             (progn
                               (IO-Spec::writeStringToFile-2 test-output goal-file)
                               nil)))
                       (normalize-end-of-lines output)))
      (when Emacs::*goto-file-position-stored*
	(setf (car Emacs::*goto-file-position-stored*)
	  (normalize-output (car Emacs::*goto-file-position-stored*))))
      (when (and error-type (not error))
	(push (format nil "~a" error-type) error-messages))
      (when (and (not error-type) error)
	(push "Expected Error did not occur"  error-messages))
      (when (and (not (equal value "--NotAValue--")) (not error-type)
		 (not (funcall value-predicate val value)))
	(when (and (consp val) (eq (car val) :|Unevaluated|))
	  (setq val "Unevaluated"))
	(push (let ((*print-level* 4)) (format nil "Expected:~%~S~%;; Got: ~%~S" value val))
	      error-messages))
      (when (and output (not error-type))
	(let ((diff-results (funcall output-predicate output test-output)))
	  (unless (null diff-results)
	    (push (format-output-errors diff-results)
		  error-messages))))
      (when (and file-goto-error
		 (not (equal file-goto-error Emacs::*goto-file-position-stored*)))
	(push (format nil "Expected error location: ~%~s~%;; Got:~%~s" file-goto-error
		      Emacs::*goto-file-position-stored*)
	      error-messages))
      (when files
	(loop for file in files
	   unless (probe-file (merge-pathnames (parse-namestring (normalize-input file))
					       *test-temporary-directory*))
	   do (push (format nil "File not created: ~a" file)
		    error-messages)))
      (if (null error-messages)
	  (when *verbose?*
	    (format *test-harness-stream* ";;; Test succeeded. ~a~%" name))
	(progn (format *test-harness-stream* "~&;;; ================================================================================~%")
	       (format *test-harness-stream* ";;; Test failed! ~a~%" name)
	       (loop for msg in error-messages
		     do (format *test-harness-stream* "~&;;; ~a~%" msg))
	       (format *test-harness-stream* "~&;;; ================================================================================~%")
	       )))))

(defun normalize-output (str)
  (if (stringp str)
      (let ((str (replace-string str *test-temporary-directory-name* "$TESTDIR/")))
        #+win32 (setq str (replace-string str *test-temporary-directory-name0* "$TESTDIR\\"))
	#+darwin (setq str (replace-string str *test-temporary-directory-name-non-private* "$TESTDIR/"))
	(setq str (replace-string str "~/" (concatenate 'string (Specware::getenv "HOME") "/")))
	(unless (equal Specware::temporaryDirectory "/tmp/")
	  (setq str (replace-string str Specware::temporaryDirectory "/tmp/")))
	(setq str (replace-string str Specware::Specware4 "$SPECWARE"))
	(setq str (replace-string str "C:$TESTDIR" "$TESTDIR"))
        (setq str (replace-string str "c:$TESTDIR" "$TESTDIR")))
    str))

(defun normalize-input (str)
  (setq str (replace-string str "$TESTDIR/" *test-temporary-directory-name*))
  (replace-string str "$SPECWARE" Specware::Specware4))


;;; Remove \return (for windows)
(defun normalize-end-of-lines (str)
  (replace-string str "
" ""))

;; There must be a better way of doing this
(defun replace-string (str old new)
  (let (match)
    (if (setq match (search old str))
	(concatenate 'string
                     (subseq str 0 match)
                     new
                     (replace-string (subseq str (+ match (length old))) old new))
        str)))

(defun format-output-errors (results)
  (let ((partial-match-at-start? (first results))
	(expected                (second results))
	(got                     (third  results))
	(partial-match-at-end?   (fourth results)))
    (with-output-to-string (s)
      (format s "~%;;; Expected:~%")
      (format s "~&;;;~%")
      (when partial-match-at-start?
	(format s "~&;;; <  ...~%"))
      (dolist (item expected)
	(cond ((consp item)
	       (case (car item)
		 (:optional
		  (dolist (line (cdr item))
		    (format s "~&;;; ?  ~A   [optional]~%" line)))
		 (:alternatives
		  (let ((n 0))
		    (dolist (alt (cdr item))
		      (incf n)
		      (let ((lines (if (consp alt) alt (list alt))))
			(dolist (line lines)
			  (format s "~&;;; ?  ~A   [alt ~D]~%"
				  line n))))))
		 (t
		  (format s "~&;;; ?  ~A   [???]~%" (cdr item)))))
	      (t
	       (format s "~&;;; <  ~A~%" item))))
      (when partial-match-at-end?
	(format s "~&;;; <  ...~%"))
      (format s "~&;;;")
      (format s "~&;;; But got:~%")
      (format s "~&;;;~%")
      (when partial-match-at-start?
	(format s "~&;;; >  ...~%"))
      (dolist (line got)
	(format s "~&;;; >  ~A~%" line))
      (when partial-match-at-end?
	(format s "~&;;; >  ...~%"))
      (format s "~&;;;")
      )))

(defun diff-files (wanted saw)
  (let ((diffs (diff-output (IO-Spec::readStringFromFile wanted)
                            (IO-Spec::readStringFromFile saw))))
    (unless (null diffs)
      (format-output-errors diffs))))

(defun diff-output (wanted saw)
  (labels ((convert-to-lines (text)
	     (if (stringp text)
		 (let ((lines nil)
		       (local-chars nil))
		   (do ((chars (coerce text 'list) (cdr chars)))
		       ((null chars)
			(reverse (cons (coerce (reverse local-chars) 'string)
				       lines)))
		     (let ((char (car chars)))
		       (cond ((equal char #\Newline)
			      (push (coerce (reverse local-chars) 'string)
				    lines)
			      (setq local-chars nil))
			     (t
			      (push char local-chars))))))
	       text))

	   (optional? (x)
	     (and (consp x)
		  (eq (car x) :optional)))

	   (alternatives? (x)
	     (and (consp x)
		  (eq (car x) :alternatives)))

	   (extend-match (wanted saw)
	     (cond ((null wanted)
		    (values wanted saw))
		   ((optional? (car wanted))
		    (if (null saw)
			(extend-match (cdr wanted) saw)
		      (let ((optional-lines (cdr (car wanted))))
			(if (lines-match? (car optional-lines) (car saw))
			    (extend-match (append (cdr optional-lines) (cdr wanted))
					  (cdr saw))
			  (extend-match (cdr wanted) saw)))))
		   ((null saw)
		    (values wanted saw))
		   ((alternatives? (car wanted))
		    (dolist (alternative (cdr (car wanted))
			      ;; all the alternatives fail
			      (values wanted saw))
		      (let ((alternative-lines (if (consp alternative)
						   alternative
						 (list alternative))))
			(when (lines-match? (car alternative-lines)
					    (car saw))
			  ;; if the first line of an alternative matches,
			  ;; commit to using the rest of that alternative
			  (return
			    (extend-match (append (cdr alternative-lines) (cdr wanted))
					  (cdr saw)))))))
		   ((lines-match? (car wanted) (car saw))
		    (extend-match (cdr wanted) (cdr saw)))
		   (t
		    (values wanted saw)))))

    (multiple-value-bind (w-tail s-tail)
	(extend-match (convert-to-lines wanted)
		      (convert-to-lines saw))
      (let ((rev-w-tail (reverse w-tail))
	    (rev-s-tail (reverse s-tail)))
	(multiple-value-bind (w-middle s-middle)
	    (extend-match rev-w-tail rev-s-tail)
	  (let* ((incomplete-match?
		  (or (not (null w-middle))
		      (not (null s-middle))))
		 (partial-match-at-start? (and incomplete-match?
					       (not (eq s-tail saw))))
		 (partial-match-at-end?   (and incomplete-match?
					       (not (eq s-middle rev-s-tail)))))
	    (if (and (null w-middle) (null s-middle))
		nil
	      (list partial-match-at-start?
		    (reverse w-middle)
		    (reverse s-middle)
		    partial-match-at-end?))))))))

(defun lines-match? (x y)
  ;; x is the pattern: ? matches any char in y, * matches any sequence in y
  (labels ((compress-whitespace (chars)
            (let ((result '())
		  (last-char-was-whitespace? t))
	      (dolist (char chars)
		(cond ((member char '(#\Space #\Tab))
		       (unless last-char-was-whitespace?
			 (push #\Space result))
		       (setq last-char-was-whitespace? t))
		      (t
		       (push char result)
		       (setq last-char-was-whitespace? nil))))
	      (reverse
	       (if last-char-was-whitespace?
		   (cdr result)
		 result))))
	   (matches? (x y)
             (do ((x x (cdr x))
		  (y y (cdr y)))
		 ((or (null x) (null y))
		  (and (null y) (or (null x) (equal x '(#\*)))))
	       (unless (eq (car x) (car y))
		 (case (car x)
		   (#\?
		    (return
		     (matches? (cdr x) (cdr y))))
		   (#\*
		    (return
		     (or (matches? (cdr x) (cdr y)) ; matches 1 char
			 (matches? (cdr x) y)       ; matches 0 chars
			 (matches? x (cdr y)))))      ; matches multiple chars
		   (t
		    (return nil)))))))
    (or (string= x y)                   ; was equalp which is case-insensitive
	(matches? (compress-whitespace (coerce x 'list))
		  (compress-whitespace (coerce y 'list))))))
