(defpackage "SPECWARE-TEST")
(in-package "SPECWARE-TEST")

#|
Top-level functions
(specware-test::run-test-directories "dir1" "dir2" ...)
runs specware-test::process-test-file on files dir1/Tests.lisp, 
dir2/Tests.lisp, ...

(specware-test::run-test-directories-rec "dir1" "dir2" ...)
runs specware-test::run-test-directories on "dir1", "dir2", ... and all
their subdirectories.

Note this can be invoked with
M-x sw:run-test-harness
which will run specware-test::run-test-directories-rec on the directory
of the current buffer. (with an argument this runs just 
specware-test::run-test-directories).

(specware-test::process-test-file "file")
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
(defvar *write-log-file* nil)
(defvar *test-harness-stream* t)
(defvar *test-directory*)
(defvar *test-temporary-directory*)
(defvar *test-temporary-directory-name*)
(defvar *test-driver-file-name* "Tests.lisp")

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

(defun run-test-directories-rec-fn (dirs)
  ;; First run the tests for the directories themselves
  (run-test-directories-fn dirs)
  ;; Then recursively test the sub-directories
  (loop for dir in dirs
     do (let* ((dirpath (if (stringp dir)
			    (make-pathname :directory dir :name :wild)
			  dir)))
	  (loop for dir-item in (directory dirpath)
		unless (equal (pathname-name dir-item) "CVS")
		do (setq dir-item (normalize-directory dir-item))
		   (when (specware::directory? dir-item)
		     (run-test-directories-rec-fn (list dir-item)))))))

(defun run-test-directories-fn (dirs)
  (loop for dir in dirs
     do (let* ((dirpath (if (stringp dir)
			    (parse-namestring (specware::ensure-final-slash dir))
			  dir))
	       (filepath (merge-pathnames (make-pathname :name *test-driver-file-name*)
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
				specware::temporaryDirectory)))
      (if (probe-file dir)
	  (get-temporary-directory-i (+ i 1))
	dir))))

(defun process-test-file (file)
  (let* ((*package* (find-package "SPECWARE-TEST"))
	 (path (if (stringp file)
		   (parse-namestring file)
		 file))
	 (*test-directory* (directory-namestring path))
	 (*test-temporary-directory* (get-temporary-directory))
	 (*test-temporary-directory-name* (replace-string (directory-namestring *test-temporary-directory*) "\\" "/"))
	 (old-directory (specware::current-directory)))
    (format t "~%;;;; Running test suite in directory ~a~%" *test-directory*)
    (ensure-directories-exist *test-temporary-directory*)
    (specware::change-directory *test-temporary-directory*)
    (unwind-protect (with-open-file (str path :direction :input)
		      (loop (let ((form (read str nil ':eof)))
			      (if (eq form ':eof)
				  (return)
				(eval form)))))
      (specware::change-directory old-directory))))

(defmacro test-files (&body files)
  `(test-files-fn '(,@files)))

(defun test-files-fn (files)
  (loop for file in files
     do (let* ((filepath (parse-namestring file))
	       (source (merge-pathnames filepath *test-directory*))
	       (target (merge-pathnames filepath *test-temporary-directory*)))
	  (ensure-directories-exist target)
	  (specware::copy-file source target))))

(defmacro test-directories (&body dirs)
  `(test-directories-fn '(,@dirs)))

(defun test-directories-fn (dirs)
  (loop for dir in dirs
     do (let* ((dirpath (make-pathname :directory (if (equal dir ".") nil dir)))
	       (source (merge-pathnames dirpath *test-directory*))
	       (target (merge-pathnames dirpath *test-temporary-directory*)))
	  ;(ensure-directories-exist target)
	  (specware::copy-directory source target nil))))

(defmacro test (&body test-forms)
  `(progn ,@(loop for fm in test-forms collect `(test-1 ,@fm))))

(defun test-0 (&rest args)
  (if *use-separate-process?*
      ()
    (apply 'test-1 args)))

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

(defun test-1 (name &key sw swe swe-spec swl swll lisp show
			 output (output-predicate 'equal)
			 (value "--NotAValue--")
			 (value-predicate 'equal)
			 file-goto-error
			 error files)
  (let (val error-type (error-messages ())
	(emacs::*goto-file-position-store?* t)
	(emacs::*goto-file-position-stored* nil)
	(cl-user::*running-test-harness?* t))
    (let ((test-output (with-output-to-string (*standard-output*)
			 (multiple-value-setq (val error-type)
			   (ignore-errors
			    (if (not (null sw))
				(cl-user::sw (normalize-input sw))
			      (if (not (null swll))
				  (cl-user::swll (normalize-input swll))
				(if (not (null swe))
				  (swe-test swe (normalize-input swe-spec))
				  (if (not (null swl))
				      (cl-user::swl (normalize-input swl))
				    (if (not (null show))
					(cl-user::show (normalize-input show))
				      (if (not (null lisp))
					  (eval (read-from-string (normalize-input lisp))))))))))))))
      (setq test-output (normalize-output test-output))
      (when emacs::*goto-file-position-stored*
	(setf (car emacs::*goto-file-position-stored*)
	  (normalize-output (car emacs::*goto-file-position-stored*))))
      (when (and error-type (not error))
	(push (format nil "~a" error-type) error-messages))
      (when (and (not error-type) error)
	(push "Expected Error did not occur"  error-messages))
      (when (and (not (equal value "--NotAValue--")) (not error-type)
		 (not (funcall value-predicate val value)))
	(push (format nil "Expected:~%~S~%;; Got: ~%~S" value val) error-messages))
      (when (and output (not error-type)
		 (not (funcall output-predicate test-output output)))
	(push (format nil "Expected output: ~%~S~%;; Got:~%~S" output test-output)
	      error-messages))
      (when (and file-goto-error
		 (not (equal file-goto-error emacs::*goto-file-position-stored*)))
	(push (format nil "Expected error location: ~%~s~%;; Got:~%~s" file-goto-error
		      emacs::*goto-file-position-stored*)
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
	(progn (format *test-harness-stream* ";;; Test failed! ~a~%" name)
	       (loop for msg in error-messages
		     do (format *test-harness-stream* ";; ~a~%" msg)))))))

(defun normalize-output (str)
  (if (stringp str)
      (let ((str (replace-string str *test-temporary-directory-name* "$TESTDIR/")))
	(setq str (replace-string str "~/" (concatenate 'string (specware::getenv "HOME") "/")))
	(unless (equal Specware::temporaryDirectory "/tmp/")
	  (setq str (replace-string str Specware::temporaryDirectory "/tmp/")))
	(setq str (replace-string str specware::specware4 "$SPECWARE"))
	(setq str (replace-string str "C:" "")))
    str))

(defun normalize-input (str)
  (setq str (replace-string str "$TESTDIR/" *test-temporary-directory-name*))
  (replace-string str "$SPECWARE" specware::specware4))

;; There must be a better way of doing this
(defun replace-string (str old new)
  (let (match)
    (loop while (setq match (search old str))
	  do (setq str (concatenate 'string
			 (subseq str 0 match)
			 new
			 (subseq str (+ match (length old))))))
    str))
