#+Lispworks
(setq *default-package-use-list* '("CL"))

(defpackage "SPECWARE")
(in-package "SPECWARE")

(terpri) ; purely cosmetic

#+allegro(setq excl:*global-gc-behavior* '(10 2.0))

;; The following flag disables the collection of xref information when a lisp
;; file is compiled and loaded. When true, it collects such information,
;; but it seems that for monadic code (with lots of closures), compiling
;; such information is very slow (ie. minutes). Other than changing the
;; load time, there is no change to the behaviour of a program.
#+allegro(setq xref::*record-xref-info* nil)

;;; ---------------
;; The following collection have been adapted from the 2000 load.lisp
;; file. Perhaps they should be factored into a separate file as they
;; are likely to be used for many of the generated lisp applications?

(defun current-directory ()
  ;; we need consistency:  all pathnames, or all strings, or all lists of strings, ...
  #+allegro   (excl::current-directory)      ; pathname
  #+Lispworks (hcl:get-working-directory)    ; ??       (current-pathname)
  #+mcl       (ccl::current-directory-name)  ; ??
  #+cmu       (extensions:default-directory) ; pathname
  #+sbcl      (sb-unix:posix-getcwd)
  )

(defun parse-device-directory (str)
  (let ((found-index (position #\: str)))
    (if found-index
	(values (subseq str 0 found-index)
		(subseq str (1+ found-index)))
      (values nil str))))

(defun change-directory (directory)
  ;; (lisp::format t "Changing to: ~A~%" directory)
  (let ((dirpath (if (pathnamep directory) directory
		   (multiple-value-bind (dev dir)
		       (parse-device-directory directory)
		     (make-pathname :directory dir
				    :device dev)))))
    #+allegro   (excl::chdir          directory)
    #+Lispworks (hcl:change-directory directory)
    #+mcl       (ccl::%chdir          directory)
    #+cmu       (setf (extensions:default-directory) directory)
    #+sbcl      (sb-unix::int-syscall ("chdir" sb-alien:c-string) directory)
    ;; in Allegro CL, at least,
    ;; if (current-directory) is already a pathname, then
    ;; (make-pathname (current-directory)) will fail
    (setq common-lisp::*default-pathname-defaults* dirpath)))

#+mcl					; doesn't have setenv built=in
(defvar *environment-shadow* nil)

(defun getenv (varname)
  #+allegro   (system::getenv varname)
  #+mcl       (or (cdr (assoc (intern varname "KEYWORD") *environment-shadow*))
		  (ccl::getenv varname))
  #+lispworks (hcl::getenv varname) 	;?
  #+cmu       (cdr (assoc (intern varname "KEYWORD") ext:*environment-list*))
  #+sbcl      (sb-ext:posix-getenv  varname)
  )

(defun setenv (varname newvalue)
  #+allegro   (setf (system::getenv varname) newvalue)
  #+mcl       (let ((pr (assoc (intern varname "KEYWORD") *environment-shadow*)))
		(if pr (setf (cdr pr) newvalue)
		  (push (cons (intern varname "KEYWORD") newvalue)
			*environment-shadow*)))
  #+lispworks (setf (hcl::getenv varname) newvalue) 
  #+cmu       (let ((pr (assoc (intern varname "KEYWORD") ext:*environment-list*)))
		(if pr (setf (cdr pr) newvalue)
		  (push (cons (intern varname "KEYWORD") newvalue)
			ext:*environment-list*)))
  #+sbcl      (sb-unix::int-syscall ("setenv" sb-alien:c-string sb-alien:c-string sb-alien:int) varname newvalue 1)
  )

#+(or mcl Lispworks)
(defun make-system (new-directory)
  (let ((*default-pathname-defaults*
	 (make-pathname :name (concatenate 'string new-directory "/")
			:defaults
			#+Lispworks system::*current-working-pathname*
			#-Lispworks *default-pathname-defaults*))
	(old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

#-(or mcl Lispworks)
(defun make-system (new-directory)
  (let ((old-directory (current-directory))
	(*default-pathname-defaults* *default-pathname-defaults*))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

#+sbcl
(setq sb-fasl:*fasl-file-type* "sfsl")	; Default is "fasl" which conflicts with allegro

(defvar *fasl-type*
  #+allegro "fasl"
  #+mcl     "dfsl"
  #+cmu     "x86f"
  #+sbcl    sb-fasl:*fasl-file-type*)

(unless (fboundp 'compile-file-if-needed)
  ;; Conditional because of an apparent Allegro bug in generate-application
  ;; where excl::compile-file-if-needed compiles even if not needed
  (defun compile-file-if-needed (file)
    #+allegro (excl::compile-file-if-needed file)
    #+Lispworks (hcl:compile-file-if-needed file)
    #+(or cmu mcl sbcl)
    (when (> (file-write-date file)
	     (or (file-write-date (make-pathname :defaults file
						 :type *fasl-type*))
		 0)) 
      (compile-file file))))

(defun compile-and-load-lisp-file (file)
   (let ((filep (make-pathname :defaults file :type "lisp")))
     ;(format t "C: ~a~%" filep)
     ;(compile-file filep)
     ;(format t "L: ~a~%" (make-pathname :defaults filep :type nil))
     (compile-file-if-needed filep)
     (load (make-pathname :defaults filep :type nil)))
   )

(defun load-lisp-file (file &rest ignore)
  (declare (ignore ignore))
  (load (make-pathname :defaults file :type "lisp")))

#+mcl					; Patch openmcl bug
(let ((ccl::*warn-if-redefine-kernel* nil))
(defun ccl::overwrite-dialog (filename prompt)
  (if ccl::*overwrite-dialog-hook*
    (funcall ccl::*overwrite-dialog-hook* filename prompt)
    filename))
)

(defparameter temporaryDirectory (namestring #+allegro   (SYSTEM:temporary-directory)
                                             #+Lispworks SYSTEM::*TEMP-DIRECTORY*
					     #+(or mcl cmu sbcl) "/tmp/"
					     ))
(defun temporaryDirectory-0 ()
  (namestring 
   #+allegro      (SYSTEM:temporary-directory)
   #+Lispworks    SYSTEM::*TEMP-DIRECTORY*
   #+(or mcl cmu sbcl) "/tmp/"))

(defun setTemporaryDirectory ()
  (setq temporaryDirectory (temporaryDirectory-0)))

#-mcl
(defun copy-file (source target)
  #+allegro(sys:copy-file source target)
  #+cmu(ext:run-program "cp" (list (namestring source)
				   (namestring target)))
  #+mcl(ccl:run-program "cp" (list (namestring source)
				   (namestring target)))
  #+sbcl(sb-ext:run-program "/bin/cp" (list (namestring source)
					    (namestring target)))
  #-(or allegro cmu sbcl mcl)
  (with-open-file (istream source :direction :input)
    (with-open-file (ostream target :direction :output :if-does-not-exist :create)
      (loop
	(let ((char (read-char istream nil :eof)))
	  (cond
	   ((eq :eof char)
	    (return))
	   ((eq #\Page char)
	    )
	   (t
	    (princ char ostream))))))))

(defun ensure-final-slash (dirname)
  (if (member (elt dirname (- (length dirname) 1))
	      '(#\/ #\\))
      dirname
    (concatenate 'string dirname "/")))

(defun directory? (pathname)
  (and (null (pathname-name pathname))
       (probe-file pathname)))

(defun extend-directory (dir ext-dir)
  (make-pathname :directory
		 (concatenate 'list
			      (pathname-directory dir)
			      (last (pathname-directory ext-dir)))))

(defun make-directory (dir)
  (let ((dir (if (pathnamep dir)
		 (namestring dir)
	       dir)))
    #+allegro (sys::make-directory dir)
    #+cmu     (unix:unix-mkdir dir #o755)
    #+mcl     (ccl:run-program "mkdir" (list dir))
    #+sbcl    (sb-ext:run-program "/bin/mkdir" (list dir))))

(defun copy-directory (source target)
  #+allegro(sys::copy-directory source target)
  #-allegro
  (let ((source-dirpath (if (stringp source)
			    (parse-namestring (ensure-final-slash source))
			  source))
	(target-dirpath (if (stringp target)
			    (parse-namestring (ensure-final-slash target))
			  target)))
    (unless (probe-file target-dirpath)
      (make-directory target-dirpath))
    (loop for dir-item in (directory source-dirpath)
      do (if (directory? dir-item)
	     (copy-directory dir-item (extend-directory target-dirpath dir-item))
	   (copy-file dir-item (merge-pathnames target-dirpath dir-item))))))
