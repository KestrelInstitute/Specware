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
  )

(defun change-directory (directory)
  ;; (lisp::format t "Changing to: ~A~%" directory)
  #+allegro   (excl::chdir          directory)
  #+Lispworks (hcl:change-directory directory)
  #+mcl       (ccl::%chdir          directory)
  #+cmu       (setf (extensions:default-directory) directory)
  ;; in Allegro CL, at least,
  ;; if (current-directory) is already a pathname, then
  ;; (make-pathname (current-directory)) will fail
  (setq common-lisp::*default-pathname-defaults* (current-directory)))

(defun getenv (varname)
  #+allegro   (system::getenv varname)
  #+mcl       (ccl::getenv varname)
  #+lispworks (hcl::getenv varname) 	;?
  #+cmu       (cdr (assoc (intern varname "KEYWORD") ext:*environment-list*))
  )

(defun setenv (varname newvalue)
  #+allegro   (setf (system::getenv varname) newvalue)
  #+mcl       (setf (ccl::getenv varname) newvalue)
  #+lispworks (setf (hcl::getenv varname) newvalue) 
  #+cmu       (setf (cdr (assoc (intern varname "KEYWORD") ext:*environment-list*))
		newvalue)
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
  (let ((old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

#+mcl
(defun make-system (new-directory)
  (let ((*default-pathname-defaults*
	 (make-pathname :name (concatenate 'string new-directory "/")
			:defaults (current-directory)))
	(old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

(defvar *fasl-type*
  #+allegro "fasl"
  #+mcl     "dfsl"
  #+cmu     "x86f")

(unless (fboundp 'compile-file-if-needed)
  ;; Conditional because of an apparent Allegro bug in generate-application
  ;; where excl::compile-file-if-needed compiles even if not needed
  (defun compile-file-if-needed (file)
    #+allegro (excl::compile-file-if-needed file)
    #+Lispworks (hcl:compile-file-if-needed file)
    #+(or cmu mcl) (when (> (file-write-date file)
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
