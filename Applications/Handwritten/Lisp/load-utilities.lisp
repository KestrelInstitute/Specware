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
  #+allegro(excl::current-directory)
  #+Lispworks(hcl:get-working-directory)  ;(current-pathname)
  #+mcl(ccl::current-directory-name)
  #+cmu (extensions:default-directory)
  )

(defun change-directory (directory)
  ;; (lisp::format t "Changing to: ~A~%" directory)
  #+allegro(excl::chdir directory)
  #+Lispworks (hcl:change-directory directory)
  #+mcl (ccl:cwd directory)
  #+cmu (setf (extensions:default-directory) directory)
  (setq common-lisp::*default-pathname-defaults* (current-directory)))

(defun getenv (varname)
  #+allegro (sys:getenv varname)
  #+cmucl (cdr (assoc (intern varname "KEYWORD") ext:*environment-list*)))

#+Lispworks
(defun make-system (new-directory)
  (let ((*default-pathname-defaults*
	 (make-pathname :name (concatenate 'string new-directory "/")
			:defaults
			system::*current-working-pathname*))
	(old-directory (current-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

#-Lispworks
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

(defun getenv (x)
  #+allegro (system::getenv x)
  #+mcl (ccl::getenv x)
  #+lispworks (hcl::getenv x) 		;?
  )

(unless (fboundp 'compile-file-if-needed)
  ;; Conditional because of an apparent Allegro bug in generate-application
  ;; where excl::compile-file-if-needed compiles even if not needed
  (defun compile-file-if-needed (file)
    #+allegro (excl::compile-file-if-needed file)
    #+Lispworks (hcl:compile-file-if-needed file)
    #+(or cmu mcl) (when t 
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
  (load (make-pathname :defaults file :type "lisp")))
