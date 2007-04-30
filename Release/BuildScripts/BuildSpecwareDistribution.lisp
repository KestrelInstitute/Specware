(in-package "COMMON-LISP-USER")

#+CMU (defparameter ext:*GC-VERBOSE* nil)

#+SBCL (setq sb-fasl:*fasl-file-type* "sfsl") ; default is "fasl", which conflicts with Allegro

(defparameter *fasl-type*
  #+CMU     "x86f"
  #+SBCL    sb-fasl:*fasl-file-type*
  #+Allegro "fasl" 
  #+OpenMCL "???"
  #-(or CMU SBCL Allegro OpenMCL) "unknown-fasl")

(defun load-builder (specware-dir distribution-dir)
  (let* ((specware-buildscripts-dir 
	  (make-pathname :directory (append (pathname-directory specware-dir) '("Release" "BuildScripts"))
			 :defaults  specware-dir))
	 (lisp-utilities-dir 
	  (make-pathname :directory (append (pathname-directory distribution-dir) '("Lisp_Utilities"))
			 :defaults  distribution-dir)))
    (flet ((my-load (dir-pathname file)
	     (let ((lisp-file (make-pathname :name file :type "lisp"      :defaults dir-pathname))
		   (fasl-file (make-pathname :name file :type *fasl-type* :defaults dir-pathname)))
	       (if (< (file-write-date lisp-file) (or (file-write-date fasl-file) 0))
		   (progn (format t "~&Loading ~A~%" fasl-file)
			  (load fasl-file))
		 (progn (format t "~&Loading ~A~%" lisp-file)
			(load (compile-file lisp-file)))))))
      (my-load lisp-utilities-dir "dist-utils")
      (my-load lisp-utilities-dir "dir-utils")
      (my-load lisp-utilities-dir "MemoryManagement")
      (my-load lisp-utilities-dir "save-image")
      (my-load lisp-utilities-dir "LoadUtilities")
      (my-load specware-buildscripts-dir "GatherSpecwareComponents"))))

(defun build-specware-release (verbose?)
  (flet ((my-getenv (var)
	   #+MSWindows (sys::getenv var)
	   #+CMU       (cdr (assoc (intern var "KEYWORD") EXTENSIONS::*ENVIRONMENT-LIST*))
           #+SBCL      (posix-getenv var)
	   #-(or MSWindows CMU SBCL) (sys::getenv var)))
    (let ((specware-dir     (concatenate 'string (my-getenv "SPECWARE4")    "/"))
	  (distribution-dir (concatenate 'string (my-getenv "DISTRIBUTION") "/")))
      (load-builder specware-dir distribution-dir)
      (let ((foo 
	     ;; hide symbol from SBCL, so it doesn't complain it's undefined at compile-time
	     (find-symbol "PREPARE_SPECWARE_RELEASE" "COMMON-LISP-USER"))) 
	(funcall foo specware-dir distribution-dir verbose?)))))

