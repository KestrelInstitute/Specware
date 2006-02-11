(in-package "USER")

(setq *GC-VERBOSE* nil)

(defun load-builder (specware-dir distribution-dir)
  (let* ((specware-buildscripts-dir 
	  (make-pathname :directory (append (pathname-directory specware-dir) '("Release" "BuildScripts"))
			 :defaults  specware-dir))
	 (lisp-utilities-dir 
	  (make-pathname :directory (append (pathname-directory distribution-dir) '("Lisp_Utilities"))
			 :defaults  distribution-dir)))
    (flet ((my-load (dir-pathname file)
	     (let ((lisp-file (make-pathname :name file :type "lisp" :defaults dir-pathname))
		   (fasl-file (make-pathname :name file :type "x86f" :defaults dir-pathname)))
	       (if (< (file-write-date lisp-file) (or (file-write-date fasl-file) 0))
		   (load fasl-file)
		 (load (compile-file lisp-file))))))
      (my-load lisp-utilities-dir "dist-utils")
      (my-load lisp-utilities-dir "dir-utils")
      (my-load lisp-utilities-dir "MemoryManagement")
      (my-load lisp-utilities-dir "save-image")
      (my-load specware-buildscripts-dir "GatherSpecwareComponents"))))

(defun build-specware-release (i j k verbose?)
  (flet ((my-getenv (var)
	   #+MSWindows (sys::getenv var)
	   #+CMU       (cdr (assoc (intern var "KEYWORD") EXTENSIONS::*ENVIRONMENT-LIST*))
	   #-(or MSWindows CMU) (sys::getenv var)))
    (let ((specware-dir     (concatenate 'string (my-getenv "SPECWARE4")    "/"))	   
	  (distribution-dir (concatenate 'string (my-getenv "DISTRIBUTION") "/")))
      (load-builder specware-dir distribution-dir)
      (funcall 'user::prepare_specware_release i j k specware-dir distribution-dir verbose?))))

