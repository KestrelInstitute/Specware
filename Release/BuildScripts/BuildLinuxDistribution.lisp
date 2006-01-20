(in-package "USER")

(setq *GC-VERBOSE* nil)

(defun load-builder (local-dir distribution-script-dir)
  (let ((local-pathname        (pathname local-dir))
	(distribution-pathname (pathname distribution-script-dir)))
    (flet ((my-load (dir-pathname file)
	     (let ((lisp-file (make-pathname :name file :type "lisp" :defaults dir-pathname))
		   (fasl-file (make-pathname :name file :type "x86f" :defaults dir-pathname)))
	       (if (< (file-write-date lisp-file) (or (file-write-date fasl-file) 0))
		   (load fasl-file)
		 (load (compile-file lisp-file))))))
      (my-load distribution-pathname "dist-utils")
      (my-load distribution-pathname "dir-utils")
      (my-load distribution-pathname "MemoryManagement")
      (my-load distribution-pathname "save-image")
      (my-load local-pathname        "GatherSpecwareComponents"))))

