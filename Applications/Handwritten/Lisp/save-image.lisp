(in-package "CL-USER")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 ALLEGRO
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+Allegro 
(defun save-lisp-image (name)
  ;; DEVELOPMENT
  (compact-memory t -1 0)
  (set-gc-parameters-for-use t)
  (excl::dumplisp :name name))

#+Allegro 
(defun save-lisp-executable (name dir files-to-load files-to-copy)
  ;; APPLICATION
  (compact-memory t -1 0)
  (set-gc-parameters-for-use t)
  (generate-application 

    ;; name of application
    name                              ; e.g. "Specware4"

    ;; directory where application (with accompanying files) should go
    dir                               ; e.g. "C:/Progra~1/Specware4-0-7/Specware4/distribution/Specware4/"

    ;; list of files to load
    files-to-load                     ; e.g. '("BuildPreamble.lisp" "Specware4.lisp" "license.lisp")

    ;; list of files to copy to the distribution directory
    :application-files  files-to-copy ; e.g. (list (in-specware-dir "Release/Windows/Specware4.cmd"))

    ;; Possible option instead of excl::delete-directory-and-files call
    :allow-existing-directory  t

    ;; the image does not have a compiler neither during the build nor after.
    ;; The application has the interpreter only.
    :include-compiler  nil

    ;; which runtime? the other option is :dynamic which includes the compiler
    :runtime  :standard
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 CMU
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+CMU
(defun save-lisp-image (name)
  ;; DEVELOPMENT
  (setq ext:*gc-verbose* nil)
  (setq ext:*bytes-consed-between-gcs* 20000000)
  ;; See http://cvs2.cons.org/ftp-area/cmucl/doc/cmu-user/extensions.html#toc43
  ;; The :purify option compacts current data and makes GC skip it in resulting image.
  (extensions::save-lisp name :purify t))

#+CMU
(defun save-lisp-executable (name dir files-to-load files-to-copy)
  ;; APPLICATION
  (setq ext:*gc-verbose* nil)
  (setq ext:*bytes-consed-between-gcs* 20000000)
  (setq ext:*environment-list* ())
  (setq lisp::lisp-environment-list ())
  ;; See http://cvs2.cons.org/ftp-area/cmucl/doc/cmu-user/extensions.html#toc43
  ;; The :purify option compacts current data and makes GC skip it in resulting image.
  (cd dir)
  (dolist (file files-to-load) (load file))
  (let ((here (pathname-directory *current-directory*)))
    (dolist (file files-to-copy) 
      (copy-file file (make-pathname :dir here :defaults file))))
  (extensions::save-lisp name :purify t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 OpenMCL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+MCL
(defun save-lisp-image (name)
  ;; DEVELOPMENT
  (unless (probe-file name)
    (create-file  name))  ; temporary bug workaround
  (ccl:save-application name))

#+MCL
(defun save-lisp-executable (name dir files-to-load files-to-copy)
  ;; APPLICATION
  (let ((name (make-pathname :dir dir :name name)))
    (unless (probe-file name)
      (create-file  name))  ; temporary bug workaround
    (ccl:save-application name)))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 Unknown
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#-(or Allegro CMU MCL)
(defun save-lisp-image (name)
  (error "Unknown version of lisp -- can't save image named ~A" name))

#-(or Allegro CMU MCL)
(defun save-lisp-executable (name)
  (error "Unknown version of lisp -- can't save application named ~A" name))


