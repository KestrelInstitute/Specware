(in-package "CL-USER")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 ALLEGRO
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+Allegro 
(defun save-this-lisp-image (name)
  ;; Save this image.
  (compact-memory t -1 0)
  (set-gc-parameters-for-use nil)
  (excl::dumplisp :name name))

#+Allegro 
(defun generate-new-lisp-application (base-lisp name dir files-to-load files-to-copy)
  (declare (ignore base-lisp)) ; presumes same as this lisp
  ;; Build a fresh image with desired properties.
  ;; (This should be a completely new image, not simply a clone of this image!)
  (compact-memory t -1 0)
  (set-gc-parameters-for-use nil)
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
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 CMU
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+CMU
(defun save-this-lisp-image (name)
  ;; Save this image.
  (setq ext:*gc-verbose* nil)
  (setq ext:*bytes-consed-between-gcs* 20000000)
  ;; See http://cvs2.cons.org/ftp-area/cmucl/doc/cmu-user/extensions.html#toc43
  ;; The :purify option compacts current data and makes GC skip it in resulting image.
  (extensions::save-lisp name :purify t))

#+CMU
(defun generate-new-lisp-application (base-lisp name dir files-to-load files-to-copy)
  ;; Build a fresh image with desired properties.
  ;; (This should be a completely new image, not simply a clone of this image!)
  ;; See http://cvs2.cons.org/ftp-area/cmucl/doc/cmu-user/extensions.html#toc43
  ;; The :purify option compacts current data and makes GC skip it in resulting image.
  (let ((app-file (namestring (make-pathname :directory dir :name name))))
    (ensure-directories-exist app-file)
    (dolist (file files-to-copy) (copy-file file (make-pathname :directory dir :defaults file)))
    (with-open-file (s "/tmp/cmds" :direction :output :if-exists :supersede)
      (format t "~%Commands to be used in lower process ~A to create~%  ~A~%" base-lisp app-file)
      (format t "========================================================~%")
      (format t "(setq ext:*gc-verbose* nil)~%")
      (format s "(setq ext:*gc-verbose* nil)~%")
      (format t "(setq ext:*bytes-consed-between-gcs* 20000000)~%")
      (format s "(setq ext:*bytes-consed-between-gcs* 20000000)~%")
      (let ((env '()))
	(dolist (env-var '(:JFLAWS :ACCORD :SPECWARE4)) 
	  (let ((pair (assoc env-var ext:*environment-list*)))
	    (if (null pair)
		(warn "~S is not in EXT:*ENVIRONMENT-LIST*" env-var)
	      (push pair env))))
	(format t "(setq ext:*environment-list* (quote ~S))~%" env)
	(format s "(setq ext:*environment-list* (quote ~S))~%" env)
	(format t "(setq lisp::lisp-environment-list (quote ~S))~%" nil)
	(format s "(setq lisp::lisp-environment-list (quote ~S))~%" nil))
      (dolist (file files-to-load) 
	(format t "(load ~S)~%" file)
	(format s "(load ~S)~%" file))
      (format t "(extensions::save-lisp ~S :purify t)~%" app-file)
      (format s "(extensions::save-lisp ~S :purify t)~%" app-file)
      (format s "~%")
      (format t "========================================================~%"))
    (let ((process nil))
      (format t "~&~%Output from the lower process being created:~%")
      (format t "~&========================================================~%")
      (unwind-protect 
	  (setq process (run-program base-lisp '() :wait t :input "/tmp/cmds" :output t :error :output))
	(if (null process)
	    (error "Problem creating lower process: ~A" base-lisp)
	  (let ((rc (process-exit-code process)))
	    (format t "~&========================================================~%")
	    (cond ((= rc 0)
		   (format t "~&~%Success saving ~A~%" app-file)
		   (format t "~&Invoke as:")
		   (format t "~& cmucl -core ~A~%~%" app-file))
		  (t
		   (format t "~&Problem: Return code = ~D when saving ~A~%~%" app-file)))
	    (process-close process)))))))

#-mcl
(defun copy-file (a b)
  (with-open-file (old a :direction :input :element-type 'unsigned-byte)
    (with-open-file (new b :direction :output :element-type 'unsigned-byte)
      (let ((eof (cons nil nil)))
	(do ((byte (read-byte old nil eof) (read-byte old nil eof)))
	    ((eq byte eof))
	  (write-byte byte new))))))
		  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 OpenMCL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+MCL
(defun save-this-lisp-image (name)
  (format t "Saving ~a~%" name)
  (set-gc-parameters-for-use nil)
  ;(unless (probe-file name) (create-file  name))  ; temporary bug workaround (??)
  (ccl:save-application name))

#+MCL
(defun generate-new-lisp-application (base-lisp name dir files-to-load files-to-copy)
  ;; Build a fresh image with desired properties.
  ;; (This should be a completely new image, not simply a clone of this image!)
  (let ((app-file (namestring (make-pathname :directory dir :name name))))
    (ensure-directories-exist app-file)
    (unless (probe-file app-file) (create-file app-file)) ; temporary bug workaround (??)
    (dolist (file files-to-copy) (copy-file file (make-pathname :directory dir :defaults file)))
    (with-open-file (s "/tmp/cmds" :direction :output :if-exists :supersede)
      (format t "~%Commands to be used in lower process ~A to create~%  ~A~%" base-lisp app-file)
      (format t "========================================================~%")
      (dolist (file files-to-load) 
	(format t "(load ~S)~%" file)
	(format s "(load ~S)~%" file))
      (format t "(ccl::save-application ~S)~%" app-file)
      (format s "(ccl::save-application ~S)~%" app-file)
      (format s "~%")
      (format t "========================================================~%"))
    (let ((process nil))
      (format t "~&~%Output from the lower process being created:~%")
      (format t "~&========================================================~%")
      (unwind-protect 
	  (setq process (run-program base-lisp '() :wait t :input "/tmp/cmds" :output t :error :output))
	(if (null process)
	    (error "Problem creating lower process: ~A" base-lisp)
	  (let ((rc (process-exit-code process)))
	    (format t "~&========================================================~%")
	    (cond ((= rc 0)
		   (format t "~&~%Success saving ~A~%" app-file)
		   (format t "~&Invoke as:")
		   (format t "~& cmucl -core ~A~%~%" app-file))
		  (t
		   (format t "~&Problem: Return code = ~D when saving ~A~%~%" app-file)))
	    (process-close process)))))))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 Unknown
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#-(or Allegro CMU MCL)
(defun save-this-lisp-image (name)
  (error "Unknown version of lisp -- can't save image named ~A" name))

#-(or Allegro CMU MCL)
(defun generate-new-lisp-application (base-lisp name dir files-to-load files-to-copy)
  (declare (ignore dir files-to-load files-to-copy))
  (error "Unknown version of lisp: ~A -- can't save application named ~A" 
	 base-lisp name))


