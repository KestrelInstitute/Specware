(in-package :cl-user)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 Utility (also in load-utilities.lisp)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun copy-file (source target)
  ;; This just copies the file verbatim, as you'd expect...
  #+allegro (sys:copy-file source target :preserve-time t)
  #+mcl     (ccl:copy-file source target :if-exists :supersede)
  #+cmu     (ext:run-program    "cp"      (list (namestring source) (namestring target)))
  #+sbcl    (sb-ext:run-program "/bin/cp" (list (namestring source) (namestring target)))
  #-(or allegro cmu sbcl mcl)
  ;; use unsigned-byte to avoid problems reading x-symbol chars
  ;; For example, read-char might complain for chars with codes above #xC0
  (with-open-file (istream source 
			   :direction    :input 
			   :element-type 'unsigned-byte)
    (with-open-file (ostream target 
			     :direction         :output 
			     :element-type      'unsigned-byte 
			     :if-does-not-exist :create)
      (loop
	(let ((byte (read-byte istream nil :eof)))
	  (cond ((eq :eof byte) 
		 (return))
		(t 
		 (write-byte byte ostream))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 ALLEGRO
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+Allegro 
(defun save-this-lisp-image (name &key executable?)
  (when executable?
    (warn "Ignoring executable? option in Allegro version of save-this-lisp-image"))
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
    files-to-load                     ; e.g. '("BuildPreamble.lisp" "Specware4.lisp")

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
(defun save-this-lisp-image (name &key executable?)
  (when executable?
    (warn "Ignoring executable? option in Allegro version of save-this-lisp-image"))
  ;; Save this image.
  (set-gc-parameters-for-use nil)
  ;; See http://cvs2.cons.org/ftp-area/cmucl/doc/cmu-user/extensions.html#toc43
  ;; The :purify option compacts current data and makes GC skip it in resulting image.
  (ext::save-lisp name :purify t))

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
      (format t "(ext::save-lisp ~S :purify t)~%" app-file)
      (format s "(ext::save-lisp ~S :purify t)~%" app-file)
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
		   (format t "~&Problem: Return code = ~D when saving ~A~%~%" rc app-file)))
	    (process-close process)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 SBCL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+SBCL
(defun save-this-lisp-image (name &key executable?)
  ;; Save this image.
  (set-gc-parameters-for-use nil)
  (sb-ext::save-lisp-and-die name :executable executable?)) ;  :purify nil

#+SBCL
(defun generate-new-lisp-application (base-lisp name dir files-to-load files-to-copy &key executable?)
  ;; Build a fresh image with desired properties.
  ;; (This should be a completely new image, not simply a clone of this image!)
  ;; See http://cvs2.cons.org/ftp-area/sbcl/doc/sbcl-user/extensions.html#toc43
  ;; The :purify option compacts current data and makes GC skip it in resulting image.
  (let ((app-file 
	 (namestring 
	  (let ((n (position #\. name)))
	    (if (null n)
		(make-pathname :directory dir :name name)
	      ;; if there are two dots, who knows what to do??
	      (make-pathname :directory dir 
			     :name (subseq name 0 n)  
			     :type (subseq name (+ n 1) nil)))))))
    (ensure-directories-exist app-file)
    (dolist (file files-to-copy) (copy-file file (make-pathname :directory dir :defaults file)))
    (with-open-file (s "/tmp/cmds" :direction :output :if-exists :supersede)
      (format t "~%Commands to be used in lower process ~A to create~%  ~A~%" base-lisp app-file)
      (format t "========================================================~%")
      ;;(format t "(setq sb-ext:*gc-verbose* nil)~%")
      ;;(format s "(setq sb-ext:*gc-verbose* nil)~%")
      ;;(format t "(setq sb-ext:*bytes-consed-between-gcs* 20000000)~%")
      ;;(format s "(setq sb-ext:*bytes-consed-between-gcs* 20000000)~%")
      (dolist (file files-to-load) 
	(format t "(load ~S)~%" file)
	(format s "(load ~S)~%" file))
      (format t "(sb-ext::save-lisp-and-die ~S :purify nil :executable ~S)~%" app-file executable?)
      (format s "(sb-ext::save-lisp-and-die ~S :purify nil :executable ~S)~%" app-file executable?)
      (format s "~%")
      (format t "========================================================~%"))
    (let ((process nil))
      (format t "~&~%Output from the lower process being created:~%")
      (format t "~&========================================================~%")
      (unwind-protect 
	  (setq process (sb-ext:run-program base-lisp '("--disable-debugger") :wait t :input "/tmp/cmds" :output t :error :output))
	(if (null process)
	    (error "Problem creating lower process: ~A" base-lisp)
	  (let ((rc (process-exit-code process)))
	    (format t "~&========================================================~%")
	    (cond ((= rc 0)
		   (format t "~&~%Success saving ~A~%" app-file)
		   (format t "~&Invoke as:")
		   (format t "~& ~A~%~%" app-file))
		  (t
		   (format t "~&Problem: Return code = ~D when saving ~A~%~%" rc app-file)))
	    (process-close process)))))))

;;; See load-utilities.lisp
;;; #-mcl
;;; (defun copy-file (a b)
;;;   (with-open-file (old a :direction :input :element-type 'unsigned-byte)
;;;     (with-open-file (new b :direction :output :element-type 'unsigned-byte)
;;;       (let ((eof (cons nil nil)))
;;; 	(do ((byte (read-byte old nil eof) (read-byte old nil eof)))
;;; 	    ((eq byte eof))
;;; 	  (write-byte byte new))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 OpenMCL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+MCL
(defun save-this-lisp-image (name &key executable?)
  (when executable?
    (warn "Ignoring executable? option in Allegro version of save-this-lisp-image"))
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
		   (format t "~& OpenMCL -core ~A~%~%" app-file))
		  (t
		   (format t "~&Problem: Return code = ~D when saving ~A~%~%" rc app-file)))
	    ;(process-close process) ;; fn doesn't exist
	    ))))))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 Unknown
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#-(or Allegro CMU MCL SBCL)
(defun save-this-lisp-image (name &key executable?)
  (error "Unknown version of lisp -- can't save image named ~A" name))

#-(or Allegro CMU MCL SBCL)
(defun generate-new-lisp-application (base-lisp name dir files-to-load files-to-copy)
  (declare (ignore dir files-to-load files-to-copy))
  (error "Unknown version of lisp: ~A -- can't save application named ~A" 
	 base-lisp name))


