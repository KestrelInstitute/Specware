;; for simplicity, use the same package that GatherComponents.lisp uses
(defpackage :Distribution)
(in-package :Distribution)

(eval-when (compile eval load)
  #+Allegro (require "dist-utils")
  ; #-Allegro (load    "dist-utils")
  #+Allegro (require "MemoryManagement")
  ; #-Allegro (load    "MemoryManagement")
  )

(defun save-this-lisp-image (name)
  #+Allegro (save-this-allegro-image name)
  #+cmu     (save-this-cmu-image     name)
  #+sbcl    (save-this-sbcl-image    name)
  #+mcl     (save-this-mcl-image     name)
  #-(or Allegro cmu mcl sbcl) (error "Unknown version of lisp -- can't save image named ~A" name))

(defun generate-new-lisp-application (base-lisp name target-dir files-to-load files-to-copy include-compiler? &key executable?)
  #-Allegro (declare (ignore include-compiler?))
  (let ((target-dir (namestring target-dir))
	(files-to-load (mapcar #'namestring files-to-load))
	(files-to-copy (mapcar #'namestring files-to-copy)))
    #+Allegro (generate-new-allegro-application base-lisp name target-dir files-to-load files-to-copy include-compiler?)
    #+cmu     (generate-new-cmu-application     base-lisp name target-dir files-to-load files-to-copy)
    #+sbcl    (generate-new-sbcl-application    base-lisp name target-dir files-to-load files-to-copy :executable? executable?)
    #+mcl     (generate-new-mcl-application     base-lisp name target-dir files-to-load files-to-copy)
    #-(or Allegro cmu mcl sbcl) (error "Unknown version of lisp: ~A -- can't save application named ~A" base-lisp name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 ALLEGRO
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+Allegro
(defun save-this-allegro-image (name)
  ;; Save this image.
  (user::compact-memory t -1 0)
  (user::set-gc-parameters-for-use nil)
  (excl::dumplisp :name name))

#+Allegro
(defun generate-new-allegro-application (base-lisp name target-dir files-to-load files-to-copy include-compiler?)
  (declare (ignore base-lisp)) ; presumes same as this lisp
  ;;
  ;; Build a fresh image with desired properties.
  ;; (This should be a completely new image, not simply a clone of this image!)
  ;;
  ;; (user::compact-memory t -1 0)
  ;; (user::set-gc-parameters-for-use nil)
  ;;
  (excl::generate-application name		; e.g. "Specware4"
			      target-dir	; e.g. "C:/Progra~1/Specware4-0-7/Specware4/distribution/Specware4/"
			      files-to-load	; e.g. '("BuildPreamble.lisp" "Specware4.lisp")
			      
			      ;; list of files to copy to the distribution directory
			      :application-files         files-to-copy      ; e.g. (list (in-specware-dir "Release/Windows/Specware4.cmd"))
			      :allow-existing-directory  t                  ; Possible option instead of excl::delete-directory-and-files call
			      :include-compiler          include-compiler?
			      :runtime                   (if include-compiler? :dynamic :standard)
			      ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 CMU
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+cmu
(defun save-this-cmu-image (name)
  ;; Save this image.
  (setq ext:*gc-verbose* nil)
  (setq ext:*bytes-consed-between-gcs* 20000000)
  ;; See http://cvs2.cons.org/ftp-area/cmucl/doc/cmu-user/extensions.html#toc43
  ;; The :purify option compacts current data and makes GC skip it in resulting image.
  (extensions::save-lisp name :purify t))

#+cmu
(defun generate-new-cmu-application (base-lisp name dir files-to-load files-to-copy)
  ;; Build a fresh image with desired properties.
  ;; (This should be a completely new image, not simply a clone of this image!)
  ;; See http://cvs2.cons.org/ftp-area/cmucl/doc/cmu-user/extensions.html#toc43
  ;;

  (let ((app-file (namestring (make-pathname :directory dir :name name))))
    ;;
    (ensure-directories-exist app-file)
    (flet ((copy-file (a b)
	     (with-open-file   (old a :direction :input  :element-type 'unsigned-byte)
	       (with-open-file (new b :direction :output :element-type 'unsigned-byte)
		 (do ((byte (read-byte old nil 'nil) (read-byte old nil 'nil)))
		     ((null byte))
		   (write-byte byte new))))))
      (dolist (file files-to-copy) 
	(copy-file file (make-pathname :directory dir :defaults file))))
    ;;
    ;; We build a script file that looks something like this, and then run it in an inferior lisp.
    ;; The :purify option compacts current data and makes GC skip it in resulting image.
    ;; ------------------------------------------------------------------------------------------
    ;; (setq ext:*gc-verbose* nil)
    ;; (setq ext:*bytes-consed-between-gcs* 20000000)
    ;; (setq ext:*environment-list* (quote (:Accord "...") (:Specware "...")))
    ;; (setq lisp::*environment-list* (quote nil))
    ;; (load "aaa")
    ;; ...
    ;; (load "zzz")
    ;; (extensions::save-lisp "foo" :purify t)
    ;; 
    ;; ------------------------------------------------------------------------------------------
    ;;
    (with-open-file (s "/tmp/cmds" :direction :output :if-exists :supersede)
      (flet ((add-command-line (msg &rest args)
	       (let ((str (apply #'format nil msg args)))
		 (when *verbose*
		   (format t "~A~%" str))
		 (format s "~A~%" str))))
	(when *verbose*
	  (format t "~%Commands to be used in lower process ~A to create~%  ~A~%" base-lisp app-file)
	  (format t "========================================================~%"))
	(add-command-line     "(setq ext:*gc-verbose* nil)                    ")
	(add-command-line     "(setq ext:*bytes-consed-between-gcs* 20000000) ")
	(let ((env '()))
	  (dolist (env-var '(:SPECWARE4 :DISTRIBUTION :ACCORD :PLANWARE :JFLAWS))
	    (let ((pair (assoc env-var ext:*environment-list*)))
	      (if (null pair)
		  (warn "~S is not in EXT:*ENVIRONMENT-LIST*" env-var)
		(push pair env))))
	  (add-command-line   "(setq ext:*environment-list* (quote ~S))       " env)
	  (add-command-line   "(setq lisp::lisp-environment-list (quote ~S))  " nil))
	(when (not *verbose*)
	  (add-command-line   "(handler-bind                                  ")
	  (add-command-line   "   ((warning (lambda (c)                       ")
	  (add-command-line   "              (let* ((args  (conditions::condition-actual-initargs c))                      ")
	  (add-command-line   "                     (fmsg  (getf args :format-control))                                    ")
	  (add-command-line   "                     (fargs (getf args :format-arguments)))                                 ")
	  (add-command-line   "                (cond ((equalp fmsg \"~~A also shadows the following symbols:~~%  ~~S\")    ")
	  (add-command-line   "                       (format *error-output*                                               ")
	  (add-command-line   "                               \"~~&;;; Noticed ~~4D shadowed symbols in ~~A package.~~%\"  ")
	  (add-command-line   "                               (length (second fargs)) (first fargs))                       ")
	  (add-command-line   "                       (invoke-restart (find-restart 'muffle-warning c)))                   ")
	  (add-command-line   "                      ((equalp fmsg \"~~A also exports the following symbols:~~%  ~~S\")    ")
	  (add-command-line   "                       (format *error-output*                                               ")
	  (add-command-line   "                               \"~~&;;; Noticed ~~4D exported symbols in ~~A package.~~%\"  ")
	  (add-command-line   "                               (length (second fargs)) (first fargs))                       ")
	  (add-command-line   "                       (invoke-restart (find-restart 'muffle-warning c)))                   ")
	  (add-command-line   "                      ((equalp fmsg \"Redefining rule ~~A from ~~S to ~~S\")                ")
	  (add-command-line   "                       (format *error-output*                                               ")
	  (add-command-line   "                               \"~~&;;; Noticed redefined parser rule: ~~A.~~%\"            ")               
	  (add-command-line   "                               (first fargs))                                               ")
	  (add-command-line   "                       (invoke-restart (find-restart 'muffle-warning c)))                   ")
	  (add-command-line   "                      )))))                                                                 "))
	(dolist (file files-to-load) 
	  (add-command-line   "  (load ~S)                                   " file))
	(when (not *verbose*)
	  (add-command-line   "  )"))
	(add-command-line     "(extensions::save-lisp ~S :purify t)          " app-file)
	(add-command-line     "")
	(when *verbose*
	  (format t "========================================================~%"))))
    ;;
    (let ((process nil))
      (when *verbose*
	(format t "~&~%Output from the lower process being created:~%")
	(format t "~&========================================================~%"))
      (unwind-protect 
	  (setq process (cl::run-program base-lisp '() 
					 :wait   t 
					 :input  "/tmp/cmds" 
					 :output t ; (if *verbose* t nil)
					 :error  t))
	(if (null process)
	    (error "Problem creating lower process: ~A" base-lisp)
	  (let ((rc (cl::process-exit-code process)))
	    (when *verbose*
	      (format t "~&========================================================~%"))
	    (cond ((= rc 0)
		   (when *verbose*
		     (format t "~&~%;;; Success saving ~A~%" app-file)
		     (format t "~&;;; Invoke as:~%")
		     (format t "~&~% cmucl -core ~A~%~%" app-file)))
		  (t
		   (error "Problem: Return code = ~D when saving ~A" rc app-file)))
	    (cl::process-close process)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 SBCL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+sbcl
(defun save-this-sbcl-image (name)
  ;; Save this image.
  ;; (set-gc-parameters-for-use nil)
  (sb-ext::save-lisp-and-die name)) ; :purify nil

#+sbcl
(defun generate-new-sbcl-application (base-lisp name dir files-to-load files-to-copy &key executable?)
  ;; Build a fresh image with desired properties.
  ;; (This should be a completely new image, not simply a clone of this image!)
  ;; See http://cvs2.cons.org/ftp-area/sbcl/doc/sbcl-user/extensions.html#toc43
  ;; The :purify option compacts current data and makes GC skip it in resulting image.
  (let ((app-file (format nil "~a~a" dir name)
	 ;(sb-ext:native-namestring 
;	  (let ((n (position #\. name)))
;	    (if (null n)
;		(make-pathname :directory dir :name name)
;	      ;; if there are two dots, who knows what to do??
;	      (make-pathname :directory dir 
;			     :name (subseq name 0 n)  
;			     :type (subseq name (+ n 1) nil)))))
          )
        (dir-path (sb-ext:parse-native-namestring dir))
        (tmp-command-file #+win32 (format nil "~a\\cmd" (sb-ext::posix-getenv "TEMP"))
                          #-win32 "/tmp/cmd"))
    (ensure-directories-exist app-file)
    (dolist (file files-to-copy) 
      (let ((file-path (sb-ext:parse-native-namestring file)))
        (generic-copy-file file (make-pathname :name (pathname-name file-path)
                                               :type (pathname-type file-path)
                                               :defaults dir-path))))
    (when (probe-file app-file)
      (format t "~&Deleting old app file: ~S~%" app-file)
      (delete-file app-file))
    (with-open-file (s tmp-command-file :direction :output :if-exists :supersede)
      (format t "~%Commands to be used in lower process ~A to create~%  ~A~%" base-lisp app-file)
      (format t "========================================================~%")
      (format t "(format t \"argv= ~~S~~%\" *POSIX-ARGV*)~%")
      (format s "(format t \"argv= ~~S~~%\" *POSIX-ARGV*)~%")
      ;;(format t "(setq sb-ext:*gc-verbose* nil)~%")
      ;;(format s "(setq sb-ext:*gc-verbose* nil)~%")
      ;;(format t "(setq sb-ext:*bytes-consed-between-gcs* 20000000)~%")
      ;;(format s "(setq sb-ext:*bytes-consed-between-gcs* 20000000)~%")
      (let ((x '(defpackage "SB-BSD-SOCKETS" (:use "COMMON-LISP"))))
	(format t "~&~S~%" x)
	(format s "~&~S~%" x))
      (dolist (file files-to-load) 
	(format t "~&(progn (format t \"~~%;; Loading ~A~~%\")" file)
	(format t "~& (load ~S)~%" file)
	(format t "~& (room t))~2%")
	(format s "~&(progn (format t \"~~%;; Loading ~A~~%\")" file)
	(format s "~& (load ~S)~%" file)
	(format s "~& (room t))~2%"))
      (format t "(sb-ext::save-lisp-and-die ~S :purify nil :executable ~S)~%" app-file executable?)
      (format s "(sb-ext::save-lisp-and-die ~S :purify nil :executable ~S)~%" app-file executable?)
      (format s "~%")
      (format t "========================================================~%"))
    (let ((process nil))
      (format t "~&~%Output from the lower process being created:~%")
      (format t "~&========================================================~%")
      (unwind-protect 
	  (setq process (sb-ext:run-program base-lisp 
					    '("--dynamic-space-size 800 --end-runtime-options") ; must be one string, not three (I don't know why...)
					    :wait   t 
					    :input  tmp-command-file
					    :output t 
					    :error  :output))
	(if (null process)
	    (error "Problem creating lower process: ~A" base-lisp)
	  (let ((rc (sb-ext:process-exit-code process)))
	    (format t "~&========================================================~%")
	    (cond ((= rc 0)
		   (format t "~&~%Success saving ~A~%" app-file)
		   (format t "~&Invoke as:")
		   (format t "~& ~A~%~%" app-file))
		  (t
		   (format t "~&Problem: Return code = ~D when saving ~A~%~%" rc app-file)))
	    (sb-ext:process-close process)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                 OpenMCL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+mcl
(defun save-this-mcl-image (name)
  (format t "Saving ~a~%" name)
  (user::set-gc-parameters-for-use nil)
  ;(unless (probe-file name) (create-file  name))  ; temporary bug workaround (??)
  (ccl:save-application name))

#+mcl
(defun generate-new-mcl-application (base-lisp name dir files-to-load files-to-copy)
  ;; Build a fresh image with desired properties.
  ;; (This should be a completely new image, not simply a clone of this image!)
  (let ((app-file (namestring (make-pathname :directory dir :name name))))
    ;;
    (ensure-directories-exist app-file)
    (unless (probe-file app-file) (create-file app-file)) ; temporary bug workaround (??)
    (dolist (file files-to-copy) 
      (copy-file file (make-pathname :directory dir :defaults file)))
    ;;
    ;; we build a script file that looks something like this, 
    ;; and then run it in an inferior lisp:
    ;; ------------------------------------------------------
    ;; (load "aaa")
    ;; ...
    ;; (load "zzz")
    ;; (ccl::save-application "foo")
    ;; 
    ;; ------------------------------------------------------
    (with-open-file (s "/tmp/cmds" :direction :output :if-exists :supersede)
      (flet ((add-command-line (msg &rest args)
	       (let ((str (apply #'format nil msg args)))
		 (when *verbose*
		   (format t "~A~%" str))
		 (format s "~A~%" str))))
	(when *verbose*
	  (format t "~%Commands to be used in lower process ~A to create~%  ~A~%" base-lisp app-file)
	  (format t "========================================================~%"))
	(dolist (file files-to-load) 
	  (add-command-line "(load ~S)" file))
	(add-command-line "(ccl::save-application ~S)" app-file)
	(add-command-line "")
	(when *verbose*
	  (format t "========================================================~%"))))
    ;;
    (let ((process nil))
      (when *verbose*
	(format t "~&~%Output from the lower process being created:~%")
	(format t "~&========================================================~%"))
      (unwind-protect 
	  (setq process (cl::run-program base-lisp '() 
					 :wait   t 
					 :input  "/tmp/cmds" 
					 :output (if *verbose* t nil)
					 :error  t))
	(if (null process)
	    (error "Problem creating lower process: ~A" base-lisp)
	  (let ((rc (cl::process-exit-code process)))
	    (when *verbose*
	      (format t "~&========================================================~%"))
	    (cond ((= rc 0)
		   (when *verbose*
		     (format t "~&~%Success saving ~A~%" app-file)
		     (format t "~&;;; Invoke as:~%")
		     (format t "~&~% cmucl -core ~A~%~%" app-file)))
		  (t
		   (error "Return code = ~D when saving ~A" rc app-file)))
	    ;; (cl::process-close process) ;; fn doesn't exist
	    ))))))
  
#+Allegro (provide "save-image")
