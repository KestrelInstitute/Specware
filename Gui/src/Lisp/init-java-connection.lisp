;;;-------------------------------------------------------------------------
;;;               Copyright (C) 2003 by Kestrel Technology
;;;                          All Rights Reserved
;;;-------------------------------------------------------------------------

(in-package :user)


(eval-when (compile load)
  (require :jlinker)
  (require :jlinkent)
  (use-package :javatools.jlinker))

(defun print-result (arg)
  (format t "~% Connection to Java ~A" arg)
  t)

(defun kill-some-processes ()
  (dolist (p sys:*all-processes*)
    (when (y-or-n-p "Kill ~a (y or n)" (mp:process-name p))
      (mp:process-kill p)))
  (values))

(defun java-listener-running-p ()
  (loop for process in sys::*all-processes* 
      for name = (mp::process-name process)
      if (search  "LinkerListener" name)
      do (return t)
      finally (return nil)))

(defun init-java-listener () 
  (when (and (not (javatools.jlinker::jlinker-query))
	     (not (java-listener-running-p)))
    ;(excl::current-directory "planware:java-ui;")
    ;(excl::set-current-working-directory  "planware:java-ui;")
    ;(setq *default-pathname-defaults* "planware:java-ui;")
    (load (concatenate 'string specware::Specware4 "/Gui/src/Lisp/jl-config.cl")) 
    (jlinker-listen :process-function #'print-result
		    :init-args '(:lisp-file nil
				 :lisp-host "localhost"
				 :lisp-port 4321
				 :verbose t))))

(defun process-unit (path-name file-name)
  (format t "~%PATH NAME ~S ~%FILE NAME ~S" path-name file-name)
  (let* ((full-file-name (namestring (pathname (concatenate 'string path-name "/" file-name))))
	 (file-name-uri (concatenate 'string "/Gui/src/" file-name))
	 (full-path-name (user::path-namestring full-file-name)))
    (format t "~% FULL FILE NAME ~S  ~% URI ~S ~% PATH-NAME ~S " full-file-name file-name-uri full-path-name)
    (format t "~% CURRENT DIRECTORY ~S" (excl::current-directory))
    (excl::chdir  full-path-name)
    (setq *default-pathname-defaults* (excl::current-directory))
    (specware-process-unit file-name-uri)
    (format t "~%~% FINISHED")))

(defun specware-process-unit (file-name)
  (format t "~% PROCESSING FILE ~S" file-name)
  (let ((output-str (with-output-to-string (str)
		      (let ((*standard-output* str))
			(user::sw  file-name)))))
    (jcall (jmethod "LispProcessManager" "setProcessUnitResults") output-str)))


;(excl::chdir "planware:java-ui;")
;(init-java-listener)
