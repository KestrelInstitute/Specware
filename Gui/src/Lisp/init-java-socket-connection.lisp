;;;-------------------------------------------------------------------------
;;;               Copyright (C) 2003 by Kestrel Technology
;;;                          All Rights Reserved
;;;-------------------------------------------------------------------------

(in-package :cl-user)


(defun print-result (arg)
  (format t "~% Connection to Java ~A" arg)
  t)

(defun kill-some-processes ()
  (dolist (p sys:*all-processes*)
    (when (y-or-n-p "Kill ~a (y or n)" (mp:process-name p))
      (mp:process-kill p)))
  (values))

(defvar *java-listener-name* "Java Listener")
(defvar *end-method-string* "--end--arguments--")

(defun java-listener-running-p ()
  (loop for process in sys::*all-processes* 
      for name = (mp::process-name process)
      if (search *java-listener-name* name)
      do (return t)
      finally (return nil)))

(defvar *java-socket*)
(defvar *java-socket-stream*)

(defun init-java-listener ()
  (mp:process-run-function *java-listener-name* 'java-listener))

(defun java-listener ()
  (setq *java-socket* (socket:make-socket :connect :passive :local-port 4323))
  (setq *java-socket-stream* (socket:accept-connection *java-socket*))
  (loop while (open-stream-p *java-socket-stream*)
	   do ;;(socket::wait-for-input *java-socket-stream*)
	      ;;(when (listen *java-socket-stream*)
	      ;; read will wait for stream
		(let ((form (read *java-socket-stream* nil :end)))
		  (if (eq form :end)
		      (return)
		    (ignore-errors (eval form)))));)
  (close *java-socket-stream*)
  ;; close socket
  (close *java-socket*)
  )

#| for testing purposes make a lisp server
(setq *java-socket* (socket:make-socket :connect :active :remote-port 4323))
(defun output-to-java-socket (str)
  (format *java-socket* "(format t \"~a~%\")" str)
  (force-output *java-socket*))
(defun read-method-call-from-java-socket ()
  (let ((methodName (read-line *java-socket*))
	(numArgs (read *java-socket*)))
    (cons methodName
	  (loop for i from 1 to numArgs
                collect (read-line *java-socket*))))
|#

(defun jstatic (method cl &rest args)
  ;; for the moment the class is assumed
  (declare (ignore cl))
  (format *java-socket-stream* "~a~%" method)
  (format *java-socket-stream* "~a~%" (length args))
  (loop for arg in args
         do (format *java-socket-stream* "~a~%" arg))
  (force-output *java-socket-stream*))

(defvar *current-path-name*)

(defun process-unit (path-name file-name)
  (format t "~%PATH NAME ~S ~%FILE NAME ~S" path-name file-name)
  (setq *current-path-name* path-name)
  (let* ((full-file-name (namestring (pathname (concatenate 'string path-name "/" file-name))))
	 (file-name-uri (concatenate 'string "/Gui/src/" file-name))
	 (full-path-name (cl-user::path-namestring full-file-name)))
    (format t "~% FULL FILE NAME ~S  ~% URI ~S ~% PATH-NAME ~S "
	    full-file-name file-name-uri full-path-name)
    (format t "~% CURRENT DIRECTORY ~S" (excl::current-directory))
    (specware::change-directory  full-path-name)
    (setq *default-pathname-defaults* (excl::current-directory))
    (specware-process-unit file-name-uri)
    (format t "~%~% FINISHED")))

(defun specware-process-unit (file-name)
  (format t "~% PROCESSING FILE ~S" file-name)
  (let ((output-str (with-output-to-string (str)
		      (let ((*standard-output* str))
			(Specware::evaluateURI_fromJava  file-name)))))
    (jstatic "setProcessUnitResults" "edu.kestrel.netbeans.lisp.LispProcessManager" output-str)))

(defun generate-lisp (path-name file-name)
  (format t "~%PATH NAME ~S ~%FILE NAME ~S" path-name file-name)
  (let* ((full-file-name (namestring (pathname (concatenate 'string path-name "/" file-name))))
	 (file-name-uri (concatenate 'string "/Gui/src/" file-name))
	 (full-path-name (cl-user::path-namestring full-file-name)))
    (format t "~% FULL FILE NAME ~S  ~% URI ~S ~% PATH-NAME ~S "
	    full-file-name file-name-uri full-path-name)
    (format t "~% CURRENT DIRECTORY ~S" (excl::current-directory))
    (specware::change-directory  full-path-name)
    (setq *default-pathname-defaults* (excl::current-directory))

    (format t "~% GENERATING LISP FOR ~S" file-name-uri)
    (let ((output-str (with-output-to-string (str)
		      (let ((*standard-output* str))
			(cl-user::swl file-name-uri)))))
    (jstatic "setGenerateLispResults" "edu.kestrel.netbeans.lisp.LispProcessManager"
	     path-name file-name output-str))

    (format t "~%~% FINISHED")))

(defun generate-java (path-name file-name)
  (format t "~%PATH NAME ~S ~%FILE NAME ~S" path-name file-name)
  (let* ((full-file-name (namestring (pathname (concatenate 'string path-name "/" file-name))))
	 (file-name-uri (concatenate 'string "/Gui/src/" file-name))
	 (full-path-name (cl-user::path-namestring full-file-name)))
    (format t "~% FULL FILE NAME ~S  ~% URI ~S ~% PATH-NAME ~S "
	    full-file-name file-name-uri full-path-name)
    (format t "~% CURRENT DIRECTORY ~S" (excl::current-directory))
    (specware::change-directory  full-path-name)
    (setq *default-pathname-defaults* (excl::current-directory))

    (format t "~% GENERATING JAVA FOR ~S" file-name-uri)
    (let ((output-str (with-output-to-string (str)
		      (let ((*standard-output* str))
			(cl-user::swj file-name-uri)))))
    (jstatic "setGenerateJavaResults" "edu.kestrel.netbeans.lisp.LispProcessManager"
	     path-name file-name output-str))

    (format t "~%~% FINISHED")))

(defpackage "SPECWARE")
(defun Specware::reportErrorToJava (file line col msg)
  (let* ((filepath (parse-namestring file))
	 (name (pathname-name filepath))
	 (filedir (pathname-directory filepath))
	 (path (pathname-directory (parse-namestring (concatenate 'string
						       *current-path-name* "/"))))
	 (rel-path (remove-common-prefix path filedir))
	 (rel-dir (concat-with-dots rel-path)))
    (jstatic "setProcessUnitResults" "edu.kestrel.netbeans.lisp.LispProcessManager"
	     rel-dir name line col msg)))

(defun remove-common-prefix (p1 p2)
  (if (and (consp p1) (consp p2))
      (if (or (equal (car p1) (car p2))
              (and (member (car p1) '("Progra~1" "Program Files") :test 'equal)
                   (member (car p2) '("Progra~1" "Program Files") :test 'equal)))
	  (remove-common-prefix (cdr p1) (cdr p2))
        p2)
    p2))

(defun concat-with-dots (l)
  (if (null l) ""
    (if (null (cdr l))
	(car l)
      (format nil "~a.~a" (car l) (concat-with-dots (cdr l))))))
