;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

;;; ======================================================================
;;;  Parser interface
;;; ======================================================================

(defvar *parse-file-name*)

(defun parseFile (*parse-file-name*)
  (let* ((session (parse-file *parse-file-name* *specware4-parser* *specware4-tokenizer* :report-gaps? nil))
	 (pres (parse-session-results session))
	 (error? (or (parse-session-error-reported? session) (parse-session-gaps session) (null pres))))
    (if error?  '(:|None|)
      (let ((res1 (third (car pres))))
	(when-debugging
	 (when (or *verbose?* *show-results?*)
	   (format t "~%---parseFile result---~%")
	   (pprint res1)
	   (format t "~%---~%")))
	(let ((res2 (mapcar #'eval res1)))
					; (when (null res2)
					; (format t "~%---~%")
					; (format t "~&;;; Note: ~A was legal, but vacuous.~%" *parse-file-name*))
	  (cons :|Some| (car res2)))))))

(defun parseFileMsg (fileName) 
  (let* ((session (parse-file fileName *specware4-parser* *specware4-tokenizer* :report-gaps? nil))
	 (pres (parse-session-results session))
	 (error? (or (parse-session-error-reported? session) (parse-session-gaps session) (null pres))))
    (if error? (cons :|Error| 
		     (let (
			   (msg (format nil "Syntax error [~{~A~^, ~}] in ~S ~%" 
					(append (if (parse-session-error-reported? session) (list "explicit error(s)") nil)
						(if (parse-session-gaps session) 
						    (let ((n (length (parse-session-gaps session)))) 
						      (list (format nil "~D gap~P" n n)))
						  nil)
						(if (null pres) (list "no result") nil))
					fileName)))
		       msg))
      (let ((res1 (third (car pres))))
	(when-debugging
	 (when (or *verbose?* *show-results?*)
	   (format t "~%---parseFileMsg result---~%")
	   (pprint res1)
	   (format t "~%---~%")))
	(let ((res2 (mapcar #'eval res1)))
	  (when (null res2)
	    (format t "~%---~%")
	    (format t "~&;;; Note: ~A was legal, but vacuous.~%" fileName))
	  (cons :|Ok| (cadr res2)))))))

;; Mock string parser based on printing to /tmp, and then parsing.

(defun parse-string (string parser tokenizer) 
  (with-open-file (s "/tmp/string-spec" :direction :output :if-exists :new-version)
    (format s string))
  (parse-file "/tmp/string-spec" parser tokenizer))

(defun parseString (string) 
  (let* ((session (parse-string string *specware4-parser* *specware4-tokenizer*))
	 (pres	  (parse-session-results session))
	 (error?  (or (parse-session-error-reported? session) (parse-session-gaps session) (null pres))))
    (if error?
	(cons :|Error| (format nil "Syntax error [~{~A~^, ~}] in explicit string.~%" 
			       (append (if (parse-session-error-reported? session) (list "explicit error(s)") nil)
				       (if (parse-session-gaps session) 
					   (let ((n (length (parse-session-gaps session)))) 
					     (list (format nil "~D gap~P" n n)))
					 nil)
				       (if (null pres) (list "no result") nil))))
      (let* ((res1 (third (car pres))))
	(when-debugging
	 (when (or *verbose?* *show-results?*)
	   (format t "~%---parseString result---~%")
	   (pprint res1)
	   (format t "~%---~%")))
	(let ((res2 res1))		; no eval here
	  (cons :|Ok| res2))))))


    

