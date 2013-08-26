;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(in-package :Parser4)

;;; ======================================================================
;;;  Parser interface
;;; ======================================================================

(defun Parse_SW_To_C_Pragma (string) 
  (let* ((*parser-source* (list :string string))
	 (session     (parse-sw-to-c-pragma-via-file string *sw-to-c-parser* *sw-to-c-tokenizer*))
	 (raw-results (parse-session-results session))
	 (error?      (or (parse-session-error-reported? session) 
			  (parse-session-gaps            session) 
			  (null raw-results))))
    (cond (error?
	   (cons :|Error| 
		 (format nil "Syntax error [~{~A~^, ~}] in explicit string.~%" 
			 (append (if (parse-session-error-reported? session) (list "explicit error(s)") nil)
				 (if (parse-session-gaps session) 
				     (let ((n (length (parse-session-gaps session)))) 
				       (list (format nil "~D gap~P" n n)))
				   nil)
				 (if (null raw-results) (list "no result") nil)))))

	  ;; revised per parseSpecwareFile above
	  ((null (rest raw-results))
	   (let* ((raw-result (first  raw-results))
		  (raw-data   (third  raw-result))  
		  (raw-form   (first  raw-data)))   ; why is raw-data is a 1-element list ?
	     (when-debugging
	      (when (or *verbose?* *show-results?*)
		(format t "~%---Parse_SW_To_C_Pragma pre-evaluation result---~%")
		(pprint raw-form)
		(format t "~%---~%")))
	     (let ((result (eval raw-form))) ; may refer to *parser-source*
	       (cons :|Some| result))))
	  (t
	   (cons :|Error|
		 (format nil "Syntax error: ~D top-level forms (as opposed to one term or one sequence of decls) in ~A~%"
			 (length raw-results)
			 string))))))


(defun parse-sw-to-c-pragma-via-file (string parser tokenizer) 
  (when (probe-file "/tmp/sw-to-c-spec") (delete-file "/tmp/sw-to-c-spec"))
  (with-open-file (s "/tmp/sw-to-c-spec" :direction :output :if-exists :new-version)
    (format s "~A" string))
  ;; parse-file is defined in /Library/Algorithms/Parsing/Chart/Handwritten/Lisp/parse-top.lisp
  (let ((*parser-source* (list :string string)))
    (parse-file "/tmp/sw-to-c-spec" parser tokenizer)))

