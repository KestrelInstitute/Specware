;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

;;; ======================================================================
;;;  Parser interface
;;; ======================================================================

;; parseFile                    => parse-file => <parser>
;; parseFileMsg                 => parse-file => <parser>
;; parseString  => parse-string => parse-file => <parser>
;;
;; parse-file is defined in /Library/Algorithms/Parsing/Chart/Handwritten/Lisp/parse-top.lisp

(defvar *parser-source* nil) ; used by make-pos in semantics.lisp

;; Called from $SPECWARE4/Languages/SpecCalculus/Parser/Parse.sw
(defun parseFile (fileName)
  (let* ((*parser-source* (list :file fileName))
	 (session (parse-file fileName *specware4-parser* *specware4-tokenizer* :report-gaps? nil))
	 (raw-results (parse-session-results session))
	 (error? (or (parse-session-error-reported? session) 
		     (parse-session-gaps            session) 
		     (null raw-results))))
    (cond (error?  
	   (when (null raw-results)
	     (format t "~&Syntax error: No term or decls in file ~A~%"
		     fileName))
	   '(:|None|))
	  ;; revised to fix Bug 001: "No error msg when processing files with multiple and un-named specs"
	  ((null (rest raw-results))
	   (let* ((raw-result (first  raw-results))
		  ; (start    (first  raw-result))  
		  ; (end      (second raw-result))  
		  (raw-data   (third  raw-result))  
		  (raw-form   (first  raw-data)))   ; why is raw-data is a 1-element list ?
	     (when-debugging
	      (when (or *verbose?* *show-results?*)
		(format t "~%---parseFile pre-evaluation result---~%")
		(pprint raw-form)
		(format t "~%---~%")))
	     (let ((result (eval raw-form)))
	       (cons :|Some| result))))
	  (t
	   (format t "~&Syntax error: ~D top-level forms (as opposed to one term or one sequence of decls) in ~A~%"
		   (length raw-results)
		   fileName)
	   '(:|None|)))))

;;; obsolete?
;;; (defun parseFileMsg (fileName) 
;;;   (let* ((*parser-source* (list :file fileName))
;;; 	 (session (parse-file fileName *specware4-parser* *specware4-tokenizer* :report-gaps? nil))
;;; 	 (pres (parse-session-results session))
;;; 	 (error? (or (parse-session-error-reported? session) (parse-session-gaps session) (null pres))))
;;;     (cond (error? 
;;; 	   (cons :|Error| 
;;; 		 (let ((msg (format nil "Syntax error [~{~A~^, ~}] in ~S ~%" 
;;; 				    (append (if (parse-session-error-reported? session) (list "explicit error(s)") nil)
;;; 					    (if (parse-session-gaps session) 
;;; 						(let ((n (length (parse-session-gaps session)))) 
;;; 						  (list (format nil "~D gap~P" n n)))
;;; 					      nil)
;;; 					    (if (null pres) (list "no result") nil))
;;; 				    fileName)))
;;; 		   msg)))
;;; 	  ((null (rest pres))
;;; 	   (let ((res1 (third (first pres))))
;;; 	     (when-debugging
;;; 	      (when (or *verbose?* *show-results?*)
;;; 		(format t "~%---parseFileMsg result---~%")
;;; 		(pprint res1)
;;; 		(format t "~%---~%")))
;;; 	     (let ((res2 (mapcar #'eval res1)))
;;; 	       ;; (when (null res2)
;;;  	       ;;   (format t "~%---~%")
;;; 	       ;;   (format t "~&;;; Note: ~A was legal, but vacuous.~%" fileName))
;;; 	       (cons :|Ok| (first res2))))) ; ?? was cadr ??
;;; 	  (t
;;; 	   (format t "~&Syntax error: There are ~D top-level terms in ~A.~%"
;;; 		   (length pres)
;;; 		   fileName)
;;; 	   '(:|None|)))))


;; parseString is not called by anything, but is handy for debugging...
(defun parseString (string) 
  (let* ((session     (parse-string string *specware4-parser* *specware4-tokenizer*))
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

	  ;; revised per parseFile above
	  ((null (rest raw-results))
	   (let* ((raw-result (first  raw-results))
		  ; (start    (first  raw-result))  
		  ; (end      (second raw-result))  
		  (raw-data   (third  raw-result))  
		  (raw-form   (first  raw-data)))   ; why is raw-data is a 1-element list ?
	     (when-debugging
	      (when (or *verbose?* *show-results?*)
		(format t "~%---parseFile pre-evaluation result---~%")
		(pprint raw-form)
		(format t "~%---~%")))
	     (let ((result (eval raw-form)))
	       (cons :|Some| result))))
	  (t
	   (cons :|Error|
		 (format nil "Syntax error: ~D top-level forms (as opposed to one term or one sequence of decls) in ~A~%"
			 (length raw-results)
			 string))))))

;; Mock string parser based on printing to /tmp, and then parsing.

(defun parse-string (string parser tokenizer) 
  (with-open-file (s "/tmp/string-spec" :direction :output :if-exists :new-version)
    (format s string))
  ;; parse-file is defined in /Library/Algorithms/Parsing/Chart/Handwritten/Lisp/parse-top.lisp
  (let ((*parser-source* (list :string string)))
    (parse-file "/tmp/string-spec" parser tokenizer)))

