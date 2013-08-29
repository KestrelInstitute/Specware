;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(defpackage :LM (:use :COMMON-LISP-USER))
(in-package :Parser4)

;;; ======================================================================
;;;  Parser interface
;;; ======================================================================

(defun LM::parseLanguageMorphism (string) 
  (let* ((*parser-source* (list :string string))
	 (session         (parse-language-morphism-via-file string))
	 (raw-results     (parse-session-results session))
	 (error?          (or (parse-session-error-reported? session) 
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

	  ((null (rest raw-results))
	   (let* ((raw-result (first  raw-results))
		  (raw-data   (third  raw-result))  
		  (raw-form   (first  raw-data)))   ; why is raw-data a 1-element list ?
	     (when-debugging
	      (when (or *verbose?* *show-results?*)
		(format t "~%---Parse_LanguageMorphism pre-evaluation result---~%")
		(pprint raw-form)
		(format t "~%---~%")))
	     (let ((result (eval raw-form))) ; may refer to *parser-source*
	       (cons :|Parsed| result))))
	  (t
	   (cons :|Error|
		 (format nil "Syntax error: ~D top-level forms (as opposed to one term or one sequence of decls) in ~A~%"
			 (length raw-results)
			 string))))))

(defun parse-language-morphism-via-file (string)
  (let ((temp-file "/tmp/language-morphism"))

    (when (probe-file temp-file) (delete-file temp-file)) ;; shouldn't be necessary, but...
    (with-open-file (s temp-file :direction :output :if-exists :new-version)
      (format s "~A" string))

    ;; parse-file is defined in /Library/Algorithms/Parsing/Chart/Handwritten/Lisp/parse-top.lisp
    (let ((*parser-source* (list :string string)))
      (parse-file temp-file  *lm-parser* *lm-tokenizer*))))

