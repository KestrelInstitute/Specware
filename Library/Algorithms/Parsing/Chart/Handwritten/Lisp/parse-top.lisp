;;; -*- Mode: LISP; Package: Parser; Base: 10; Syntax: Common-Lisp -*-

(in-package :Parser4)

(defun parse-file (file parser tokenizer &key package 
					      (report-gaps? t)
					      (report-ambiguities? t)
					      start-rule-name)
  (incf-timing-data 'before-parse-file)
  (unless (parser-p parser)
    (error "~S is not a parser" parser))
  (unless (or (functionp tokenizer) (fboundp tokenizer))
    (error "~S is not a tokenizer" tokenizer))
    
  ;; gc now while there is not much live data to collect, 
  ;; since a gc in the midst of the parse may need to move a lot of temp stuff 
  ;; -- we would like newspace to be fairly large -- check this?? --
  (setq *current-parser-session* nil)
  (when-debugging
   (reset-parser-debug-vars))
  ;; call garbageCollect if it looks plausible
  (let ((gc (find-symbol #+casesensitive "garbageCollect"
                         #-casesensitive "GARBAGECOLLECT"
                         #+casesensitive "System-Spec"
                         #-casesensitive "SYSTEM-SPEC")))
    (when (fboundp gc)
      (funcall gc nil)))
  ;;
  (incf-timing-data 'initial-gc)
  (let* ((package (or package 
		      (parser-symbol-package parser)
		      common-lisp::*package*))
	 (start-rule (if start-rule-name
			 (gethash start-rule-name (parser-ht-name-to-rule parser))
		       (parser-toplevel-rule parser)))
	 ;; start-rule could be nil, so be careful! (see below)
	 (session (make-parse-session 
		   :file                 file
		   :parser               parser
		   :tokenizer            tokenizer
		   :package              package
		   :report-gaps?         report-gaps?
		   :report-ambiguities?  report-ambiguities?
		   :error-reported?      nil
		   :start-rule           start-rule ; possibly nil here!
		   )))
    (setq *current-parser-session* session)
    (when-debugging 
     (reset-parser-debug-vars))
    ;;
    (multiple-value-bind (locations number-of-raw-tokens comment-eof-error?) 
	(tokenize-file session file tokenizer)
      (declare (ignore comment-eof-error?))
      ;;
      (setf (parse-session-locations session) locations)
      ;;
      (when *verbose?*
	(comment "Using  parser ~A (~6D rule~:P, package ~A)"
		 (parser-name parser)
		 (parser-total-rule-count parser)
		 (package-name package))
	(comment "~6D byte~:P in ~A" 
		 (with-open-file (s file) (file-length s))       
		 file)
	(comment "~6D raw tokens" number-of-raw-tokens)
	(comment "~6D non-comment token~:P" (1- (length locations)))
	)
      ;;
      (incf-timing-data 'before-attach-rules)
      (cond ((null start-rule)
             ;; could do this sooner, above, but waiting until here might provide more information when debugging...
             (comment "Explicit start-rule does not exist in gramamr: ~A." start-rule-name)
             (setf (parse-session-error-reported? session) t))
            (t
             (parser-attach-rules session)
             (incf-timing-data 'attach-rules)
             (parser-get-values   session)
             (incf-timing-data 'get-values)
             ;;
             (let ((n (length (parse-session-results session))))
        	(cond (*verbose?* 
              	       (comment "~6D resulting toplevel form~:P" n))
              	      ;; ((not (= n 1))
              	      ((> n 1)
	               ;; (comment "Used parser ~A (~D rule~:P, package ~A)"
		       ;; 	(parser-name parser)
		       ;; 	(parser-total-rule-count parser)
		       ;; 	(package-name package))
	               ;; (comment "~6D byte~:P in ~A" 
		       ;; 	(with-open-file (s file) (file-length s))       
		       ;; 	file)
	               ;; (comment "~6D raw tokens" number-of-raw-tokens)
	               ;; (comment "~6D non-comment token~:P" (1- (length locations)))
	               ;; (when comment-eof-error?
		       ;;  (comment "     1 unterminated comment that runs to EOF"))
	               (comment "~6D resulting toplevel form~:P" n))))))
      ;;
      session)))


