;;; -*- Mode: LISP; Package: Parser; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

(defun parse-file (file parser tokenizer &key package 
					      (report-gaps? t)
					      (report-ambiguities? t))

  (incf-timing-data 'before-parse-file)
  (unless (parser-p parser)
    (error "~S is not a parser" parser))
  (unless (or (functionp tokenizer) (fboundp tokenizer))
    (error "~S is not a tokenizer" tokenizer))
    
  ;; gc now while there is not much live data to collect, 
  ;; since a gc in the midst of the parse may need to move a lot of temp stuff 
  ;; -- we would like newspace to be fairly large -- check this?? --
  (when-debugging
   (setq *current-parser-session* nil)
   (reset-parser-debug-vars))
  (specware::gc) 
  ;;
  (incf-timing-data 'initial-gc)
  (let* ((package (or package 
		      (parser-symbol-package parser)
		      common-lisp::*package*))
	 (session (make-parse-session 
		   :file                 file
		   :parser               parser
		   :tokenizer            tokenizer
		   :package              package
		   :report-gaps?         report-gaps?
		   :report-ambiguities?  report-ambiguities?
		   :error-reported?      nil
		   )))
    (when-debugging 
     (setq *current-parser-session* session)
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
;;;	       (comment "Used parser ~A (~D rule~:P, package ~A)"
;;;			(parser-name parser)
;;;			(parser-total-rule-count parser)
;;;			(package-name package))
;;;	       (comment "~6D byte~:P in ~A" 
;;;			(with-open-file (s file) (file-length s))       
;;;			file)
;;;	       (comment "~6D raw tokens" number-of-raw-tokens)
;;;	       (comment "~6D non-comment token~:P" (1- (length locations)))
;;;	       (when comment-eof-error?
;;;		 (comment "     1 unterminated comment that runs to EOF"))
	       (comment "~6D resulting toplevel form~:P" n))))
      ;;
      session)))


