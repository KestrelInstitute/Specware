(defpackage "UNICODE")
(defpackage "XML")
(in-package "XML")

(defun show_sort (msg srt)
  (format t "~%~A : ~S~%" msg srt))

(defun read_unicode_chars_from_file (filename)
  (let ((eof (cons nil nil))
	(chars nil))
    (if (probe-file filename)
	(with-open-file (s filename :element-type 'unsigned-byte)
	  (do ((char (read-byte s nil eof) 
		     (read-byte s nil eof)))
	      ((eq char eof)
	       (cons :|Some| (reverse chars)))
	    (push char chars)))
      '(:|None|))))

(defun write_unicode_chars_to_file (bytes filename)
  (with-open-file (s filename :element-type 'unsigned-byte
		     :direction :output
		     :if-exists :supersede)
    (dolist (byte bytes)
      (write-byte byte s))))

(defun parseXML (filename pattern)
  (break "From ~A: ~% read ~S" 
	 filename
	 pattern))

(defconstant null-attributes '())
(defconstant null-whitespace '())
(defconstant null-chardata   '(:|None|))
(defconstant newline-chardata   (cons :|Some| (list 13))) ; avoid bootstrap issues by making list directly

(defun XML::printXML (datum-and-table)
  (let* ((datum (car datum-and-table))
	 (table (cdr datum-and-table))
	 (main-entry (first table))
	 (main-sort  (car  main-entry))
	 (main-qid   (cadr main-sort))
	 (main-id    (cdr  main-qid)))
    ;; (format t "~&--------------------------------------------------------------------------------~%")
    ;; (dolist (entry table)
    ;;   (print (car entry))
    ;;   (print (cdr entry))
    ;;   (format t "~&--------------------------------------------------------------------------------~%"))
    ;; (format t "~6%")
    (let* ((null-prolog (make_prolog '(:|None|) () '(:|None|)))
	   (doc (make_document null-prolog
			       (make-element main-id datum main-sort table)
			       ())))
      (print_Document_to_String-1 doc))))

(defun chase (sort table)
  (let ((expansion (cdr (assoc sort table :test 'equal))))
    (cond ((null expansion) 
	   sort)
	  ((eq (car expansion) :|Base|)
	   (chase expansion table))
	  ((eq (car expansion) :|Subsort|)
	   (chase (cadr expansion) table))
	  ((eq (car expansion) :|Quotient|)
	   (chase (cadr expansion) table))
	  (t
	   expansion))))

(defun make-element (name datum sort table)
  (let* ((pattern (chase sort table))
	 (name (unicode::ustring name))
	 (stag (make_STag name null-attributes null-whitespace))
	 (etag (make_ETag name null-whitespace)))
    (make_Element_as_Full stag
			  (make-content datum pattern table)
			  etag)))

(defun make-content (datum pattern table)
  (setq pattern (chase pattern table))
  (let ((key  (car pattern))
	(body (cdr pattern)))
    (case key
      (:|Product| 
	(cond ((consp datum)
	       ;; datum is a cons [1 . 2] -- use entry names as tags
	       (make_Content null-chardata
			     (list
			      (let ((pattern (first body)))
				(cons (make_Content_Item_as_Element
				       (make-element (car pattern) (car datum) (cdr pattern) table))
				      newline-chardata))
			      (let ((pattern (second body)))
				(cons (make_Content_Item_as_Element
				       (make-element (car pattern) (cdr datum) (cdr pattern) table))
				      newline-chardata))
			      )))
	      (t
	       ;; datum is a vector -- use entry names as tags
	       (let ((items nil))
		 (dotimes (i (length datum))
		   (let* ((item (svref datum i))
			  (pattern (pop body))
			  (field-name (car pattern))
			  (field-type (cdr pattern)))
		     (push  
		      (cons (make_Content_Item_as_Element 
			     (make-element field-name item field-type table))
			    newline-chardata)
		      items)))
		 (make_Content null-chardata
			       items)))))

      (:|CoProduct| 
	;; datum is a pair
	;; dispatch on key to get entry 
	(let ((constructor (car datum))
	      (value       (cdr datum)))
	  (make_Content null-chardata
			(dolist (entry pattern)
			  (when (equal constructor (car entry))
			    (return 
			      (list 
			       (cons (make_Content_Item_as_Element 
				      (make-element constructor value (cdr entry) table))
				     newline-chardata))))))))
      
      (:|Base|
	(let ((qid (car body)))
	  (cond ((equal qid '("String" . "String"))
		 (unless (stringp datum)
		   (warn "Expected string: ~S" datum))
		 (make_Content (cons :|Some| (unicode::ustring datum) )
			       ()))

		((equal qid '("Integer" . "Integer"))
		 (unless (numberp datum)
		   (warn "Expected number: ~S" datum))
		 (make_Content (cons :|Some| (unicode::ustring (format nil "~D" datum)))
			       ()))

		((equal qid '("Option" . "Option"))
		 (if (eq (car datum) :|None|)
		     (make_Content null-chardata ())
		   (make-content (cdr datum) (cadr body) table)))

		(t
		 ;; (print (list :unknown-base pattern))
		 (make_Content (cons :|Some| (unicode::ustring (format nil "?? Base: ~A.~A ??" (car qid) (cdr qid))))
			       ())))))

      (t
       (print (list :unknown pattern))
       (make_Content (cons :|Some| (unicode::ustring (format nil "?? Key: ~A ??" key)))
		     ())))))

