(defpackage "XML")
(in-package "XML")

(defun XML::printXML (datum-and-table)
  (let* ((datum (car datum-and-table))
	 (table (cdr datum-and-table)))
    (let ((doc (generate_Document datum table)))
      (print_Document_to_String doc))))

;;;; ;;; ------------------------------------------------------------------------
;;;; 
;;;; (defconstant null-whitespace '())
;;;; 
;;;; (defun indentation-chardata (n)
;;;;   (cons :|Some| (cons 10 (cons 10 (make-whitespace n)))))
;;;; 
;;;; (defun make-whitespace (n)
;;;;   (let ((chars nil))
;;;;     (dotimes (i n) (push 32 chars))
;;;;     chars))
;;;; 
;;;; ;;; ------------------------------------------------------------------------
;;;; 
;;;; (defun XML::printXML (datum-and-table)
;;;;   (let* ((datum (car datum-and-table))
;;;; 	 (table (cdr datum-and-table))
;;;; 	 (main-entry (first table))
;;;; 	 (main-sort  (car  main-entry))
;;;; 	 (main-qid   (cadr main-sort))
;;;; 	 (main-id    (cdr  main-qid)))
;;;;     (let ((doc (make_Document 
;;;; 		(list 
;;;; 		 xml::standard_XMLDecl_DocItem  ; first <?xml version="1.0"?>
;;;;                  (cons :|WhiteSpace| '(10 10))  ; then a couple of newlines
;;;; 		 ;;
;;;;                  ;; (cons :|DTD|  (make_DocTypeDecl ...)) ; TODO
;;;; 		 ;;
;;;;                  (cons :|WhiteSpace| '(10 10))  ; then a couple of newlines
;;;; 		 (make-content-item-from-full-element main-id 
;;;; 						      datum 
;;;; 						      main-sort 
;;;; 						      table
;;;; 						      0)
;;;; 		 ))))
;;;;       (print_Document_to_String doc))))
;;;; 
;;;; (defun chase (sort table)
;;;;   (labels ((aux (sort)
;;;; 	    (let ((expansion (cdr (assoc sort table :test 'equal))))
;;;; 	      (cond ((null expansion)                 sort)
;;;; 		    ((eq (car expansion) :|Base|)     (aux expansion))
;;;; 		    ((eq (car expansion) :|Subsort|)  (aux (cadr expansion)))
;;;; 		    ((eq (car expansion) :|Quotient|) (aux (cadr expansion)))
;;;; 		    (t                                expansion)))))
;;;;     (aux sort)))
;;;; 
;;;; (defun make-content-item-from-full-element (name datum sort table indent)
;;;;   (make_Content_Item_from_Element 
;;;;    (make-element name datum sort table (+ indent 2))))
;;;; 
;;;; (defun make-element (name datum sort table indent)
;;;;   (let* ((pattern (chase sort table))
;;;; 	 (name (unicode::ustring name))
;;;; 	 (sort-attribute  (make_GenericAttribute '(32) (unicode::ustring "type") '() '() 
;;;; 						 (make_QuotedText '34
;;;; 								  (pp-sort-for-xml-attribute sort))))
;;;; 	 (attributes 
;;;; 	  (list sort-attribute)))
;;;;     (multiple-value-bind (items text)
;;;; 	(make-content-items datum sort pattern table indent)
;;;;       (cond ((and (null items) (null text))
;;;; 	     (make_Empty_Element-1
;;;; 	      (make_EmptyElemETag name attributes null-whitespace)))
;;;; 	    (t
;;;; 	     (make_Full_Element
;;;; 	       (make_STag name attributes null-whitespace)
;;;; 	       (make_Content (cond ((null text)        (indentation-chardata indent))
;;;; 				   ((eq text :|None|) :|None|)
;;;; 				   (t                  (cons :|Some| 
;;;; 							     (append (cons 10 (make-whitespace indent))
;;;; 								     text 
;;;; 								     (cons 10 (make-whitespace (- indent 2)))))))
;;;; 			     
;;;; 			     items)
;;;; 	       (make_ETag name null-whitespace)))))))
;;;; 
;;;; (defun pp-sort-for-xml-attribute (sort)
;;;;   (labels ((aux (sort)
;;;; 		(case (car sort)
;;;; 		  (:|Base|
;;;; 		     (let* ((qid (cadr sort))
;;;; 			    (arg (caddr sort))
;;;; 			    (qualifier (car qid))
;;;; 			    (id        (cdr qid)))
;;;; 		       (if (null arg)
;;;; 			   (format nil "~A.~A" qualifier id)
;;;; 			 (format nil "~A.~A ~A" qualifier id (aux arg)))))
;;;; 		  (t
;;;; 		   (format nil "[COMPOUND SORT: ~S]" sort)))))
;;;;     (unicode::ustring (aux sort))))
;;;; 
;;;; (defun make-content-items (datum sort pattern table indent)
;;;;   (let ((key  (car pattern))
;;;; 	(body (cdr pattern)))
;;;;     (case key
;;;; 
;;;;       (:|Product| 
;;;; 	 (cond ((consp datum)
;;;; 		;; datum is a cons [1 . 2] -- use entry names as tags
;;;; 		(list
;;;; 		 (let ((pattern (first body)))
;;;; 		   (cons (make-content-item-from-full-element (car pattern) (car datum) (cdr pattern) table indent)
;;;; 			 (indentation-chardata indent)))
;;;; 		 (let ((pattern (second body)))
;;;; 		   (cons (make-content-item-from-full-element (car pattern) (cdr datum) (cdr pattern) table indent)
;;;; 			 (indentation-chardata (- indent 2))))))
;;;; 	       (t
;;;; 		;; datum is a vector -- use entry names as tags
;;;; 		(let ((items nil)
;;;; 		      (n (length datum)))
;;;; 		  (dotimes (i n (reverse items))
;;;; 		    (let* ((item (svref datum i))
;;;; 			   (pattern (pop body))
;;;; 			   (field-name (car pattern))
;;;; 			   (field-type (cdr pattern)))
;;;; 		      (push  
;;;; 		       (cons (make-content-item-from-full-element field-name item field-type table indent)
;;;; 			     (if (= (+ i 1) n)
;;;; 				 (indentation-chardata (- indent 2))
;;;; 			       (indentation-chardata indent)))
;;;; 		       items)))))))
;;;; 
;;;;       (:|CoProduct| 
;;;; 	 ;; datum is a pair
;;;; 	 ;; dispatch on key to get entry 
;;;; 	 (let* ((constructor (symbol-name (car datum)))
;;;; 		(value       (cdr datum))
;;;; 		(pair        (assoc constructor body :test 'equal)))
;;;; 	   (if (null pair)
;;;; 	       ;; ??
;;;; 	       nil
;;;; 	     (cond ((and (equal constructor "Some") 
;;;; 			 (= (length body) 2)
;;;; 			 (assoc "None" body :test 'equal))
;;;; 		    (make-content-items (cdr datum)
;;;; 					sort
;;;; 					(chase (cdr pair) table)
;;;; 					table 
;;;; 					indent))
;;;; 		   ((and (equal constructor "None") 
;;;; 			 (= (length body) 2)
;;;; 			 (assoc "Some" body :test 'equal))
;;;; 		    nil)
;;;; 		   (t
;;;; 		    (list 
;;;; 		     (cons (make-content-item-from-full-element constructor value (cdr pair) table indent)
;;;; 			   (indentation-chardata indent))))))))
;;;;       
;;;;       (:|Base|
;;;; 	 (let ((qid (car body)))
;;;; 	   (cond ((equal qid '("String" . "String"))
;;;; 		  (unless (stringp datum)
;;;; 		    (warn "Expected string: ~S" datum))
;;;; 		  (values () 
;;;; 			  (unicode::ustring (format nil "~S" datum))))
;;;; 
;;;; 		 ((equal qid '("Integer" . "Integer"))
;;;; 		  (unless (numberp datum)
;;;; 		    (warn "Expected number: ~S" datum))
;;;; 		  (values ()
;;;; 			  (unicode::ustring (format nil "~D" datum))))
;;;; 
;;;; 		 ((equal qid '("List" . "List"))
;;;; 		  (unless (consp datum)
;;;; 		    (warn "Expected list: ~S" datum))
;;;; 		  (let ((new-element (chase (cadr body) table)))
;;;; 		    (if (equal new-element (cadr body))
;;;; 			(values ()
;;;; 				(unicode::ustring (format nil "~D" datum)))
;;;; 		      (make-content-items datum 
;;;; 					  sort
;;;; 					  (list :|Base| qid new-element)
;;;; 					  table 
;;;; 					  indent))))
;;;; 
;;;; 		 ((equal qid '("Option" . "Option"))
;;;; 		  (if (eq (car datum) :|None|)
;;;; 		      (values '()
;;;; 			      :|None|)
;;;; 		    (progn 
;;;; 		      (make-content-items (cdr datum) 
;;;; 					  sort
;;;; 					  (chase (cadr body) table)
;;;; 					  table 
;;;; 					  indent))))
;;;; 		 (t
;;;; 		  (values ()
;;;; 			  (unicode::ustring (format nil "?? Base: ~A.~A ??" (car qid) (cdr qid))))))))
;;;; 
;;;;       (t
;;;;        (values ()
;;;; 	       (unicode::ustring (format nil "?? Key: ~A ??" key)))))))
;;;; 
;;;; ;;; ------------------------------------------------------------------------
;;;; 
;;;; (defun show_sort (msg srt)
;;;;   (format t "~%~A : ~S~%" msg srt))

