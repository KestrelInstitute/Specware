(defpackage "XML")
(in-package "XML")

;;; input

(defun readXMLFile (filename table)
  (let ((possible-document (read_document_from_file filename)))
    (if (eq (car possible-document) :|Some|)
	(internalize_Document-2 (cdr possible-document) table)
      :|None|)))

(defun parseXML (string-and-table)
  (let ((string (car string-and-table))
	(table  (cdr string-and-table)))
    (let ((possible-document (read_document_from_string string)))
      (if (eq (car possible-document) :|Some|)
	  (internalize_Document-2 (cdr possible-document) table)
	:|None|))))

(defun parseUnicodeXML (string-and-table)
  (let ((string (car string-and-table))
	(table  (cdr string-and-table)))
    (let ((possible-document (read_document_from_ustring string)))
      (if (eq (car possible-document) :|Some|)
	  (internalize_Document-2 (cdr possible-document) table)
	:|None|))))

(defun internalize_Document-2 (document table)
  (let* ((sd (caar table))
	 (desired-sd (if (and (eq (car sd) :|Base|)
			      (equal (cadr sd) '("Option" . "Option")))
			 (caddr sd)
		       sd)))
    (aux_internalize_Document-3 document desired-sd table)))

;;; output 

(defun writeXMLFile-2 (datum-and-filename table)
  (let ((datum    (car datum-and-filename))
	(filename (cdr datum-and-filename)))
    (let ((doc (generate_Document-2 datum table)))
      (print_Document_to_file-2 doc filename))))

(defun printXML (datum-and-table)
  (let ((datum (car datum-and-table))
	(table (cdr datum-and-table)))
    (let ((doc (generate_Document-2 datum table)))
      (print_Document_to_String doc))))

(defun printUnicodeXML (datum-and-table)
  (let ((datum (car datum-and-table))
	(table (cdr datum-and-table)))
    (let ((doc (generate_Document-2 datum table)))
      (print_Document_to_UString doc))))

