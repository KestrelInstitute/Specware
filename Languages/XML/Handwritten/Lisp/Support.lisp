(defpackage "XML")
(in-package "XML")

(defun printXML (datum-and-table)
  (let* ((datum (car datum-and-table))
	 (table (cdr datum-and-table)))
    (let ((doc (generate_Document-2 datum table)))
      (print_Document_to_String doc))))

(defun internalize_Document-2 (document table)
  (let* ((optional-sd (caar table))
	 (sd (caddr optional-sd)))
    (aux_internalize_Document-3 document sd table)))

