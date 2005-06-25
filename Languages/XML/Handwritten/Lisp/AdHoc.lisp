(defpackage "XML")
(in-package "XML")

;;; Misc hooks that attempt to bypass metaslang types.
;;; The user may wish to redefine these to be cognizant of user-defined types.
;;; For example, this may succeed in reading and writing floats
;;; even though metaslang is unaware of them
;;;

(defun XML::WRITE_AD_HOC_STRING-2 (sort-descriptor datum)
  (declare (ignore sort-descriptor))
  (format nil "~S" datum))

(defun  XML::READ_AD_HOC_STRING-2 (sort-descriptor xml-element-content) 
  (declare (ignore sort-descriptor))
  (let (; (items   (car xml-element-content)) 
	(trailer (cdr xml-element-content))) 
    ;; Unicode.string is defined in /Library/IO/Unicode/UStringAsList.sw
    ;; which is compiled after this...
    (read-from-string (funcall 'unicode::|!string| (cdr trailer)))))

;;; InternalizeDocument.sw: 
;;;   op internalize_EmptyElemTag_ad_hoc : fa (X) EmptyElemTag * SortDescriptor (* * QIdDescriptor * (List SortDescriptor) * SortDescriptorExpansionTable *) -> Option X

(defun XML::internalize_EmptyElemTag_ad_hoc-2 (tag sort-descriptor)
  (declare (ignore tag sort-descriptor))
  '(:|None|))
