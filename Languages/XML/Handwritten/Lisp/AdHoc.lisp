(defpackage :XML)
(in-package :XML)

;;; Misc hooks that attempt to bypass metaslang types.
;;; The user may wish to redefine these to be cognizant of user-defined types.
;;; For example, this may succeed in reading and writing floats
;;; even though metaslang is unaware of them
;;;

(defun XML::WRITE_AD_HOC_STRING-2 (type-descriptor datum)
  (declare (ignore type-descriptor))
  (format nil "~S" datum))

(defun  XML::READ_AD_HOC_STRING-2 (type-descriptor xml-element-content) 
  (declare (ignore type-descriptor))
  (let (; (items   (car xml-element-content)) 
	(trailer (cdr xml-element-content))) 
    ;; Unicode.string is defined in /Library/IO/Unicode/UStringAsList.sw
    ;; which is compiled after this...
    (read-from-string (funcall 'Unicode::|!string| (cdr trailer)))))

;;; InternalizeDocument.sw: 
;;;   op internalize_EmptyElemTag_ad_hoc : fa (X) EmptyElemTag * TypeDescriptor (* * QIdDescriptor * (List TypeDescriptor) * TypeDescriptorExpansionTable *) -> Option X

(defun XML::internalize_EmptyElemTag_ad_hoc-2 (tag type-descriptor)
  (declare (ignore tag type-descriptor))
  '(:|None|))
