;;; Specware interface to opticl

(defpackage :Image (:use :cl))
(defpackage :Opticl (:use :cl))

(in-package :Image)

;;; op [p] readImageFile  (filename : FileName) : Option (Image p)
;;; op [p] writeImageFile (filename : FileName) (image : Image p) : ()  

(defun readImageFile (filename)
  (let* ((matrix (opticl::read-image-file filename))
         (etype  (array-element-type matrix)))
    (cond ((and (consp etype) (eq (car etype) 'unsigned-byte))
           (let ((n (cadr etype)))
             (cons :|Some| (mkImage-4 :|Bit| :|Nat| n matrix))))
          (t
           (list :|None|)))))

(defun writeImageFile-1-1 (filename image)
  (let ((matrix (svref image 0)))
    (opticl::write-image-file filename matrix)))
                 
