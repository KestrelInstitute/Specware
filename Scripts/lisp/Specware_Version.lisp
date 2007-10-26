(in-package "USER")

;;; ============ File Processing Utilities ============

(defun fix-dir (dir)
  (let ((dir (substitute #\/ #\\ dir)))
    (if (eq (schar dir (1- (length dir))) #\/)
	dir
      (concatenate 'string dir "/"))))
(defun fix-dir (dir)
  (let ((dir (substitute #\/ #\\ dir)))
    (if (eq (schar dir (1- (length dir))) #\/)
	dir
      (concatenate 'string dir "/"))))
    
;;; ============ Parameters ============

(defparameter *Specware-Dir*               (fix-dir (sys:getenv "SPECWARE4")))

(defparameter *Specware-Name*              "Specware4") ; Name of dir and startup files

(defparameter *Specware-Major-Version*     4)
(defparameter *Specware-Minor-Version*     2)
(defparameter *Specware-Patch-Level*       4)

(defparameter *Specware-Version-Dotted*    (format nil "~D.~D.~D" *Specware-Major-Version* *Specware-Minor-Version* *Specware-Patch-Level*))
(defparameter *Specware-Version-Dashed*    (format nil "~D-~D-~D" *Specware-Major-Version* *Specware-Minor-Version* *Specware-Patch-Level*))

(defparameter *Specware-Version-Name*      (format nil "Specware-~D-~D"    *Specware-Major-Version* *Specware-Minor-Version*))
(defparameter *Specware-Full-Version-Name* (format nil "Specware-~A" *Specware-Version-Dashed*))

(defun show-specware-version ()
  (format t "~&--------------------------------------------------------------------------------~%")
  (format t "~&*Specware-Dir*               = ~S~%" *Specware-Dir*)
  (format t "~&*Specware-Name*              = ~S~%" *Specware-Name*)
  (format t "~&*Specware-Major-Version*     = ~S~%" *Specware-Major-Version*)
  (format t "~&*Specware-Minor-Version*     = ~S~%" *Specware-Minor-Version*)
  (format t "~&*Specware-Patch-Level*       = ~S~%" *Specware-Patch-Level*)
  (format t "~&*Specware-Version-Dotted*    = ~S~%" *Specware-Version-Dotted*)
  (format t "~&*Specware-Version-Dashed*    = ~S~%" *Specware-Version-Dashed*)

  (format t "~&*Specware-Version-Name*      = ~S~%" *Specware-Version-Name*)
  (format t "~&*Specware-Full-Version-Name* = ~S~%" *Specware-Full-Version-Name*)
  (format t "~&--------------------------------------------------------------------------------~%")
  )

(show-specware-version)

