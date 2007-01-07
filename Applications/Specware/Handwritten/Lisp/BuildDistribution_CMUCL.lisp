;; This file builds a distribution directory for Linux/CMUCL Runtime Specware.

(defpackage :Specware)

(format t "~%;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")
(format t "~&About to build distribution dir for Specware under CMUCL on Linux.~%")
(format t "~&[This implements Step Linux-D in How_to_Create_a_Specware_CD.txt]~%")
(format t "~&;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")

;;; ============ UTILITIES ============

(defun fix-dir (dir)
  (let ((dir (substitute #\/ #\\ dir)))
    (if (eq (schar dir (1- (length dir))) #\/)
	dir
      (concatenate 'string dir "/"))))
    
(defun delete-file-if-present (file &optional msg)
  (when (probe-file file)
    (if (null msg)
	(format t "~&;;; Deleting file ~A~%" file)
      (format t "~&;;; ~A~%" msg))

    (delete-file file)))

(defun delete-dir-if-present (dir &optional msg)
  (when (probe-file dir)
    (if (null msg)
	(format t "~&;;; Deleting dir  ~A~%" dir)
      (format t "~&;;; ~A~%" msg))
    (specware::delete-directory dir)))

(defun make-dir-if-missing (dir)
  (unless (probe-file dir)
    (format t "~&;;; Making new    ~A~%" dir)
    (specware::make-directory dir)))

(defparameter *Specware-dir*  (format nil "~A/" (cdr (assoc :SPECWARE4 ext:*environment-list*))))
(defun in-specware-dir     (file) (concatenate 'string *Specware-dir* file))

(load (in-specware-dir "Applications/Handwritten/Lisp/load-utilities"))

;;; ============ PARAMETERS ============

;; Specware-name and Specware-Version might not be needed here.
;; They are in BuildPreamble.lisp where they are needed.

(defparameter Specware-name                  "Specware4")	; Name of dir and startup files
(defparameter cl-user::Specware-version      "4.2")
(defparameter cl-user::Specware-version-name "Specware-4-2")
(defparameter cl-user::Specware-patch-level  "0")
(defparameter Major-Version-String           "4-2")		; patch detection, about-specware cmd

(defparameter *Distribution-dir*  (concatenate 'string *specware-dir* "/distribution-cmulisp/"))

(defun in-distribution-dir (file) (concatenate 'string *Distribution-dir* file))

;;; =========== BUILD DISTRIBUTION DIRECTORY ============== 

(format t "~2&;;; Copying Tests, Documentation, Patches to distribution directory~%")

(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/CopyFilesForDistribution.lisp"))

;;; ============ SHOW RESULTS ============

(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/show-dirs.lisp"))

(format t "~&;;; Current status of distribution directory:~%;;;~%")
(show-dirs *distribution-dir* 3 ";;; ")

(format t "~&;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")
(format t "~&;;;~%")
(format t "~&;;; We now have ~A~%" (in-distribution-dir ""))
(format t "~&;;;~%")
(format t "~&;;; This completes Step Linux-D in How_To_Create_a_Specware_CD.txt]~%")
(format t "~&;;; Next you will copy the new distribution dir over to the Core-Win ~%")
(format t "~&;;; Windows machine and proceed over there~%")
(format t "~&;;;~%")
(format t "~&;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")

(format t "~&It is safe to exit now~%")

