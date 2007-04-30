;; This file builds a distribution directory for Linux/Mac OS X/SBCL Runtime Specware.

(defpackage :Specware)
(in-package :cl-user)

(defvar *including-isabelle-interface?* t)

(format t "~%;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")
(format t "~&About to build distribution dir for Specware under SBCL on Linux or Mac OS X.~%")
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

(load (format nil "~A/Applications/Handwritten/Lisp/load-utilities"
	      Specware::*specware-dir*))

;;; ============ PARAMETERS ============

;;; Get version information from canonical source...
(let ((version-file (format nil "~AApplications/Specware/Handwritten/Lisp/SpecwareVersion.lisp"
			    specware::*Specware-dir*)))
  (if (probe-file version-file)
      (load version-file)
    (error "in BuildDistribution_SBCL.lisp:  Cannot find ~A" version-file)))

(defparameter *Distribution-dir*  (concatenate 'string Specware::*specware-dir* "distribution-sbcl/Specware/"))

(ensure-directories-exist *Distribution-dir*)

(defun in-distribution-dir (file) (concatenate 'string *Distribution-dir* file))
(defun in-specware-dir (file) (concatenate 'string Specware::*specware-dir* file))


;;; =========== BUILD DISTRIBUTION DIRECTORY ============== 

(format t "~2&;;; Copying Tests, Documentation, Patches to distribution directory~%")

(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/CopyFilesForDistribution.lisp"))

(when *including-isabelle-interface?*
  (load (in-specware-dir "Applications/Specware/Handwritten/Lisp/CopyIsaFilesForDistribution.lisp")))

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

