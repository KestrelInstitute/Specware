;; This file builds a distribution directory for Windows/Allegro Runtime Specware.

(defpackage :Specware)

(format t "~%;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")
(format t "~&About to build distribution dir for Specware under Allegro on Windows.~%")
(format t "~&[See STEP D in How_to_Create_a_Specware_CD.txt]~%")
(format t "~&;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")

#+Allegro (require "BUILD")  ; workaround for annoying bug
#+Allegro (require "genapp") ; workaround for annoying bug

;; These two definitions might not be needed here
;; They are in BuildPreamble.lisp where they are needed
(defparameter Specware-name "Specware4")	; Name of directory and startup files
(defparameter cl-user::Specware-version      "4.1")
(defparameter cl-user::Specware-version-name "Specware-4-1")
(defparameter cl-user::Specware-patch-level  "4")

(defun fix-dir (dir)
  (let ((dir (substitute #\/ #\\ dir)))
    (if (eq (schar dir (1- (length dir))) #\/)
	dir
      (concatenate 'string dir "/"))))
    
(defparameter Specware-dir (fix-dir (sys:getenv "SPECWARE4")))
(defparameter Allegro-dir  (fix-dir (sys:getenv "ALLEGRO")))

(defun in-specware-dir (file) (concatenate 'string Specware-dir file))
(defun in-lisp-dir     (file) (concatenate 'string Allegro-dir  file))

;; Used in patch detection and about-specware command
(defvar Major-Version-String "4-1")

(defparameter distribution-directory "")

(let* ((d1 (format nil "C:/SpecwareReleases/~A-~A/"
		   specware-version-name	 
		   specware-patch-level))
       (d2 (concatenate 'string d1 "Specware/"))
       (d3 (concatenate 'string d2 "Windows/"))
       (d4 (concatenate 'string d3 "Specware4/")))
  (format t "~%")
  (unless (probe-file d1) 
    (format t "~&;;; Making new ~A~%" d1)
    (specware::make-directory d1))
  (unless (probe-file d2)
    (format t "~&;;; Making new ~A~%" d2)
    (specware::make-directory d2))
  (unless (probe-file d3)
    (format t "~&;;; Making new ~A~%" d3)
    (specware::make-directory d3))
  (when (probe-file d4)
    (format t "~&;;; Deleting old version of ~A~%" d4)
    (excl::delete-directory-and-files d4))
  (setq distribution-directory d4))

(defun in-distribution-dir (file) (concatenate 'string distribution-directory file))

(format t "~%")

;; If the application directory already exists, then we delete it.
;; Note that generate-application will complain and die if the directory exists.
;; [or perhaps not, if  :allow-existing-directory t]

(when (probe-file distribution-directory)
  (format t "~&;;; Deleting old directory: ~A~%" distribution-directory)
  (excl::delete-directory-and-files distribution-directory))

(format t "~&;;; Calling excl:generate-application~%")

;;; For Windows, we use the Allegro Enterprise gen-app facility

;;; For generate-application, the environment var 
;;;  SPECWARE4 can be C:/Specware4, **** but not C:\Specware4 ****
;;;  ALLEGRO   can be C:\Progra~1\acl62 or C:/Progra~1/acl62 

(excl:generate-application
 ;; this is the name of the application
 Specware-name

 ;; this is the directory where the application is to go
 ;; (plus accompanying files) 
 distribution-directory

 ;; a list of files to load 
 ;; [current directory is Specware4/Applications/Specware/Handwritten/Lisp/]
 '("BuildPreamble.lisp" "Specware4.lisp" "license.lisp")

 ;; a list of files to copy to the distribution directory
 :application-files
 (list (in-specware-dir "Release/Windows/Specware4.cmd")
       (in-specware-dir "Release/Windows/Specware4 Shell.cmd")
       (in-specware-dir "Applications/Specware/Handwritten/Lisp/StartShell.lisp")
       (in-specware-dir "Applications/Specware/bin/windows/check-and-set-environment.cmd"))
 
 ;; Possible option instead of excl::delete-directory-and-files call
 :allow-existing-directory t

 ;; the image does not have a compiler neither during the build nor after.
 ;; The application has the interpreter only.
 :include-compiler t

 ;; which runtime? the other option is :dynamic which includes the compiler
 :runtime :dynamic
 )

;;; Specware4 directory

(format t "~2&;;; Copying Tests, Documentation, Patches, accord.el to distribution directory~%")

(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/copy-files-for-distribution.lisp"))

;;; Emacs support

(format t "~&;;; Copying emacs xeli dir to distribution directory~%")

(let ((dir (in-distribution-dir "Library")))
  (unless (probe-file dir)
    (format t "~&;;; Making new ~A~%" dir)
    (specware::make-directory dir)))

(let ((dir (in-distribution-dir "Library/IO")))
  (unless (probe-file dir)
    (format t "~&;;; Making new ~A~%" dir)
    (specware::make-directory dir)))

(let ((dir (in-distribution-dir "Library/IO/Emacs")))
  (unless (probe-file dir)
    (format t "~&;;; Making new ~A~%" dir)
    (specware::make-directory dir)))

(let ((dir (in-distribution-dir "Library/IO/Emacs/xeli/")))
  (when (probe-file dir)
    (format t "~&;;; Deleting old ~A~%" dir)
    (excl::delete-directory-and-files dir)))

(specware::copy-directory (in-lisp-dir "xeli/") (in-distribution-dir "Library/IO/Emacs/xeli/"))

(format t "~%;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")
(format t "~&Now have ~A~%" (in-distribution-dir ""))
(format t "~&;;; [This completes STEP D in How_To_Create_Accord_CD.txt]~%")
(format t "~&;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")

(format t "~&It is safe to exit now~%")

