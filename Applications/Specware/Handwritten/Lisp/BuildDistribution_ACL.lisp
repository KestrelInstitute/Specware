;; This file builds a distribution directory for Windows/Allegro Runtime Specware.
;; Perhaps it should be under Specware4/Release/ instead -- it refers to several
;; files on that directory.

(defpackage :Specware)

(format t "~%;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")
(format t "~&About to build distribution dir for Specware under Allegro on Windows.~%")
(format t "~&[This implements STEP D in How_to_Create_a_Specware_CD.txt]~%")
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

#+Allegro (require "BUILD")  ; workaround for annoying bug
#+Allegro (require "genapp") ; workaround for annoying bug

;;; ============ PARAMETERS ============

;; Specware-name and Specware-Version might not be needed here.
;; They are in BuildPreamble.lisp where they are needed.

(defparameter Specware-name                  "Specware4")	; Name of directory and startup files
(defparameter cl-user::Specware-version      "4.1")
(defparameter cl-user::Specware-version-name "Specware-4-1")
(defparameter cl-user::Specware-patch-level  "4")
(defparameter Major-Version-String           "4-1")		; for patch detection, about-specware command

(defparameter *Specware-dir*      (fix-dir (sys:getenv "SPECWARE4")))
(defparameter *Allegro-dir*       (fix-dir (sys:getenv "ALLEGRO")))

(defparameter *Release-dir*       (format nil "C:/SpecwareReleases/~A-~A/"
					  specware-version-name	 
					  specware-patch-level))
(defparameter *Windows-dir*       (concatenate 'string *release-dir* "Windows/"))
(defparameter *Distribution-dir*  (concatenate 'string *windows-dir* "Specware4/"))
(defparameter *CD-dir*            (concatenate 'string *release-dir* "CD/"))

(defun in-specware-dir     (file) (concatenate 'string *Specware-dir*     file))
(defun in-lisp-dir         (file) (concatenate 'string *Allegro-dir*      file))
(defun in-release-dir      (file) (concatenate 'string *Release-dir*      file))
(defun in-distribution-dir (file) (concatenate 'string *Distribution-dir* file))
(defun in-cd-dir           (file) (concatenate 'string *CD-dir*           file))

;;; =========== DELETE OLD DIRECTORIES, CREATE NEW  ============== 

(format t "~%")
(format t "~&;;; Preparing distribution directory prior to generate-application ...~%")

(make-dir-if-missing *Release-dir*)
(make-dir-if-missing *Windows-dir*)

;; If the application directory already exists, then we delete it.
;; Note that generate-application will complain and die if the directory exists.
;; [or perhaps not, if  :allow-existing-directory t]

(delete-dir-if-present *Distribution-dir*
		       (format nil
			       "Deleting old distribution dir: ~A"
			       *Distribution-dir*))

(format t "~%")

;;; =========== GENERATE STANDALONE LISP APPLICATION ============== 

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
 *distribution-dir*

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

;;; =========== BUILD DISTRIBUTION DIRECTORY ============== 

(format t "~2&;;; Copying Tests, Documentation, Patches, accord.el to distribution directory~%")

(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/CopyFilesForDistribution.lisp"))
(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/show-dirs.lisp"))

(format t "~&;;; Current status of release directory:~%;;;~%")
(show-dirs *release-dir* 3 ";;; ")

(format t "~&;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")
(format t "~&;;;~%")
(format t "~&;;; We now have ~A~%" (in-distribution-dir ""))
(format t "~&;;;~%")
(format t "~&;;; This completes Step Windows-D in How_To_Create_Accord_CD.txt]~%")
(format t "~&;;; Next you will run InstallShield to build dirs to be placed on CD.~%")
(format t "~&;;;~%")
(format t "~&;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")

;;; =========== DONE ============== 

(format t "~&It is safe to exit now~%")

