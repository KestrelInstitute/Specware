;; This file builds a distribution directory for Windows/Allegro Runtime Specware.
;; Perhaps it should be under Specware4/Release/ instead -- it refers to several
;; files on that directory.

(defpackage :Specware)

(defvar *including-isabelle-interface?* t)

(format t "~%;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")
(format t "~&About to build distribution dir for Specware under Allegro on Windows.~%")
(format t "~&[This implements Step Windows-D in How_to_Create_a_Specware_CD.txt]~%")
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
    (Specware::delete-directory dir)))

(defun make-dir-if-missing (dir)
  (unless (probe-file dir)
    (format t "~&;;; Making new    ~A~%" dir)
    (Specware::make-directory dir)))

(require "BUILD")  ; workaround for annoying bug
(require "genapp") ; workaround for annoying bug

;;; ============ PARAMETERS ============

(defparameter *Specware-dir*      (fix-dir (sys:getenv "SPECWARE4")))

;;; Get version information from canonical source...
(let ((version-file (format nil "~AApplications/Specware/Handwritten/Lisp/SpecwareVersion.lisp"
			    *Specware-dir*)))
  (if (probe-file version-file)
      (load version-file)
    (error "in BuildDistribution_ACL.lisp:  Cannot find ~A" version-file)))

(defparameter *Allegro-dir*       (fix-dir (sys:getenv "ALLEGRO")))

(defparameter *Release-dir*       (format nil "C:/SpecwareReleases/~A-~A/"
					  *Specware-Version-Name*
					  *Specware-Patch-Level*))
(defparameter *CD-dir*            (concatenate 'string *release-dir* "CD/"))
(defparameter *Windows-dir*       (concatenate 'string *release-dir* "Windows/"))
(defparameter *Distribution-dir*  (concatenate 'string *windows-dir* "Specware4/"))

(defun in-specware-dir     (file) (concatenate 'string *Specware-dir*     file))
(defun in-lisp-dir         (file) (concatenate 'string *Allegro-dir*      file))
(defun in-release-dir      (file) (concatenate 'string *Release-dir*      file))
(defun in-distribution-dir (file) (concatenate 'string *Distribution-dir* file))
(defun in-cd-dir           (file) (concatenate 'string *CD-dir*           file))

;;; =========== DELETE OLD DIRECTORIES, CREATE NEW  ============== 

(format t "~%")
(format t "~&;;; Preparing distribution directory prior to generate-application ...~%")

(make-dir-if-missing *Release-dir*)
(make-dir-if-missing (in-release-dir "Windows"))
(make-dir-if-missing (in-release-dir "Linux"))
(make-dir-if-missing (in-release-dir "Linux/Specware4"))
(make-dir-if-missing (in-release-dir "Mac"))
(make-dir-if-missing (in-release-dir "Mac/Specware4"))

(make-dir-if-missing *CD-dir*)
(make-dir-if-missing (in-cd-dir "Windows"))
(make-dir-if-missing (in-cd-dir "Linux"))
(make-dir-if-missing (in-cd-dir "Mac"))

;; If the application directory already exists, then we delete it.
;; Note that generate-application will complain and die if the directory exists.
;; [or perhaps not, if  :allow-existing-directory t]

(delete-dir-if-present *Distribution-dir* ; "Windows/Specware4"
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
 *Specware-Name*

 ;; this is the directory where the application is to go
 ;; (plus accompanying files) 
 *distribution-dir*

 ;; a list of files to load 
 ;; [current directory is Specware4/Applications/Specware/Handwritten/Lisp/]
 '("BuildPreamble.lisp" "Specware4.lisp")

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

(format t "~2&;;; Copying Tests, Documentation, Patches to distribution directory~%")

(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/CopyFilesForDistribution.lisp"))

(when *including-isabelle-interface?*
  (load (in-specware-dir "Applications/Specware/Handwritten/Lisp/CopyIsaFilesForDistribution.lisp")))

;;; ============ EMACS SUPPORT ============

(format t "~&;;;~%")
(if (probe-file (in-distribution-dir "Library/IO/Emacs/xeli/"))
    (format t "~&;;; Getting Allegro/emacs interface already in specware libarary. ...~%")
  (progn
    (format t "~&;;; Getting Allegro/emacs interface from ~A ...~%" (in-lisp-dir "xeli/"))
    (Specware::copy-directory (in-lisp-dir "xeli/") 
			      (in-distribution-dir "Library/IO/Emacs/xeli/"))))

;;; ============ AUTORUN FILES FOR CD ============

(format t "~&;;;~%")
(format t "~&;;;     ===~%")
(format t "~&;;;~%")

;; Set up the directory that will hold the CD contents:
;;   C:/SpecwareReleases/Specware-i-j-k/CD/
;;
;; Put in the Autorun.inf file that will automatically invoke
;; Windows\setupwin32.exe for the user when the CD is inserted.
;;
;; Later the results from InstallShield will be put under
;;   C:/SpecwareReleases/Specware-i-j-k/CD/Windows/Specware4/
;;   C:/SpecwareReleases/Specware-i-j-k/CD/Linux/Specware4/
;;   C:/SpecwareReleases/Specware-i-j-k/CD/Mac/Specware4/
;;   ...


(delete-dir-if-present *cd-dir*)
(sleep 1) ; avoid stupid race condition in Windows

(make-dir-if-missing *cd-dir*)

(format t "~&;;; Adding Autorun for Windows: ~A~%" (in-cd-dir "Autorun.inf"))
(Specware::copy-file (in-specware-dir "Release/Autorun.inf")
		     (in-cd-dir "Autorun.inf"))

(format t "~&;;; Adding install script for Windows: ~A~%" (in-cd-dir "InstallOnWindows.cmd"))
(Specware::copy-file (in-specware-dir "Release/InstallOnWindows.cmd")
		     (in-cd-dir "InstallOnWindows.cmd"))

(format t "~&;;; Adding install script for Linux: ~A~%" (in-cd-dir "InstallOnLinux"))
(Specware::copy-file (in-specware-dir "Release/InstallOnLinux")
		     (in-cd-dir "InstallOnLinux"))

(format t "~&;;; Adding install script for Mac: ~A~%" (in-cd-dir "InstallOnMac"))
(Specware::copy-file (in-specware-dir "Release/InstallOnMac")
		     (in-cd-dir "InstallOnMac"))

;;; ============ EMPTY DIRS TO RECEIVE INSTALLSHIELD RESULTS ============

(make-dir-if-missing (concatenate 'string *CD-dir* "Windows"))
(make-dir-if-missing (concatenate 'string *CD-dir* "Windows/Specware4"))
(make-dir-if-missing (concatenate 'string *CD-dir* "Linux"))
(make-dir-if-missing (concatenate 'string *CD-dir* "Linux/Specware4"))
(make-dir-if-missing (concatenate 'string *CD-dir* "Mac"))
(make-dir-if-missing (concatenate 'string *CD-dir* "Mac/Specware4"))

(format t "~&;;;~%")

;;; ============ SHOW RESULTS ============

(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/show-dirs.lisp"))

(format t "~&;;; Current status of release directory:~%;;;~%")
(show-dirs *release-dir* 3 ";;; ")

(format t "~&;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")
(format t "~&;;;~%")
(format t "~&;;; We now have ~A~%" (in-distribution-dir ""))
(format t "~&;;;~%")
(format t "~&;;; This completes Step Windows-D in How_To_Create_a_Specware_CD.txt]~%")
(format t "~&;;; Next you will run InstallShield to build dirs to be placed on CD.~%")
(format t "~&;;;~%")
(format t "~&;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%")

(format t "~&It is safe to exit now~%")

