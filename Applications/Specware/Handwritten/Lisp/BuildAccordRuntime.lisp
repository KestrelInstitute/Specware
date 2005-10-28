;; This file builds a distribution directory for Window/Allegro Runtime Accord (including Specware).

(defpackage :Specware)

;; These two definitions might not be needed here
;; They are in BuildPreamble.lisp where they are needed
(defvar Accord-version "4.1.3")
(defvar Accord-version-name "Accord-4-1-3")
(defvar Accord-name "Specware-Accord")	; Name of directory and startup files
(defvar Accord-dir (sys:getenv "ACCORD"))
(defvar Specware-dir (sys:getenv "SPECWARE4"))
(defun in-accord-dir (file) (concatenate 'string Accord-dir "/" file))
(defun in-specware-dir (file) (concatenate 'string Specware-dir "/" file))
(defun in-lisp-dir (file) (concatenate 'string (sys:getenv "ALLEGRO") "/" file))

;; This is the sub-directory to receive this particular distribution.
;; In particular, this is where generate-application puts all its stuff.
(defparameter distribution-directory 
  (in-accord-dir  (concatenate 'string "distribution/" Accord-name "/")))
(defun in-distribution-dir (file) (concatenate 'string distribution-directory file))

;; If the application directory already exists, then we delete it.
;; generate-application complains and dies if the directory exists.
(when (probe-file distribution-directory)
  (excl::delete-directory-and-files distribution-directory))

(excl:generate-application
  ;; this is the name of the application
  Accord-name

  ;; this is the directory where the application is to go
  ;; (plus accompanying files) 
  distribution-directory

  ;; a list of files to load
  (mapcar #'(lambda (file) (format nil "~A/Applications/Specware/Handwritten/Lisp/~A.lisp" 
				   Specware-dir
				   file))
	  '("BuildAccordPreamble" "Specware4" "load-accord" "accord-license"))

  ;; a list of files to copy to the distribution directory
  :application-files
  (list ;;; (in-accord-dir "/Library/")
	;;; (in-accord-dir "/Applications/Accord/Courses/")
   (in-specware-dir "Applications/Specware/Handwritten/Lisp/StartShell.lisp"))

  ;; Possible option instead of excl::delete-directory-and-files call
  ;;  :allow-existing-directory t

  ;; the image does not have a compiler neither during the build nor after.
  ;; The application has the interpreter only.
  :include-compiler nil

  ;; which runtime? the other option is :dynamic which includes the compiler
  :runtime :standard
  )

;;; Command files
(specware::copy-file (in-specware-dir "Release/Windows/Specware-Accord.cmd")
		     (in-distribution-dir "Specware XEmacs.cmd"))
(specware::copy-file (in-specware-dir "Release/Windows/Specware-Accord-Shell.cmd")
		     (in-distribution-dir "Specware.cmd"))

(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/copy-files-for-distribution.lisp"))

;;; Copy needed directories to distribution
(specware::copy-directory (in-specware-dir "Library/Accord/")
			  (in-distribution-dir "Library/Accord/"))

(specware::copy-directory (in-lisp-dir "xeli/") (in-distribution-dir "Library/IO/Emacs/xeli/"))


(specware::make-directory (in-distribution-dir "Examples/Accord/"))

(specware::copy-directory (in-specware-dir "../Accord/Tests/Library/")
			  (in-distribution-dir "Examples/Accord/Library/"))
(delete-file-if-present (in-distribution-dir "Examples/Accord/Library/.cvsignore"))

(specware::copy-directory (in-specware-dir "../Accord/Tests/Cipher/")
			  (in-distribution-dir "Examples/Accord/Cipher/"))
(delete-file-if-present (in-distribution-dir "Examples/Accord/Cipher/.cvsignore"))

(specware::copy-directory (in-specware-dir "../Accord/Tests/F91/")
			  (in-distribution-dir "Examples/Accord/F91/"))
(delete-file-if-present (in-distribution-dir "Examples/Accord/F91/.cvsignore"))

(specware::copy-directory (in-specware-dir "../Accord/Tests/GCD/")
			  (in-distribution-dir "Examples/Accord/GCD/"))
(delete-file-if-present (in-distribution-dir "Examples/Accord/GCD/.cvsignore"))

(specware::copy-directory (in-specware-dir "../Accord/Tests/Queens/")
			  (in-distribution-dir "Examples/Accord/Queens/"))
(delete-file-if-present (in-distribution-dir "Examples/Accord/Queens/.cvsignore"))

